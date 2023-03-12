use anyhow::{anyhow, bail, Context, Result};
use pasta_curves::pallas;

use fcomm::{
    public_params, Claim, Commitment, CommittedExpression, CommittedExpressionMap, Evaluation, Id,
    LurkPtr, NovaProofCache, Opening, Proof,
};
use lurk::eval::{Evaluable, Status, IO};
use lurk::field::LurkField;
use lurk::package::Package;
use lurk::proof::{nova::NovaProver, Prover};
use lurk::repl::{ReplState, ReplTrait};
use lurk::store::{Expression, Pointer, Ptr, ScalarPointer, Store};
use lurk::tag::ExprTag;
use lurk::writer::Write;

use std::io;
use std::path::Path;

pub struct ClutchState<F: LurkField> {
    repl_state: ReplState<F>,
    history: Vec<IO<F>>,
    proof_map: NovaProofCache,
    expression_map: CommittedExpressionMap,
    last_claim: Option<Claim<F>>,
}

type F = pallas::Scalar;

impl ReplTrait<F> for ClutchState<F> {
    fn new(s: &mut Store<F>, limit: usize) -> Self {
        let proof_map = fcomm::nova_proof_cache();
        let expression_map = fcomm::committed_expression_store();
        Self {
            repl_state: ReplState::new(s, limit),
            history: Default::default(),
            proof_map,
            expression_map,
            last_claim: None,
        }
    }

    fn name() -> String {
        "Lurk Clutch".into()
    }

    fn prompt(&self) -> String {
        "!> ".into()
    }

    fn handle_run<P: AsRef<Path> + Copy>(
        &mut self,
        store: &mut Store<F>,
        file_path: P,
        package: &Package,
    ) -> Result<()> {
        self.repl_state.handle_run(store, file_path, package)
    }

    /// Returns two bools.
    /// First bool is true if input is a command.
    /// Second bool is true if processing should continue.
    fn maybe_handle_command(
        &mut self,
        store: &mut Store<F>,
        line: &str,
        package: &Package,
    ) -> Result<(bool, bool)> {
        self.repl_state.maybe_handle_command(store, line, package)
    }

    fn handle_meta<P: AsRef<Path> + Copy>(
        &mut self,
        store: &mut Store<F>,
        expr_ptr: Ptr<F>,
        package: &Package,
        p: P,
    ) -> Result<()> {
        let expr = store.fetch(&expr_ptr).unwrap();

        macro_rules! delegate {
            () => {
                self.repl_state.handle_meta(store, expr_ptr, package, p)
            };
        }

        let res: Option<Ptr<F>> = match expr {
            Expression::Cons(car, rest) => match &store.fetch(&car).unwrap() {
                Expression::Sym(s) => {
                    if let Some(name) = s.simple_keyword_name() {
                        match name.as_str() {
                            "CALL" => self.call(store, rest)?,
                            "CHAIN" => self.chain(store, rest)?,
                            "COMMIT" => self.commit(store, rest)?,
                            "OPEN" => self.open(store, rest)?,
                            "PROOF-IN-EXPR" => self.proof_in_expr(store, rest)?,
                            "PROOF-OUT-EXPR" => self.proof_out_expr(store, rest)?,
                            "PROOF-CLAIM" => self.proof_claim(store, rest)?,
                            "PROVE" => self.prove(store, rest)?,
                            "VERIFY" => self.verify(store, rest)?,
                            _ => return delegate!(),
                        }
                    } else {
                        return delegate!();
                    }
                }
                Expression::Comm(_, c) => {
                    // NOTE: this cannot happen from a text-based REPL, since there is not currrently a literal Comm syntax.
                    self.apply_comm(store, *c, rest)?
                }
                Expression::Num(c) => {
                    let comm = store.intern_num(*c);
                    self.apply_comm(store, comm, rest)?
                }
                _ => return delegate!(),
            },
            Expression::Num(n) => {
                let i = n.into_scalar().to_u64_unchecked();
                self.hist(i as usize).map(|io| io.expr)
            }
            _ => return delegate!(),
        };

        if let Some(expr) = res {
            let mut handle = io::stdout().lock();
            expr.fmt(store, &mut handle)?;
            println!();
        };
        Ok(())
    }

    fn handle_non_meta(
        &mut self,
        store: &mut Store<F>,
        expr_ptr: Ptr<F>,
        update_env: bool,
    ) -> Result<(IO<F>, IO<F>, usize)> {
        match self.repl_state.handle_non_meta(store, expr_ptr, update_env) {
            Ok((input, output, iterations)) => {
                self.history.push(output);

                let claim = Claim::Evaluation::<F>(Evaluation {
                    expr: input.expr.fmt_to_string(store),
                    env: input.env.fmt_to_string(store),
                    cont: input.cont.fmt_to_string(store),
                    expr_out: output.expr.fmt_to_string(store),
                    env_out: output.env.fmt_to_string(store),
                    cont_out: output.cont.fmt_to_string(store),
                    status: output.status(),
                    iterations: None,
                });

                self.last_claim = Some(claim);

                Ok((input, output, iterations))
            }
            e => e,
        }
    }
}

impl<F: LurkField> ClutchState<F> {
    fn hist(&self, n: usize) -> Option<&IO<F>> {
        self.history.get(n)
    }
}

impl ClutchState<F> {
    fn commit(&mut self, store: &mut Store<F>, rest: Ptr<F>) -> Result<Option<Ptr<F>>> {
        let (first, rest) = store.car_cdr(&rest)?;
        let (second, _) = store.car_cdr(&rest)?;

        let (expr, secret) = if rest.is_nil() {
            // TODO: also support Commitment::from_ptr_with_hiding (randomized secret at runtime).
            (first, F::zero())
        } else if let Expression::Num(n) = store.fetch(&second).unwrap() {
            (first, n.into_scalar())
        } else {
            bail!("Secret must be a Num")
        };

        let (evaled, _, _, _) = self.repl_state.eval_expr(expr, store)?;

        let commitment = Commitment::from_ptr_and_secret(store, &evaled, secret);

        let committed_expression = CommittedExpression {
            expr: LurkPtr::from_ptr(store, &evaled),
            secret: Some(secret),
            commitment: Some(commitment),
        };

        self.expression_map.set(commitment, &committed_expression)?;
        Ok(Some(store.intern_maybe_opaque_comm(commitment.comm)))
    }

    fn open(&mut self, store: &mut Store<F>, rest: Ptr<F>) -> Result<Option<Ptr<F>>> {
        Ok(self.open_aux(store, rest)?.1)
    }

    fn apply_comm(
        &mut self,
        store: &mut Store<F>,
        comm: Ptr<F>,
        rest: Ptr<F>,
    ) -> Result<Option<Ptr<F>>> {
        let call_form = store.cons(comm, rest);
        self.apply_comm_aux(store, call_form, false)
    }
    fn call(&mut self, store: &mut Store<F>, rest: Ptr<F>) -> Result<Option<Ptr<F>>> {
        self.apply_comm_aux(store, rest, false)
    }
    fn chain(&mut self, store: &mut Store<F>, rest: Ptr<F>) -> Result<Option<Ptr<F>>> {
        let x = self.apply_comm_aux(store, rest, true)?;

        if let Some(cons) = x {
            let (result_expr, new_comm) = store.car_cdr(&cons)?;

            let new_secret0 = store.secret(new_comm).expect("secret missing");
            let new_secret = *store
                .get_expr_hash(&new_secret0)
                .expect("hash missing")
                .value();

            let (_, new_fun) = store.open(new_comm).expect("opening missing");
            let new_commitment = Commitment::from_comm(store, &new_comm);

            let expr = LurkPtr::from_ptr(store, &new_fun);

            let new_function = CommittedExpression::<F> {
                expr,
                secret: Some(new_secret),
                commitment: Some(new_commitment),
            };

            self.expression_map.set(new_commitment, &new_function)?;

            let interned_commitment = store.intern_maybe_opaque_comm(new_commitment.comm);
            let mut handle = io::stdout().lock();
            interned_commitment.fmt(store, &mut handle)?;
            println!();

            Ok(Some(result_expr))
        } else {
            bail!("chained functional commitment output must be a pair (result, new-commitment)");
        }
    }
    fn apply_comm_aux(
        &mut self,
        store: &mut Store<F>,
        rest: Ptr<F>,
        chain: bool,
    ) -> Result<Option<Ptr<F>>> {
        let args = store.cdr(&rest)?;
        if let (commitment, Some(e)) = self.open_aux(store, rest)? {
            let call = store.cons(e, args);
            let (arg, _) = store.car_cdr(&args)?;

            let (result, _iterations, cont, _) = self
                .repl_state
                .eval_expr(call, store)
                .with_context(|| "Evaluating call")?;

            let (output, new_commitment) = if chain {
                let (output, new_comm) = store.car_cdr(&result)?;
                (output, Some(Commitment::from_comm(store, &new_comm)))
            } else {
                (result, None)
            };

            let claim = Claim::Opening::<F>(Opening {
                input: arg.fmt_to_string(store),
                output: output.fmt_to_string(store),
                status: Status::from(cont),
                commitment,
                new_commitment,
            });

            self.last_claim = Some(claim);

            Ok(Some(result))
        } else {
            Ok(None)
        }
    }
    fn open_aux(
        &mut self,
        store: &mut Store<F>,
        rest: Ptr<F>,
    ) -> Result<(Commitment<F>, Option<Ptr<F>>)> {
        let maybe_comm = store.car(&rest)?;

        let comm = match maybe_comm.tag() {
            ExprTag::Comm => maybe_comm,
            ExprTag::Num => {
                // See Store::open_mut().
                let scalar = store
                    .fetch_num(&maybe_comm)
                    .map(|x| x.into_scalar())
                    .unwrap();

                store.intern_maybe_opaque_comm(scalar)
            }
            _ => {
                bail!("not a commitment");
            }
        };

        let commitment = Commitment::from_comm(store, &comm);

        if let Ok((_secret, value)) = store.open_mut(maybe_comm) {
            return Ok((commitment, Some(value)));
        };

        Ok((
            commitment,
            self.expression_map
                .get(&commitment)
                .map(|c| c.expr.ptr(store, self.repl_state.limit)),
        ))
    }

    fn proof_in_expr(&mut self, store: &mut Store<F>, rest: Ptr<F>) -> Result<Option<Ptr<F>>> {
        let proof = self.get_proof(store, rest)?;
        let (input, _output) = proof.io(store)?;

        let mut handle = io::stdout().lock();
        input.expr.fmt(store, &mut handle)?;
        println!();
        Ok(None)
    }
    fn proof_out_expr(&mut self, store: &mut Store<F>, rest: Ptr<F>) -> Result<Option<Ptr<F>>> {
        let proof = self.get_proof(store, rest)?;
        let (_input, output) = proof.io(store)?;

        let mut handle = io::stdout().lock();
        output.expr.fmt(store, &mut handle)?;
        println!();
        Ok(None)
    }
    fn proof_claim(&mut self, store: &mut Store<F>, rest: Ptr<F>) -> Result<Option<Ptr<F>>> {
        let proof = self.get_proof(store, rest)?;

        println!("{0:#?}", proof.claim);
        Ok(None)
    }

    fn get_proof(&mut self, store: &mut Store<F>, rest: Ptr<F>) -> Result<Proof<F>> {
        let (proof_cid, _rest1) = store.car_cdr(&rest)?;
        let cid_string = if let Expression::Str(p) = store.fetch(&proof_cid).unwrap() {
            p.to_string()
        } else {
            bail!("Proof path must be a string");
        };

        let cid = fcomm::cid_from_string(&cid_string)?;
        self.proof_map
            .get(&cid)
            .ok_or(anyhow!("proof not found: {cid}"))
    }

    fn prove(&mut self, store: &mut Store<F>, rest: Ptr<F>) -> Result<Option<Ptr<F>>> {
        let (proof_in_expr, _rest1) = store.car_cdr(&rest)?;

        let chunk_frame_count = 1;
        let prover = NovaProver::<F>::new(chunk_frame_count);
        let pp = public_params(chunk_frame_count);

        let proof = if rest.is_nil() {
            if let Some(claim) = &self.last_claim {
                Proof::prove_claim(store, claim, self.repl_state.limit, false, &prover, &pp)?
            } else {
                bail!("no last claim");
            }
        } else {
            Proof::<pallas::Scalar>::eval_and_prove(
                store,
                proof_in_expr,
                self.repl_state.limit,
                false,
                &prover,
                &pp,
            )?
        };

        proof.verify(&pp).expect("created proof doesn't verify");
        let cid_str = proof.claim.cid().to_string();
        println!("{0:#?}", proof.claim);

        let cid = store.str(cid_str);
        Ok(Some(cid))
    }
    fn verify(&mut self, store: &mut Store<F>, rest: Ptr<F>) -> Result<Option<Ptr<F>>> {
        let (proof_cid, _) = store.car_cdr(&rest)?;

        let cid_string = if let Expression::Str(p) = store.fetch(&proof_cid).unwrap() {
            p.to_string()
        } else {
            bail!("Proof path must be a string");
        };

        let cid = fcomm::cid_from_string(&cid_string)?;
        let proof = self
            .proof_map
            .get(&cid)
            .ok_or(anyhow!("proof not found: {cid}"))?;
        let chunk_frame_count = 1;
        let pp = public_params(chunk_frame_count);
        let result = proof.verify(&pp).unwrap();

        if result.verified {
            Ok(Some(store.get_t()))
        } else {
            Ok(Some(store.get_nil()))
        }
    }
}
