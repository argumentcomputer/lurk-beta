use anyhow::{anyhow, bail, Context, Result};
use pasta_curves::pallas;

use fcomm::{
    public_params, Claim, Commitment, CommittedExpression, CommittedExpressionMap, Evaluation, Id,
    LurkPtr, NovaProofCache, Opening, Proof,
};
use lurk::eval::{Evaluable, Status, IO};
use lurk::field::{LanguageField, LurkField};
use lurk::package::Package;
use lurk::proof::{nova, nova::NovaProver, Prover};
use lurk::repl::{repl, ReplState, ReplTrait};
use lurk::store::{Expression, Pointer, Ptr, Store};
use lurk::tag::ExprTag;
use lurk::writer::Write;

use std::io;
use std::path::Path;

struct ClutchState<F: LurkField> {
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
                            "COMMIT" => {
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

                                let commitment =
                                    Commitment::from_ptr_and_secret(store, &evaled, secret);

                                let committed_expression = CommittedExpression {
                                    expr: LurkPtr::from_ptr(store, &evaled),
                                    secret: Some(secret),
                                    commitment: Some(commitment),
                                };

                                self.expression_map.set(commitment, &committed_expression)?;
                                Some(store.intern_maybe_opaque_comm(commitment.comm))
                            }
                            "OPEN" => {
                                let (maybe_comm, rest) = store.car_cdr(&rest)?;

                                let args = rest.as_cons();

                                let comm = match maybe_comm.tag() {
                                    ExprTag::Comm => Some(maybe_comm),
                                    ExprTag::Num => {
                                        // See Store::open_mut().
                                        let scalar = store
                                            .fetch_num(&maybe_comm)
                                            .map(|x| x.into_scalar())
                                            .unwrap();
                                        Some(store.intern_maybe_opaque_comm(scalar))
                                    }
                                    _ => {
                                        bail!("not a commitment");
                                    }
                                };

                                let expr_and_comm = comm.and_then(|comm| {
                                    let commitment = Commitment::from_comm(store, &comm);

                                    self.expression_map.get(&commitment).map(|c| {
                                        (c.expr.ptr(store, self.repl_state.limit), commitment)
                                    })
                                });

                                match (expr_and_comm, args) {
                                    (Some((e, commitment)), Some(a)) => {
                                        let call = store.cons(e, a);
                                        let (arg, _) = store.car_cdr(&a)?;

                                        let (result, _iterations, cont, _) = self
                                            .repl_state
                                            .eval_expr(call, store)
                                            .with_context(|| "Evaluating call")?;

                                        let claim = Claim::Opening::<F>(Opening {
                                            input: arg.fmt_to_string(store),
                                            output: result.fmt_to_string(store),
                                            status: Status::from(cont),
                                            commitment,
                                            new_commitment: None,
                                        });

                                        self.last_claim = Some(claim);

                                        Some(result)
                                    }
                                    (Some((expr, _)), _) => Some(expr),
                                    _ => None,
                                }
                            }
                            "PROOF-IN-EXPR" => {
                                let (proof_cid, _rest1) = store.car_cdr(&rest)?;
                                let cid_string =
                                    if let Expression::Str(p) = store.fetch(&proof_cid).unwrap() {
                                        p.to_string()
                                    } else {
                                        bail!("Proof path must be a string");
                                    };

                                let cid = fcomm::cid_from_string(&cid_string)?;
                                let proof = self
                                    .proof_map
                                    .get(&cid)
                                    .ok_or(anyhow!("proof not found: {cid}"))?;
                                let (input, _output) = proof.io(store)?;

                                let mut handle = io::stdout().lock();
                                input.expr.fmt(store, &mut handle)?;
                                println!();
                                None
                            }
                            "PROOF-OUT-EXPR" => {
                                let (proof_cid, _rest1) = store.car_cdr(&rest)?;
                                let cid_string =
                                    if let Expression::Str(p) = store.fetch(&proof_cid).unwrap() {
                                        p.to_string()
                                    } else {
                                        bail!("Proof path must be a string");
                                    };

                                let cid = fcomm::cid_from_string(&cid_string)?;
                                let proof = self
                                    .proof_map
                                    .get(&cid)
                                    .ok_or(anyhow!("proof not found: {cid}"))?;
                                let (_input, output) = proof.io(store)?;

                                let mut handle = io::stdout().lock();
                                output.expr.fmt(store, &mut handle)?;
                                println!();
                                None
                            }
                            "PROOF-CLAIM" => {
                                let (proof_cid, _rest1) = store.car_cdr(&rest)?;
                                let cid_string =
                                    if let Expression::Str(p) = store.fetch(&proof_cid).unwrap() {
                                        p.to_string()
                                    } else {
                                        bail!("Proof path must be a string");
                                    };

                                let cid = fcomm::cid_from_string(&cid_string)?;
                                let proof = self
                                    .proof_map
                                    .get(&cid)
                                    .ok_or(anyhow!("proof not found: {cid}"))?;

                                println!("{0:#?}", proof.claim);
                                None
                            }
                            "PROVE" => {
                                let (proof_in_expr, _rest1) = store.car_cdr(&rest)?;

                                let chunk_frame_count = 1;
                                let prover = NovaProver::<F>::new(chunk_frame_count);
                                let pp = public_params(chunk_frame_count);

                                let proof = if rest.is_nil() {
                                    if let Some(claim) = &self.last_claim {
                                        Proof::prove_claim(
                                            store,
                                            claim,
                                            self.repl_state.limit,
                                            false,
                                            &prover,
                                            &pp,
                                        )?
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
                                Some(cid)
                            }
                            "VERIFY" => {
                                let (proof_cid, _) = store.car_cdr(&rest)?;

                                let cid_string =
                                    if let Expression::Str(p) = store.fetch(&proof_cid).unwrap() {
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
                                    Some(store.get_t())
                                } else {
                                    Some(store.get_nil())
                                }
                            }
                            _ => return delegate!(),
                        }
                    } else {
                        return delegate!();
                    }
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

fn main() -> Result<()> {
    pretty_env_logger::init();

    // If an argument is passed, treat is as a Lurk file to run.
    let mut args = std::env::args();
    let lurk_file = if args.len() > 1 {
        Some(args.nth(1).expect("Lurk file missing"))
    } else {
        None
    };

    let default_field = LanguageField::Pallas;
    let field = if let Ok(lurk_field) = std::env::var("LURK_FIELD") {
        match lurk_field.as_str() {
            "BLS12-381" => LanguageField::BLS12_381,
            "PALLAS" => LanguageField::Pallas,
            "VESTA" => LanguageField::Vesta,
            _ => default_field,
        }
    } else {
        default_field
    };

    match field {
        LanguageField::Pallas => repl::<_, nova::S1, ClutchState<nova::S1>>(lurk_file.as_deref()),
        _ => panic!("unsupported field"),
    }
}
