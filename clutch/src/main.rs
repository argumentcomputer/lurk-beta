use anyhow::Result;
use pasta_curves::pallas;

use fcomm::{Commitment, CommittedExpression, FileStore, LurkPtr, Proof};
use lurk::field::{LanguageField, LurkField};
use lurk::package::Package;
use lurk::proof::{
    nova,
    nova::{public_params, NovaProver},
    Prover,
};
use lurk::repl::{repl, ReplState, ReplTrait};
use lurk::store::{Expression, Pointer, Ptr, Store};
use lurk::tag::ExprTag;
use lurk::writer::Write;

use std::io;
use std::path::Path;

struct ClutchState<F: LurkField>(ReplState<F>);

type F = pallas::Scalar;

impl ReplTrait<F> for ClutchState<F> {
    fn new(s: &mut Store<F>, limit: usize) -> Self {
        Self(ReplState::new(s, limit))
    }

    fn name() -> String {
        "Lurk Clutch".into()
    }

    fn handle_run<P: AsRef<Path> + Copy>(
        &mut self,
        store: &mut Store<F>,
        file_path: P,
        package: &Package,
    ) -> Result<()> {
        self.0.handle_run(store, file_path, package)
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
        self.0.maybe_handle_command(store, line, package)
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
                self.0.handle_meta(store, expr_ptr, package, p)
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
                                    println!("Secret must be a Num");
                                    return Ok(());
                                };

                                let commitment =
                                    Commitment::from_ptr_and_secret(store, &expr, secret);

                                let committed_expression = CommittedExpression {
                                    expr: LurkPtr::from_ptr(store, &expr),
                                    secret: Some(secret),
                                    commitment: Some(commitment),
                                };

                                let expression_map = fcomm::committed_expression_store();
                                expression_map.set(commitment, &committed_expression)?;
                                Some(store.intern_maybe_opaque_comm(commitment.comm))
                            }
                            "OPEN" => {
                                let (maybe_comm, rest) = store.car_cdr(&rest)?;
                                let (_arg, _) = store.car_cdr(&rest)?;

                                assert!(rest.is_nil()); // TODO: if one or more args, apply to function.

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
                                        println!("not a commitment");
                                        None
                                    }
                                };

                                comm.map(|comm| {
                                    let commitment = Commitment::from_comm(store, &comm);
                                    let expression_map = fcomm::committed_expression_store();

                                    let committed_expression = expression_map
                                        .get(&commitment)
                                        .expect("committed expression not found");

                                    committed_expression.expr.ptr(store)
                                })
                            }
                            "PROVE" => {
                                let (proof_path, rest) = store.car_cdr(&rest)?;
                                let (proof_in_expr, _) = store.car_cdr(&rest)?;

                                let path =
                                    if let Expression::Str(p) = store.fetch(&proof_path).unwrap() {
                                        p.to_string()
                                    } else {
                                        println!("Proof path must be a string");
                                        return Ok(());
                                    };

                                let chunk_frame_count = 1;

                                let prover = NovaProver::<F>::new(chunk_frame_count);
                                let pp = public_params(chunk_frame_count);
                                let proof = Proof::<pallas::Scalar>::eval_and_prove(
                                    store,
                                    proof_in_expr,
                                    self.0.limit,
                                    false,
                                    &prover,
                                    &pp,
                                )
                                .expect("proving failed");

                                proof.write_to_path(path);
                                proof.verify(&pp).expect("created proof doesn't verify");

                                Some(proof_in_expr)
                            }
                            "VERIFY" => {
                                let (proof_path, _) = store.car_cdr(&rest)?;

                                let path =
                                    if let Expression::Str(p) = store.fetch(&proof_path).unwrap() {
                                        p.to_string()
                                    } else {
                                        println!("Proof path must be a string");
                                        return Ok(());
                                    };

                                let proof = Proof::read_from_path(path).unwrap();
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
    ) -> Result<()> {
        self.0.handle_non_meta(store, expr_ptr, update_env)
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
