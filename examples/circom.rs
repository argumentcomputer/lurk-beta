use std::fmt::Debug;
use std::marker::PhantomData;
use std::sync::Arc;
use std::time::Instant;

use lurk::circuit::gadgets::circom::CircomGadget;
use lurk::circuit::gadgets::pointer::AllocatedPtr;
use lurk::coprocessor::circom::CircomCoprocessor;
use lurk::eval::{empty_sym_env, lang::Lang};
use lurk::field::LurkField;
use lurk::proof::{nova::NovaProver, Prover};
use lurk::ptr::Ptr;
use lurk::public_parameters::public_params;
use lurk::store::Store;
use lurk::{Num, Symbol};
use lurk_macros::Coproc;
use pasta_curves::pallas::Scalar as Fr;

const REDUCTION_COUNT: usize = 1;

#[derive(Debug, Clone)]
pub struct CircomSha256<F: LurkField> {
    _n: usize,
    pub(crate) _p: PhantomData<F>,
}

impl<F: LurkField> CircomSha256<F> {
    fn new(n: usize) -> Self {
        CircomSha256 {
            _n: n,
            _p: PhantomData,
        }
    }
}

impl<F: LurkField> CircomGadget<F> for CircomSha256<F> {
    fn name(&self) -> &str {
        "circom_sha256"
    }

    fn into_circom_input(&self, _input: &[AllocatedPtr<F>]) -> Vec<(String, Vec<F>)> {
        // TODO: actually use the lurk inputs
        let arg_in = ("arg_in".into(), vec![F::ZERO, F::ZERO]);
        vec![arg_in]
    }

    fn simple_evaluate(&self, s: &mut Store<F>, _args: &[Ptr<F>]) -> Ptr<F> {
        // TODO: actually use the lurk inputs
        let expected = Num::Scalar(
            F::from_str_vartime(
                "55165702627807990590530466439275329993482327026534454077267643456",
            )
            .unwrap(),
        );
        s.intern_num(expected)
    }
}

#[derive(Clone, Debug, Coproc)]
enum Sha256Coproc<F: LurkField> {
    SC(CircomCoprocessor<F, CircomSha256<F>>),
}

/// Run the example in this file with
/// `cargo run --release --example circom_sha256`
fn main() {
    let store = &mut Store::<Fr>::new();
    let sym_str = Symbol::new(&[".circom_sha256_2"]); // two inputs
    let circom_sha256 = CircomSha256::new(0);
    let lang = Lang::<Fr, Sha256Coproc<Fr>>::new_with_bindings(
        store,
        vec![(
            sym_str.clone(),
            CircomCoprocessor::new(circom_sha256).into(),
        )],
    );

    let coproc_expr = format!("{}", sym_str);
    dbg!(coproc_expr.clone());

    let expr = format!("({coproc_expr})");
    let ptr = store.read(&expr).unwrap();

    let nova_prover = NovaProver::<Fr, Sha256Coproc<Fr>>::new(REDUCTION_COUNT, lang.clone());
    let lang_rc = Arc::new(lang);

    println!("Setting up public parameters...");

    let pp_start = Instant::now();
    let pp = public_params::<Sha256Coproc<Fr>>(REDUCTION_COUNT, lang_rc.clone()).unwrap();
    let pp_end = pp_start.elapsed();

    println!("Public parameters took {:?}", pp_end);

    println!("Beginning proof step...");

    let proof_start = Instant::now();
    let (proof, z0, zi, num_steps) = nova_prover
        .evaluate_and_prove(&pp, ptr, empty_sym_env(store), store, 10000, lang_rc)
        .unwrap();
    let proof_end = proof_start.elapsed();

    println!("Proofs took {:?}", proof_end);

    println!("Verifying proof...");

    let verify_start = Instant::now();
    let res = proof.verify(&pp, num_steps, &z0, &zi).unwrap();
    let verify_end = verify_start.elapsed();

    println!("Verify took {:?}", verify_end);

    if res {
        println!(
            "Congratulations! You proved and verified a CIRCOM-SHA256 hash calculation in {:?} time!",
            pp_end + proof_end + verify_end
        );
    }
}
