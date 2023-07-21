use std::sync::Arc;
use std::time::Instant;

use lurk::circuit::gadgets::circom::create_circom_config;
use lurk::circuit::gadgets::data::GlobalAllocations;
use lurk::circuit::gadgets::pointer::{AllocatedContPtr, AllocatedPtr};
use lurk::coprocessor::{CoCircuit, Coprocessor};
use lurk::eval::{empty_sym_env, lang::Lang};
use lurk::field::LurkField;
use lurk::proof::{nova::NovaProver, Prover};
use lurk::ptr::Ptr;
use lurk::public_parameters::public_params;
use lurk::store::Store;
use lurk::{Num, Symbol};
use lurk_macros::Coproc;

use bellperson::{ConstraintSystem, SynthesisError};

use nova_scotia::r1cs::CircomConfig;
use pasta_curves::pallas::Scalar as Fr;

const REDUCTION_COUNT: usize = 1;

#[derive(Debug)]
pub(crate) struct CircomSha256Coprocessor<F: LurkField> {
    n: usize,
    name: String,
    circom_config: CircomConfig<F>,
}

impl<F: LurkField> Clone for CircomSha256Coprocessor<F> {
    fn clone(&self) -> Self {
        CircomSha256Coprocessor::new(self.n, self.name.clone())
    }
}

impl<F: LurkField> CoCircuit<F> for CircomSha256Coprocessor<F> {
    fn arity(&self) -> usize {
        0
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocations<F>,
        _store: &Store<F>,
        _input_exprs: &[AllocatedPtr<F>],
        input_env: &AllocatedPtr<F>,
        input_cont: &AllocatedContPtr<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        
        let arg_in = ("arg_in".into(), vec![F::ZERO, F::ZERO]);
        let inputs = vec![arg_in];
        let witness = nova_scotia::calculate_witness(&self.circom_config, inputs, true).expect("msg");
        let output = nova_scotia::synthesize(cs, self.circom_config.r1cs.clone(), Some(witness))?;

        let res = AllocatedPtr::from_parts(g.num_tag.clone(), output);

        Ok((res, input_env.clone(), input_cont.clone()))
    }
}

impl<F: LurkField> Coprocessor<F> for CircomSha256Coprocessor<F> {
    fn eval_arity(&self) -> usize {
        0
    }

    fn simple_evaluate(&self, s: &mut Store<F>, _args: &[Ptr<F>]) -> Ptr<F> {
        let expected = Num::Scalar(
            F::from_str_vartime(
                "55165702627807990590530466439275329993482327026534454077267643456",
            )
            .unwrap(),
        );
        s.intern_num(expected)
    }

    fn has_circuit(&self) -> bool {
        true
    }
}

impl<F: LurkField> CircomSha256Coprocessor<F> {
    pub(crate) fn new(n: usize, name: String) -> Self {
        let circom_config = create_circom_config(&name).expect("circom config failed");
        Self {
            n,
            name,
            circom_config,
        }
    }
}

#[derive(Clone, Debug, Coproc)]
enum Sha256Coproc<F: LurkField> {
    SC(CircomSha256Coprocessor<F>),
}

/// Run the example in this file with
/// `cargo run --release --example circom_sha256`
fn main() {
    let store = &mut Store::<Fr>::new();
    let sym_str = Symbol::new(&[".circom_sha256_2"]); // two inputs
    let lang = Lang::<Fr, Sha256Coproc<Fr>>::new_with_bindings(
        store,
        vec![(
            sym_str.clone(),
            CircomSha256Coprocessor::new(64, "circom_sha256".into()).into(),
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
