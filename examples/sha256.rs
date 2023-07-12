use std::env;
use std::marker::PhantomData;
use std::sync::Arc;
use std::time::Instant;

use lurk::circuit::gadgets::constraints::alloc_equal;
use lurk::circuit::gadgets::data::{allocate_constant, GlobalAllocations};
use lurk::circuit::gadgets::pointer::{AllocatedContPtr, AllocatedPtr};
use lurk::coprocessor::{CoCircuit, Coprocessor};
use lurk::eval::{empty_sym_env, lang::Lang};
use lurk::field::LurkField;
use lurk::proof::{nova::NovaProver, Prover};
use lurk::ptr::Ptr;
use lurk::public_parameters::public_params;
use lurk::store::Store;
use lurk_macros::Coproc;

use bellperson::gadgets::boolean::{AllocatedBit, Boolean};
use bellperson::gadgets::multipack::pack_bits;
use bellperson::gadgets::num::AllocatedNum;
use bellperson::gadgets::sha256::sha256;
use bellperson::{ConstraintSystem, SynthesisError};

use pasta_curves::pallas::Scalar as Fr;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const REDUCTION_COUNT: usize = 10;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct Sha256Coprocessor<F: LurkField> {
    n: usize,
    expected: [u128; 2],
    pub(crate) _p: PhantomData<F>,
}

impl<F: LurkField> CoCircuit<F> for Sha256Coprocessor<F> {
    fn arity(&self) -> usize {
        0
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _g: &GlobalAllocations<F>,
        store: &Store<F>,
        _input_exprs: &[AllocatedPtr<F>],
        input_env: &AllocatedPtr<F>,
        input_cont: &AllocatedContPtr<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        let preimage = (0..self.n * 8)
            .map(|i| AllocatedBit::alloc(cs.namespace(|| format!("preimage bit {i}")), Some(false)))
            .map(|b| b.map(Boolean::from))
            .collect::<Result<Vec<_>, _>>()?;

        let mut bits = sha256(cs.namespace(|| "SHAhash"), &preimage)?;

        bits.reverse();

        let nums: Vec<AllocatedNum<_>> = (0..2)
            .map(|i| {
                pack_bits(
                    cs.namespace(|| format!("num{i}")),
                    &bits[(128 * i)..(128 * (i + 1))],
                )
                .unwrap()
            })
            .collect();

        let eqs: Vec<Boolean> = (0..2)
            .map(|i| {
                let num = allocate_constant(
                    &mut cs.namespace(|| format!("allocate result {i}")),
                    F::from_u128(self.expected[i]),
                )
                .unwrap();

                let eq = alloc_equal(
                    cs.namespace(|| format!("equate numbers {i}")),
                    &num,
                    &nums[i],
                )
                .unwrap();

                eq
            })
            .collect();

        let both_eq = Boolean::and(cs.namespace(|| "both equal"), &eqs[0], &eqs[1])?;

        let result_ptr = AllocatedPtr::as_lurk_boolean(cs, store, &both_eq)?;

        Ok((result_ptr, input_env.clone(), input_cont.clone()))
    }
}

impl<F: LurkField> Coprocessor<F> for Sha256Coprocessor<F> {
    fn eval_arity(&self) -> usize {
        0
    }

    fn simple_evaluate(&self, s: &mut Store<F>, _args: &[Ptr<F>]) -> Ptr<F> {
        let mut hasher = Sha256::new();

        let input = vec![0u8; self.n];

        hasher.update(input);
        let result = hasher.finalize();

        let mut u: Vec<u128> = (0..2)
            .map(|i| {
                let a: [u8; 16] = result[(16 * i)..(16 * (i + 1))].try_into().unwrap();
                u128::from_be_bytes(a)
            })
            .collect();

        u.reverse();

        let result = s.as_lurk_boolean(u == self.expected);

        result
    }

    fn has_circuit(&self) -> bool {
        true
    }
}

impl<F: LurkField> Sha256Coprocessor<F> {
    pub(crate) fn new(n: usize, expected: [u128; 2]) -> Self {
        Self {
            n,
            expected,
            _p: Default::default(),
        }
    }
}

#[derive(Clone, Debug, Coproc, Serialize, Deserialize)]
enum Sha256Coproc<F: LurkField> {
    SC(Sha256Coprocessor<F>),
}

/// Run the example in this file with
/// `cargo run --release --example sha256 1 f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b false`
fn main() {
    let args: Vec<String> = env::args().collect();

    let num_of_64_bytes = args[1].parse::<usize>().unwrap();
    let expect = hex::decode(args[2].parse::<String>().unwrap()).unwrap();
    let setup_only = args[3].parse::<bool>().unwrap();

    let input_size = 64 * num_of_64_bytes;

    let mut u: [u128; 2] = [0u128; 2];
    for i in 0..2 {
        u[i] = u128::from_be_bytes(expect[(i * 16)..(i + 1) * 16].try_into().unwrap())
    }

    u.reverse();

    let store = &mut Store::<Fr>::new();
    let sym = sym!("sha256", format!("{}-zero-bytes", input_size));

    let coproc_expr = format!("({})", &sym);

    let lang = Lang::<Fr, Sha256Coproc<Fr>>::new_with_bindings(
        store,
        vec![(
            sym_str.clone(),
            Sha256Coprocessor::new(input_size, u).into(),
        )],
    );

    let coproc_expr = format!("({})", sym_str);

    let expr = format!("({coproc_expr})");
    let ptr = store.read(&expr).unwrap();

    let nova_prover = NovaProver::<Fr, Sha256Coproc<Fr>>::new(REDUCTION_COUNT, lang.clone());
    let lang_rc = Arc::new(lang);

    println!("Setting up public parameters...");

    let pp_start = Instant::now();
    let pp = public_params::<Sha256Coproc<Fr>>(REDUCTION_COUNT, lang_rc.clone()).unwrap();
    let pp_end = pp_start.elapsed();

    println!("Public parameters took {:?}", pp_end);

    if setup_only {
        return;
    }

    println!("Beginning proof step...");

    let proof_start = Instant::now();
    let (proof, z0, zi, num_steps) = nova_prover
        .evaluate_and_prove(&pp, ptr, empty_sym_env(store), store, 10000, lang_rc)
        .unwrap();
    let proof_end = proof_start.elapsed();

    println!("Proofs took {:?}", proof_end);

    println!("Verifying proof...");

    let verify_start = Instant::now();
    let res = proof.verify(&pp, num_steps, z0, &zi).unwrap();
    let verify_end = verify_start.elapsed();

    println!("Verify took {:?}", verify_end);

    if res {
        println!(
            "Congratulations! You proved and verified a SHA256 hash calculation in {:?} time!",
            pp_end + proof_end + verify_end
        );
    }
}
