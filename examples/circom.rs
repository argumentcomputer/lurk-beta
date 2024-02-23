//! # Circom Gadgets
//!
//! ## Setting up a Circom Gadget with Lurk
//!
//! First, in a separate directory from `lurk-rs`, clone the circomlib repo with the `Sha256_2` circuit.
//! ```
//! git clone git@github.com:iden3/circomlib.git && cd circomlib
//! ```
//!
//! Now return to the `lurk-rs` directory and run the following commands
//! ```
//! cargo run --release -- circom --reference iden3/sha256_2_test <PATH_TO_CIRCOMLIB>/test/circuits/
//! cargo run --release --example circom
//! ```
//!
//! This compiles the circom project and processes it for lurk to interface with.
//! The new `sha256_2_test` gadget is stored in `<CIRCOM_DIR>/iden3/sha256_2_test/*`.
//! To use the gadget, create a [CircomSha256] struct and implement the [CircomGadget] trait.
//! Refer to the example code below. Finally, declare the sha256 coprocessor:
//!
//! ```rust
//! #[derive(Clone, Debug, Coproc)]
//! enum Sha256Coproc<F: LurkField> {
//!    SC(CircomCoprocessor<F, CircomSha256<F>>),
//! }
//! ```
//!
//! Hooray! Now we can use a [CircomSha256] coprocessor just like a normal one.

use std::fmt::Debug;
use std::marker::PhantomData;
use std::sync::Arc;
use std::time::Instant;

use lurk::circuit::gadgets::circom::{CircomGadget, CircomGadgetReference};
use lurk::circuit::gadgets::pointer::AllocatedPtr;

#[cfg(not(target_arch = "wasm32"))]
use lurk::coprocessor::circom::non_wasm::CircomCoprocessor;

use lurk::eval::lang::Lang;
use lurk::field::LurkField;
use lurk::lem::{pointers::Ptr, store::Store};
use lurk::proof::RecursiveSNARKTrait;
use lurk::public_parameters::{
    instance::{Instance, Kind},
    supernova_public_params,
};

use lurk_macros::Coproc;
use pasta_curves::pallas::Scalar as Fr;

use anyhow::Result;
use circom_scotia::r1cs::CircomInput;
use ff::PrimeField;
use lurk::lem::eval::{
    evaluate, make_cprocs_funcs_from_lang, make_eval_step_from_config, EvalConfig,
};
use lurk::proof::supernova::SuperNovaProver;
use lurk::state::user_sym;
use sha2::{Digest, Sha256};

#[allow(dead_code)]
const REDUCTION_COUNT: usize = 1;

#[derive(Debug, Clone)]
pub struct CircomSha256<F: LurkField> {
    _n: usize,
    pub(crate) _p: PhantomData<F>,
    reference: CircomGadgetReference,
}

impl<F: LurkField> CircomSha256<F> {
    fn new(n: usize) -> Result<Self> {
        Ok(CircomSha256 {
            _n: n,
            _p: PhantomData,
            reference: CircomGadgetReference::new("iden3/sha256_2_test")?,
        })
    }
}

pub fn from_vec_u32<F: PrimeField>(arr: Vec<u32>) -> F {
    let mut res = F::ZERO;
    let radix = F::from(0x0001_0000_0000_u64);
    for &val in &arr {
        res = res * radix + F::from(u64::from(val));
    }
    res
}

/// Helper function to convert a vector of [`u32`] values to a [`PrimeField`] element. Assumes little endian representation.
/// Compatible with Circom version 2.
pub fn to_vec_u32<F: PrimeField>(f: F) -> Result<Vec<u32>> {
    let repr = F::to_repr(&f);
    let repr = repr.as_ref();

    let (pre, res, suf) = unsafe { repr.align_to::<u32>() };

    if !pre.is_empty() || !suf.is_empty() {
        panic!("nope")
    }

    Ok(res.into())
}

impl<F: LurkField> CircomGadget<F> for CircomSha256<F> {
    fn reference(&self) -> &CircomGadgetReference {
        &self.reference
    }

    fn into_circom_input(self, input: &[AllocatedPtr<F>]) -> Vec<CircomInput<F>> {
        dbg!("------------------------------INTO CIRCOM INPUT--------------------------------");
        dbg!(input
            .first()
            .unwrap()
            .hash()
            .get_value()
            .unwrap_or(F::ZERO)
            .to_bytes());
        dbg!(input
            .get(1)
            .unwrap()
            .hash()
            .get_value()
            .unwrap_or(F::ZERO)
            .to_bytes());
        let a = CircomInput::new(
            "a".into(),
            vec![input.first().unwrap().hash().get_value().unwrap_or(F::ZERO)],
        );
        let b = CircomInput::new(
            "b".into(),
            vec![input.get(1).unwrap().hash().get_value().unwrap_or(F::ZERO)],
        );
        vec![a, b]
    }

    fn evaluate_simple(&self, s: &Store<F>, args: &[Ptr]) -> Ptr {
        dbg!("------------------------------EVALUATE SIMPLE--------------------------------");

        let a_ptr = &args[0];
        let b_ptr = &args[1];
        let a_scalar = *s.hash_ptr(a_ptr).value();
        let b_scalar = *s.hash_ptr(b_ptr).value();

        dbg!(s.fetch_string(a_ptr));
        dbg!(s.fetch_string(b_ptr));

        // Create a Sha256 object
        let mut hasher = Sha256::new();

        // Write input message
        hasher.update([a_scalar.to_bytes(), b_scalar.to_bytes()].concat());

        // Read hash digest and consume hasher
        let result: Vec<u8> = hasher.finalize().to_vec();
        dbg!(F::from_bytes(&result));
        // TODO hash to get proper ptr
        // TODO: actually use the lurk inputs
        s.num(
            F::from_str_vartime(
                "55165702627807990590530466439275329993482327026534454077267643456",
            )
            .unwrap(),
        )
    }

    fn arity(&self) -> usize {
        2
    }
}

#[derive(Clone, Debug, Coproc)]
enum CircomCoproc<F: LurkField> {
    SC(CircomCoprocessor<F, CircomSha256<F>>),
}

/// Run the example in this file with
/// `cargo run --release -- circom --name sha256_2 examples/sha256/`
/// `cargo run --release --example circom`
fn main() {
    let store = &Store::default();
    let circom_sym = user_sym("circom_sha256_2");

    let expr = "(circom_sha256_2 \"a\" \"b\")".to_string();
    let ptr = store.read_with_default_state(&expr).unwrap();

    let circom_sha256: CircomSha256<Fr> = CircomSha256::new(0).unwrap();
    let mut lang = Lang::<Fr, CircomCoproc<Fr>>::new();

    lang.add_coprocessor(circom_sym, CircomCoprocessor::new(circom_sha256));
    let lang_rc = Arc::new(lang.clone());

    let lurk_step = make_eval_step_from_config(&EvalConfig::new_nivc(&lang));
    let cprocs = make_cprocs_funcs_from_lang(&lang);
    let frames = evaluate(Some((&lurk_step, &cprocs, &lang)), ptr, store, 1000).unwrap();

    // TODO is reduction count alright
    let supernova_prover = SuperNovaProver::<Fr, CircomCoproc<Fr>>::new(10, lang_rc.clone());

    let pp_start = Instant::now();

    println!("Setting up running claim parameters (rc = 10)...");

    let instance_primary = Instance::new(10, lang_rc, true, Kind::SuperNovaAuxParams);
    let pp = supernova_public_params(&instance_primary).unwrap();

    let pp_end = pp_start.elapsed();
    println!("Running claim parameters took {:?}", pp_end);

    println!("Beginning proof step...");
    let proof_start = Instant::now();
    let (proof, z0, zi, _num_steps) = tracing_texray::examine(tracing::info_span!("bang!"))
        .in_scope(|| {
            supernova_prover
                .prove_from_frames(&pp, &frames, store)
                .unwrap()
        });
    let proof_end = proof_start.elapsed();

    println!("Proofs took {:?}", proof_end);

    println!("Verifying proof...");

    let verify_start = Instant::now();
    assert!(proof.verify(&pp, &z0, &zi).unwrap());
    let verify_end = verify_start.elapsed();

    println!("Verify took {:?}", verify_end);

    println!("Compressing proof..");
    let compress_start = Instant::now();
    let compressed_proof = proof.compress(&pp).unwrap();
    let compress_end = compress_start.elapsed();

    println!("Compression took {:?}", compress_end);

    let buf = bincode::serialize(&compressed_proof).unwrap();
    println!("proof size : {:}B", buf.len());

    let compressed_verify_start = Instant::now();
    let res = compressed_proof.verify(&pp, &z0, &zi).unwrap();
    let compressed_verify_end = compressed_verify_start.elapsed();

    println!("Final verification took {:?}", compressed_verify_end);

    if res {
        println!(
            "Congratulations! You proved, verified, compressed, and verified (again!) an NIVC SHA256 hash calculation in {:?} time!",
            verify_end + proof_end + verify_end + compress_end
        );
    }
}
