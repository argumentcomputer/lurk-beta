//! # Circom Gadgets
//!
//! ## Fetching a remote Circom Gadget
//!
//! Declare a `CircomGadget` implementing a `reference` pointing to a valid Circom Gadget repository
//! and an existing release `version`. If the `CircomCoprocessor` can not find it locally it will directly
//! fetch the r1cs and wasm files from Github.
//!
//! Refer to the example code below. Finally, declare the sha256 coprocessor:
//!
//! ```rust
//! #[derive(Clone, Debug, Coproc)]
//! enum Sha256Coproc<F: LurkField> {
//!    SC(CircomCoprocessor<F, CircomSha256<F>>),
//! }
//! ```
//!
//! Hooray! Now we can use a [CircomKeccak] coprocessor just like a normal one.

use circom_scotia::r1cs::CircomInput;
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
use lurk::lem::eval::{
    evaluate, make_cprocs_funcs_from_lang, make_eval_step_from_config, EvalConfig,
};

use lurk::lem::{pointers::Ptr, store::Store};
use lurk::proof::supernova::SuperNovaProver;
use lurk::proof::RecursiveSNARKTrait;
use lurk::public_parameters::{
    instance::{Instance, Kind},
    supernova_public_params,
};
use lurk::state::user_sym;

use lurk_macros::Coproc;
use pasta_curves::pallas::Scalar as Fr;
use tiny_keccak::{Hasher, Keccak};

#[allow(dead_code)]
const REDUCTION_COUNT: usize = 1;

#[derive(Debug, Clone)]
pub struct CircomKeccak<F: LurkField> {
    _n: usize,
    pub(crate) _p: PhantomData<F>,
    reference: CircomGadgetReference,
}

impl<F: LurkField> CircomKeccak<F> {
    fn new(n: usize) -> Self {
        CircomKeccak {
            _n: n,
            _p: PhantomData,
            reference: CircomGadgetReference::new("lurk-lab/keccak-circom-gadget").unwrap(),
        }
    }
}

impl<F: LurkField> CircomGadget<F> for CircomKeccak<F> {
    fn reference(&self) -> &CircomGadgetReference {
        &self.reference
    }

    fn version(&self) -> Option<&str> {
        Some("v0.1.0")
    }

    fn into_circom_input(self, input: &[AllocatedPtr<F>]) -> Vec<CircomInput<F>> {
        dbg!(input.first().unwrap().hash().get_value());
        // TODO: actually use the lurk inputs
        let input_bytes = [
            116, 101, 115, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
        ];

        let input_bits = bytes_to_bits(&input_bytes);

        vec![CircomInput::new(
            "in".into(),
            input_bits.clone().iter().map(|_| F::ZERO).collect(),
        )]
        /*vec![(
            "in".into(),
            input_bits.clone().iter().map(|b| F::from(*b)).collect(),
        )]*/
    }

    fn evaluate_simple(&self, s: &Store<F>, args: &[Ptr]) -> Ptr {
        let string_ptr = &args[0];
        let string_scalar = *s.hash_ptr(string_ptr).value();
        dbg!(string_scalar);
        let string_scalar_bytes = string_scalar.to_bytes();

        let mut hasher = Keccak::v256();
        let mut output_bytes = [0u8; 32];
        hasher.update(&string_scalar_bytes);

        hasher.finalize(&mut output_bytes);

        s.num(F::from_bytes(&output_bytes).unwrap())
    }

    fn arity(&self) -> usize {
        1
    }
}

#[derive(Clone, Debug, Coproc)]
enum KeccakCoproc<F: LurkField> {
    SC(CircomCoprocessor<F, CircomKeccak<F>>),
}

fn main() {
    let store = &Store::default();
    let circom_sym = user_sym("circom_keccak");

    let expr = "(circom_keccak \"test\")".to_string();
    let ptr = store.read_with_default_state(&expr).unwrap();

    let circom_sha256: CircomKeccak<Fr> = CircomKeccak::new(0);
    let mut lang = Lang::<Fr, KeccakCoproc<Fr>>::new();

    lang.add_coprocessor(circom_sym, CircomCoprocessor::new(circom_sha256));
    let lang_rc = Arc::new(lang.clone());

    let lurk_step = make_eval_step_from_config(&EvalConfig::new_nivc(&lang));
    let cprocs = make_cprocs_funcs_from_lang(&lang);
    let frames = evaluate(Some((&lurk_step, &cprocs, &lang)), ptr, store, 1000).unwrap();

    // TODO is reduction count alright
    let supernova_prover = SuperNovaProver::<Fr, KeccakCoproc<Fr>>::new(10, lang_rc.clone());

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

// Transforms a slice of bytes to a slice of bits. When dividing one byte in bits, order the bits
// from the least significant to the most significant one.
fn bytes_to_bits(bytes: &[u8]) -> Vec<bool> {
    let mut bits = Vec::new(); // Create a new, empty vector to store bits

    for &byte in bytes.iter() {
        // Iterate over each byte in the input slice
        for j in 0..8 {
            // For each bit in the byte
            if byte & (1 << j) > 0 {
                // Check if the bit is set
                bits.push(true); // If the bit is set, push 1 to the vector
            } else {
                bits.push(false); // If the bit is not set, push 0
            }
        }
    }
    bits // Return the vector of bits
}
