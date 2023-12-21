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

use std::fmt::Debug;
use std::marker::PhantomData;
use std::sync::Arc;
use std::time::Instant;

use lurk::circuit::gadgets::circom::CircomGadget;
use lurk::circuit::gadgets::pointer::AllocatedPtr;
use lurk::lem::multiframe::MultiFrame;

#[cfg(not(target_arch = "wasm32"))]
use lurk::coprocessor::circom::non_wasm::CircomCoprocessor;

use lurk::eval::lang::Lang;
use lurk::field::LurkField;
use lurk::lem::{pointers::Ptr, store::Store};
use lurk::proof::{nova::NovaProver, Prover, RecursiveSNARKTrait};
use lurk::public_parameters::{
    instance::{Instance, Kind},
    public_params,
};
use lurk::Symbol;
use lurk_macros::Coproc;
use pasta_curves::pallas::Scalar as Fr;

const REDUCTION_COUNT: usize = 1;

#[derive(Debug, Clone)]
pub struct CircomKeccak<F: LurkField> {
    _n: usize,
    pub(crate) _p: PhantomData<F>,
}

impl<F: LurkField> CircomKeccak<F> {
    fn new(n: usize) -> Self {
        CircomKeccak {
            _n: n,
            _p: PhantomData,
        }
    }
}

impl<F: LurkField> CircomGadget<F> for CircomKeccak<F> {
    fn reference(&self) -> &str {
        "lurk-lab/keccak-circom-gadget"
    }

    fn version(&self) -> Option<&str> {
        Some("v0.1.0")
    }

    fn into_circom_input(self, _input: &[AllocatedPtr<F>]) -> Vec<(String, Vec<F>)> {
        // TODO: actually use the lurk inputs
        let input_bytes = [
            116, 101, 115, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
        ];

        let input_bits = bytes_to_bits(&input_bytes);

        vec![(
            "in".into(),
            input_bits.clone().iter().map(|_| F::ZERO).collect(),
        )]
        /*vec![(
            "in".into(),
            input_bits.clone().iter().map(|b| F::from(*b)).collect(),
        )]*/
    }

    fn evaluate_simple(&self, s: &Store<F>, _args: &[Ptr]) -> Ptr {
        // TODO: actually use the lurk inputs
        let _expected_output = [
            37, 17, 98, 135, 161, 178, 88, 97, 125, 150, 143, 65, 228, 211, 170, 133, 153, 9, 88,
            212, 4, 212, 175, 238, 249, 210, 214, 116, 170, 85, 45, 21,
        ];

        s.num(
            F::from_str_vartime(
                "55165702627807990590530466439275329993482327026534454077267643456",
            )
            .unwrap(),
        )
    }
}

#[derive(Clone, Debug, Coproc)]
enum KeccakCoproc<F: LurkField> {
    SC(CircomCoprocessor<F, CircomKeccak<F>>),
}

fn main() {
    let store = &Store::<Fr>::default();
    let sym_str = Symbol::new(&[".circom_keccak"], false); // two inputs
    let circom_keccak: CircomKeccak<Fr> = CircomKeccak::new(0);
    let mut lang = Lang::<Fr, KeccakCoproc<Fr>>::new();
    lang.add_coprocessor(sym_str, CircomCoprocessor::new(circom_keccak));
    let lang_rc = Arc::new(lang);

    let expr = "(.circom_keccak)".to_string();
    let ptr = store.read_with_default_state(&expr).unwrap();

    let nova_prover = NovaProver::<Fr, KeccakCoproc<Fr>, MultiFrame<'_, _, _>>::new(
        REDUCTION_COUNT,
        lang_rc.clone(),
    );

    println!("Setting up public parameters...");

    let pp_start = Instant::now();
    let instance = Instance::new(REDUCTION_COUNT, lang_rc, true, Kind::NovaPublicParams);
    let pp = public_params::<_, _, MultiFrame<'_, _, _>>(&instance).unwrap();
    let pp_end = pp_start.elapsed();

    println!("Public parameters took {pp_end:?}");

    println!("Beginning proof step...");

    let proof_start = Instant::now();
    let (proof, z0, zi, _num_steps) = nova_prover
        .evaluate_and_prove(&pp, ptr, store.intern_nil(), store, 10000)
        .unwrap();
    let proof_end = proof_start.elapsed();

    println!("Proofs took {proof_end:?}");

    println!("Verifying proof...");

    let verify_start = Instant::now();
    let res = proof.verify(&pp, &z0, &zi).unwrap();
    let verify_end = verify_start.elapsed();

    println!("Verify took {verify_end:?}");

    if res {
        println!(
            "Congratulations! You proved and verified a Keccak hash calculation in {:?} time!",
            pp_end + proof_end + verify_end
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
