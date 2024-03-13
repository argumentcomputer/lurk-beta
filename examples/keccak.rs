//! # Circom Gadgets
//!
//! ## Fetching a remote Circom Gadget
//!
//! Declare a `CircomGadget` implementing a `reference` pointing to a valid Circom Gadget repository
//! and an existing release `version`. If the `CircomCoprocessor` can not find it locally it will directly
//! fetch the r1cs and wasm files from Github. When doing so, the files will be fetched from the repository
//! `https://github.com/lurk-lab/keccak-circom-gadget` and the release `v0.1.0`.
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use circom_scotia::r1cs::CircomInput;
use pasta_curves::pallas;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::sync::Arc;
use std::time::Instant;
use tiny_keccak::{Hasher, Keccak};

use lurk::circuit::gadgets::circom::{CircomGadget, CircomGadgetReference};
use lurk::circuit::gadgets::pointer::AllocatedPtr;

#[cfg(not(target_arch = "wasm32"))]
use lurk::coprocessor::circom::non_wasm::CircomCoprocessor;

use lurk::coprocessor::gadgets::{chain_car_cdr, construct_list};
use lurk::coprocessor::{CoCircuit, Coprocessor};
use lurk::dual_channel::dummy_terminal;
use lurk::field::LurkField;
use lurk::lang::Lang;
use lurk::lem::eval::{
    evaluate, make_cprocs_funcs_from_lang, make_eval_step_from_config, EvalConfig,
};
use lurk::lem::{pointers::Ptr, store::Store};
use lurk::proof::supernova::SuperNovaProver;
use lurk::proof::RecursiveSNARKTrait;
use lurk::public_parameters::{instance::Instance, supernova_public_params};
use lurk::state::user_sym;
use lurk::tag::{ExprTag, Tag};
use lurk_macros::Coproc;
use serde::{Deserialize, Serialize};

const REDUCTION_COUNT: usize = 10;

/*************************************************
 * Utilities
 *************************************************/
fn string_to_le_bits(input_string: &str) -> Vec<u32> {
    let bytes = input_string
        .chars()
        .flat_map(|c| c.to_string().into_bytes())
        .collect::<Vec<_>>();

    bellpepper::gadgets::multipack::bytes_to_bits_le(&bytes)
        .iter()
        .map(|b| if *b { 1 } else { 0 })
        .collect::<Vec<_>>()
}

// Transforms a slice of bits in a slice of bytes. Fills the bytes from least to most significant
// bit.
fn bits_to_bytes(bits: &[bool]) -> Vec<u8> {
    let mut bytes = vec![0; (bits.len() + 7) / 8]; // Initialize a vector with zeroes

    for (i, &bit) in bits.iter().enumerate() {
        // Iterate over each bit with its index
        let byte_index = i / 8; // Calculate the byte index for the current bit
        if bit {
            // If the current bit is true,
            bytes[byte_index] |= 1 << (i % 8); // Set the corresponding bit in the byte
        }
    }
    bytes // Return the array of bytes
}

/*************************************************
 * Lurk components
 *************************************************/

/// Program that will be proven and verified
fn lurk_program<F: LurkField>(store: &Store<F>, input: &str) -> Ptr {
    let program = format!(
        r#"
            (let ((bit-list (str_to_le_bits "{input}"))
                (hashed-output (keccak_hash bit-list)))
             hashed-output)
        "#,
    );

    store.read_with_default_state(&program).unwrap()
}

// List of coprocessor available
#[derive(Clone, Debug, Coproc)]
pub enum KeccakExampleCoproc<F: LurkField> {
    STB(StrToBits<F>),
    Keccak(CircomCoprocessor<F, CircomKeccak<F>>),
}

/*************************************************
 * String to LE bits
 *************************************************/

/// Structure representing the str_to_bits coprocessor
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StrToBits<F: LurkField> {
    /// Size of the input string
    n: usize,
    pub(crate) _p: PhantomData<F>,
}

impl<F: LurkField> CoCircuit<F> for StrToBits<F> {
    fn arity(&self) -> usize {
        1
    }

    #[inline]
    fn synthesize_simple<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &lurk::lem::circuit::GlobalAllocator<F>,
        s: &Store<F>,
        not_dummy: &Boolean,
        args: &[AllocatedPtr<F>],
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        // Get all str characters
        let (elts, _, _) = chain_car_cdr(cs, g, s, not_dummy, &args[0], self.n, false)?;
        // Convert to 8 bits per character
        let elts_u32 = elts
            .iter()
            .enumerate()
            .flat_map(|(i, e)| {
                e.hash()
                    .to_bits_le(&mut cs.namespace(|| format!("to_bits_le {i}")))
                    .unwrap()
                    .iter()
                    .take(8)
                    .map(|b| u32::from(b.get_value().unwrap_or(false)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        let mut elts_alloc_num = elts_u32
            .iter()
            .enumerate()
            .map(|(i, b)| {
                AllocatedNum::alloc(&mut cs.namespace(|| format!("alloc bit {i}")), || {
                    Ok(F::from(u64::from(*b)))
                })
            })
            .collect::<Result<Vec<AllocatedNum<F>>, SynthesisError>>()?;

        if elts_alloc_num.len() != 256 {
            elts_alloc_num.extend_from_slice(
                &(0..256 - elts_alloc_num.len())
                    .map(|i| {
                        AllocatedNum::alloc(
                            &mut cs.namespace(|| format!("pad bit {}", elts_alloc_num.len() + i)),
                            || Ok(F::ZERO),
                        )
                        .unwrap()
                    })
                    .collect::<Vec<AllocatedNum<F>>>(),
            );
        }
        // AllocatedNum to AllocatedPtr
        let elts_alloc_ptr = elts_alloc_num
            .into_iter()
            .enumerate()
            .map(|(i, n)| {
                AllocatedPtr::alloc_tag(
                    &mut cs.namespace(|| format!("alloc ptr {i}")),
                    ExprTag::Num.to_field(),
                    n,
                )
                .unwrap()
            })
            .collect::<Vec<AllocatedPtr<F>>>();

        let list = construct_list(cs, g, s, &elts_alloc_ptr, None)?;

        // Return the value
        Ok(list)
    }
}

impl<F: LurkField> Coprocessor<F> for StrToBits<F> {
    fn has_circuit(&self) -> bool {
        true
    }

    /// Converts a String to its le_bits representation
    fn evaluate_simple(&self, s: &Store<F>, args: &[Ptr]) -> Ptr {
        let str = s.fetch_string(&args[0]).unwrap();
        let le_bits = string_to_le_bits(&str);

        let mut le_bits_ptr = le_bits
            .into_iter()
            .map(|b| s.num(F::from(u64::from(b))))
            .collect::<Vec<Ptr>>();

        if le_bits_ptr.len() != 256 {
            le_bits_ptr.extend_from_slice(
                &(0..256 - le_bits_ptr.len())
                    .map(|_| s.num(F::ZERO))
                    .collect::<Vec<_>>(),
            );
        }

        s.list(le_bits_ptr)
    }
}

impl<F: LurkField> StrToBits<F> {
    pub fn new(n: usize) -> Self {
        Self {
            n,
            _p: Default::default(),
        }
    }
}

/// Structure representing the Keccak gadget used in the Circom Coprocessor
#[derive(Debug, Clone)]
pub struct CircomKeccak<F: LurkField> {
    /// Size of the incoming bit vector
    n: usize,
    pub(crate) _p: PhantomData<F>,
    reference: CircomGadgetReference,
}

impl<F: LurkField> CircomKeccak<F> {
    fn new(n: usize) -> Self {
        CircomKeccak {
            n,
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

    fn into_circom_input<CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
        g: &lurk::lem::circuit::GlobalAllocator<F>,
        s: &Store<F>,
        not_dummy: &bellpepper_core::boolean::Boolean,
        inputs: &[AllocatedPtr<F>],
    ) -> Result<Vec<CircomInput<F>>, SynthesisError> {
        // Get all bits
        let (elts, _, _) = chain_car_cdr(cs, g, s, not_dummy, &inputs[0], self.n, false)?;

        // Constraint that they are bits
        let mut elts_alloc_bits = elts
            .iter()
            .enumerate()
            .map(|(i, e)| {
                AllocatedBit::alloc(
                    &mut cs.namespace(|| format!("alloc bit {i}")),
                    if e.hash().get_value().unwrap_or(F::ZERO) == F::ZERO {
                        Some(false)
                    } else {
                        Some(true)
                    },
                )
                .unwrap()
            })
            .collect::<Vec<_>>();

        // Padding to 256 bits
        elts_alloc_bits.extend_from_slice(
            &(0..256 - self.n)
                .map(|i| {
                    AllocatedBit::alloc(&mut cs.namespace(|| format!("alloc bit {i}")), Some(false))
                        .unwrap()
                })
                .collect::<Vec<_>>(),
        );

        Ok(vec![CircomInput::new(
            "in".parse().unwrap(),
            elts_alloc_bits
                .iter()
                .map(|e| {
                    if e.get_value().unwrap_or(true) {
                        F::ONE
                    } else {
                        F::ZERO
                    }
                })
                .collect::<_>(),
        )])
    }

    fn evaluate_simple(&self, s: &Store<F>, args: &[Ptr]) -> Ptr {
        let (bits, _) = s.fetch_list(&args[0]).unwrap();

        let z_bits = bits.iter().map(|ptr| s.hash_ptr(ptr)).collect::<Vec<_>>();

        let bytes_to_hash = bits_to_bytes(
            &z_bits
                .iter()
                .map(|ptr| ptr.value() != &F::ZERO)
                .collect::<Vec<_>>(),
        );

        // Calculate the Keccak-256 hash
        let mut hasher = Keccak::v256();
        hasher.update(&bytes_to_hash);
        let mut output_bytes = [0u8; 32];
        hasher.finalize(&mut output_bytes);
        // Convert the output bytes into a Vec<u8> representing bits
        let output_bits_ptr = bellpepper::gadgets::multipack::bytes_to_bits_le(&output_bytes)
            .iter()
            .map(|b| if *b { s.num(F::ONE) } else { s.num(F::ZERO) })
            .collect::<Vec<Ptr>>();

        s.list(output_bits_ptr)
    }

    fn arity(&self) -> usize {
        1
    }
}

fn main() {
    // Get command line input
    let args = std::env::args().collect::<Vec<_>>();

    // Initialize store, responsible for handling variables in the lurk context
    let store: &Store<pallas::Scalar> = &Store::default();

    // Define the symbol that will call upon our Coprocessor
    let str_to_le_bits_sym = user_sym("str_to_le_bits");
    let keccak_sym = user_sym("keccak_hash");
    let program = lurk_program(store, &args[1]);

    // Create the Lang. ie the list of corprocessor that will be accessible in our program
    let mut lang = Lang::<pallas::Scalar, KeccakExampleCoproc<pallas::Scalar>>::new();
    lang.add_coprocessor(str_to_le_bits_sym, StrToBits::new(args[1].len()));
    lang.add_coprocessor(
        keccak_sym,
        CircomCoprocessor::new(CircomKeccak::new(args[1].len() * 8)),
    );

    let lurk_step = make_eval_step_from_config(&EvalConfig::new_nivc(&lang));
    let cprocs = make_cprocs_funcs_from_lang(&lang);

    println!("Evaluating Lurk program..");

    let frames = evaluate(
        Some((&lurk_step, &cprocs, &lang)),
        program,
        store,
        1000,
        &dummy_terminal(),
    )
    .unwrap();
    let bits_out = bits_to_bytes(
        &store
            .fetch_list(&frames.last().unwrap().output[0])
            .unwrap()
            .0
            .iter()
            .map(|ptr| ptr.raw().get_atom().unwrap() == 1)
            .collect::<Vec<_>>(),
    );

    println!("Evaluated Lurk program, output: {:?}", bits_out);

    let supernova_prover =
        SuperNovaProver::<pallas::Scalar, KeccakExampleCoproc<pallas::Scalar>>::new(
            REDUCTION_COUNT,
            Arc::new(lang),
        );

    let pp_start = Instant::now();

    println!("Setting up running claim parameters (rc = {REDUCTION_COUNT})...");
    let instance_primary = Instance::new_supernova(&supernova_prover, true);
    let pp = supernova_public_params(&instance_primary).unwrap();
    let pp_end = pp_start.elapsed();
    println!("Running claim parameters took {:?}", pp_end);

    println!("Beginning proof step...");
    let proof_start = Instant::now();

    let (proof, z0, zi, _) = supernova_prover
        .prove_from_frames(&pp, &frames, store)
        .unwrap();

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

    let compressed_verify_start = Instant::now();
    let res = compressed_proof.verify(&pp, &z0, &zi).unwrap();
    assert!(res);

    let compressed_verify_end = compressed_verify_start.elapsed();
    println!("Final verification took {:?}", compressed_verify_end);
    println!(
        "Congratulations! You proved, verified, compressed, and verified (again!) an NIVC Keccak hash calculation in {:?} time!",
        verify_end + proof_end + verify_end + compress_end
    );
}
