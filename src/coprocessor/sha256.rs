use bellpepper::gadgets::{multipack::pack_bits, sha256::sha256};
use bellpepper_core::{boolean::Boolean, ConstraintSystem, SynthesisError};
use lurk_macros::Coproc;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::marker::PhantomData;

use crate::{
    self as lurk,
    circuit::gadgets::pointer::AllocatedPtr,
    field::LurkField,
    lem::{pointers::Ptr, store::Store},
    tag::{ExprTag, Tag},
    z_ptr::ZPtr,
};

use super::{CoCircuit, Coprocessor};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Sha256Coprocessor<F: LurkField> {
    n: usize,
    pub(crate) _p: PhantomData<F>,
}

fn synthesize_sha256<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    ptrs: &[AllocatedPtr<F>],
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let zero = Boolean::constant(false);

    let mut bits = vec![];

    let pad_to_next_len_multiple_of_8 = |bits: &mut Vec<_>| {
        bits.resize((bits.len() + 7) / 8 * 8, zero.clone());
    };

    for ptr in ptrs {
        let tag_bits = ptr
            .tag()
            .to_bits_le_strict(&mut cs.namespace(|| "preimage_tag_bits"))?;
        let hash_bits = ptr
            .hash()
            .to_bits_le_strict(&mut cs.namespace(|| "preimage_hash_bits"))?;

        bits.extend(tag_bits);
        pad_to_next_len_multiple_of_8(&mut bits);
        bits.extend(hash_bits);
        pad_to_next_len_multiple_of_8(&mut bits);
    }

    bits.reverse();

    let mut digest_bits = sha256(cs.namespace(|| "digest_bits"), &bits)?;

    digest_bits.reverse();

    // Fine to lose the last <1 bit of precision.
    let digest_scalar = pack_bits(cs.namespace(|| "digest_scalar"), &digest_bits)?;
    AllocatedPtr::alloc_tag(
        &mut cs.namespace(|| "output_expr"),
        ExprTag::Num.to_field(),
        digest_scalar,
    )
}

fn compute_sha256<F: LurkField, T: Tag>(n: usize, z_ptrs: &[ZPtr<T, F>]) -> F {
    let mut hasher = Sha256::new();

    let mut input = vec![0u8; 64 * n];

    for (i, z_ptr) in z_ptrs.iter().enumerate() {
        let tag_zptr: F = z_ptr.tag().to_field();
        let hash_zptr = z_ptr.value();
        input[(64 * i)..(64 * i + 32)].copy_from_slice(&tag_zptr.to_bytes());
        input[(64 * i + 32)..(64 * (i + 1))].copy_from_slice(&hash_zptr.to_bytes());
    }

    input.reverse();

    hasher.update(input);
    let mut bytes = hasher.finalize();

    // The pack_bits gadget used by the synthesize_sha256 function
    // sets the n most significant bits of the hash output to zero,
    // where n is 256 minus the field's capacity. We do the same
    // here to match the output.
    discard_bits::<F>(&mut bytes);
    bytes.reverse();
    F::from_bytes(&bytes).unwrap()
}

impl<F: LurkField> CoCircuit<F> for Sha256Coprocessor<F> {
    fn arity(&self) -> usize {
        self.n
    }

    #[inline]
    fn synthesize_simple<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _g: &lurk::lem::circuit::GlobalAllocator<F>,
        _s: &lurk::lem::store::Store<F>,
        _not_dummy: &Boolean,
        args: &[AllocatedPtr<F>],
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        synthesize_sha256(cs, args)
    }
}

impl<F: LurkField> Coprocessor<F> for Sha256Coprocessor<F> {
    fn eval_arity(&self) -> usize {
        self.n
    }

    fn has_circuit(&self) -> bool {
        true
    }

    fn evaluate_simple(&self, s: &Store<F>, args: &[Ptr]) -> Ptr {
        let z_ptrs = args.iter().map(|ptr| s.hash_ptr(ptr)).collect::<Vec<_>>();
        s.num(compute_sha256(self.n, &z_ptrs))
    }
}

impl<F: LurkField> Sha256Coprocessor<F> {
    pub fn new(n: usize) -> Self {
        Self {
            n,
            _p: Default::default(),
        }
    }
}

// Retains the Scalar::CAPACITY last bits of a big-endian input
fn discard_bits<Scalar: LurkField>(bytes: &mut [u8]) {
    let bits_to_zero = 256 - Scalar::CAPACITY as usize;
    let full_bytes_to_zero = bits_to_zero / 8;
    let partial_bits_to_zero = bits_to_zero % 8;

    bytes[..full_bytes_to_zero].iter_mut().for_each(|b| *b = 0);

    if partial_bits_to_zero > 0 {
        let mask = 0xFF >> partial_bits_to_zero;
        bytes[full_bytes_to_zero] &= mask;
    }
}

#[derive(Clone, Debug, Coproc, Serialize, Deserialize)]
pub enum Sha256Coproc<F: LurkField> {
    SC(Sha256Coprocessor<F>),
}
