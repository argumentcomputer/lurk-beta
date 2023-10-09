use bellpepper::gadgets::{multipack::pack_bits, sha256::sha256};
use bellpepper_core::{boolean::Boolean, ConstraintSystem, SynthesisError};
use lurk_macros::Coproc;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::marker::PhantomData;

use crate::{
    self as lurk,
    circuit::gadgets::{
        data::GlobalAllocations,
        pointer::{AllocatedContPtr, AllocatedPtr},
    },
    field::LurkField,
    num::Num,
    ptr::Ptr,
    store::Store,
    tag::{ExprTag, Tag},
};

use super::{CoCircuit, Coprocessor};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Sha256Coprocessor<F: LurkField> {
    n: usize,
    pub(crate) _p: PhantomData<F>,
}

impl<F: LurkField> CoCircuit<F> for Sha256Coprocessor<F> {
    fn arity(&self) -> usize {
        self.n
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _g: &GlobalAllocations<F>,
        _store: &Store<F>,
        input_exprs: &[AllocatedPtr<F>],
        input_env: &AllocatedPtr<F>,
        input_cont: &AllocatedContPtr<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        let zero = Boolean::constant(false);

        let mut bits = vec![];

        for input_ptr in input_exprs {
            let tag_bits = input_ptr
                .tag()
                .to_bits_le_strict(&mut cs.namespace(|| "preimage_tag_bits"))?;
            let hash_bits = input_ptr
                .hash()
                .to_bits_le_strict(&mut cs.namespace(|| "preimage_hash_bits"))?;

            bits.extend(tag_bits);
            bits.push(zero.clone()); // need 256 bits (or some multiple of 8).
            bits.extend(hash_bits);
            bits.push(zero.clone()); // need 256 bits (or some multiple of 8).
        }

        bits.reverse();

        let mut digest_bits = sha256(cs.namespace(|| "digest_bits"), &bits)?;

        digest_bits.reverse();

        // Fine to lose the last <1 bit of precision.
        let digest_scalar = pack_bits(cs.namespace(|| "digest_scalar"), &digest_bits)?;
        let output_expr = AllocatedPtr::alloc_tag(
            &mut cs.namespace(|| "output_expr"),
            ExprTag::Num.to_field(),
            digest_scalar,
        )?;
        Ok((output_expr, input_env.clone(), input_cont.clone()))
    }
}

impl<F: LurkField> Coprocessor<F> for Sha256Coprocessor<F> {
    fn eval_arity(&self) -> usize {
        self.n
    }

    fn simple_evaluate(&self, s: &Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
        let mut hasher = Sha256::new();

        let mut input = vec![0u8; 64 * self.n];

        for (i, input_ptr) in args.iter().enumerate() {
            let input_zptr = s.hash_expr(input_ptr).unwrap();
            let tag_zptr: F = input_zptr.tag().to_field();
            let hash_zptr = input_zptr.value();
            input[(64 * i)..(64 * i + 32)].copy_from_slice(&tag_zptr.to_bytes());
            input[(64 * i + 32)..(64 * (i + 1))].copy_from_slice(&hash_zptr.to_bytes());
        }

        input.reverse();

        hasher.update(input);
        let mut bytes = hasher.finalize();
        bytes.reverse();
        let l = bytes.len();
        // Discard the two most significant bits.
        bytes[l - 1] &= 0b00111111;

        let scalar = F::from_bytes(&bytes).unwrap();
        let result = Num::from_scalar(scalar);

        s.intern_num(result)
    }

    fn has_circuit(&self) -> bool {
        true
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

#[derive(Clone, Debug, Coproc, Serialize, Deserialize)]
pub enum Sha256Coproc<F: LurkField> {
    SC(Sha256Coprocessor<F>),
}
