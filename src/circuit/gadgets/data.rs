use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};
use neptune::{
    circuit2::poseidon_hash_allocated as poseidon_hash,
    circuit2_witness::poseidon_hash_allocated_witness,
    poseidon::{Arity, PoseidonConstants},
};

use crate::field::LurkField;
use crate::tag::{ContTag, ExprTag, Op1, Op2, Tag};

pub(crate) fn hash_poseidon<CS: ConstraintSystem<F>, F: LurkField, A: Arity<F>>(
    mut cs: CS,
    preimage: Vec<AllocatedNum<F>>,
    constants: &PoseidonConstants<F, A>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    if cs.is_witness_generator() {
        poseidon_hash_allocated_witness(&mut cs, &preimage, constants)
    } else {
        poseidon_hash(cs, preimage, constants)
    }
}

pub(crate) fn allocate_constant<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    val: F,
) -> AllocatedNum<F> {
    let allocated = AllocatedNum::<F>::alloc_infallible(cs.namespace(|| "allocate"), || val);

    // allocated * 1 = val
    cs.enforce(
        || "enforce constant",
        |lc| lc + allocated.get_variable(),
        |lc| lc + CS::one(),
        |_| Boolean::Constant(true).lc(CS::one(), val),
    );

    allocated
}

impl ExprTag {
    pub fn allocate_constant<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> AllocatedNum<F> {
        allocate_constant(
            &mut cs.namespace(|| format!("{self:?} tag")),
            self.to_field(),
        )
    }
}

impl ContTag {
    pub fn allocate_constant<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> AllocatedNum<F> {
        allocate_constant(
            &mut cs.namespace(|| format!("{self:?} base continuation tag")),
            self.to_field(),
        )
    }
}

impl Op1 {
    pub fn allocate_constant<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> AllocatedNum<F> {
        allocate_constant(
            &mut cs.namespace(|| format!("{self:?} tag")),
            self.to_field(),
        )
    }
}

impl Op2 {
    pub fn allocate_constant<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> AllocatedNum<F> {
        allocate_constant(
            &mut cs.namespace(|| format!("{self:?} tag")),
            self.to_field(),
        )
    }
}
