use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem};

use crate::field::LurkField;
use crate::tag::{ContTag, ExprTag, Op1, Op2, Tag};

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
        allocate_constant(ns!(cs, format!("{self:?} tag")), self.to_field())
    }
}

impl ContTag {
    pub fn allocate_constant<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> AllocatedNum<F> {
        allocate_constant(
            ns!(cs, format!("{self:?} base continuation tag")),
            self.to_field(),
        )
    }
}

impl Op1 {
    pub fn allocate_constant<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> AllocatedNum<F> {
        allocate_constant(ns!(cs, format!("{self:?} tag")), self.to_field())
    }
}

impl Op2 {
    pub fn allocate_constant<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> AllocatedNum<F> {
        allocate_constant(ns!(cs, format!("{self:?} tag")), self.to_field())
    }
}
