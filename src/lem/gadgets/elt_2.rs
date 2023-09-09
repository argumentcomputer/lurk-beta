#![allow(unreachable_pub)]
#![allow(dead_code)]

//! Second implementation of `Elt`, a generalization of `AllocatedNum`. This one
//! is less general than the first version, but is simpler and much faster to
//! synthesize.

use crate::field::LurkField;
use bellperson::LinearCombination;
use bellperson::{
    gadgets::{
        boolean::{AllocatedBit, Boolean},
        num::AllocatedNum,
    },
    ConstraintSystem, SynthesisError, Variable,
};
use ff::PrimeField;

#[derive(Clone)]
pub struct Elt<Scalar: PrimeField> {
    coef: Scalar,
    value: Option<Scalar>,
    variable: Variable,
}

impl<Scalar: PrimeField> From<AllocatedNum<Scalar>> for Elt<Scalar> {
    fn from(num: AllocatedNum<Scalar>) -> Elt<Scalar> {
        Elt {
            coef: Scalar::ONE,
            value: num.get_value(),
            variable: num.get_variable(),
        }
    }
}

impl<Scalar: PrimeField> Elt<Scalar> {
    pub fn from_scalar<CS: ConstraintSystem<Scalar>>(coef: Scalar) -> Elt<Scalar> {
        Elt {
            coef,
            value: Some(coef),
            variable: CS::one(),
        }
    }

    pub fn get_value(&self) -> Option<&Scalar> {
        self.value.as_ref()
    }

    pub fn is_zero(&self) -> Option<bool> {
        self.value.map(|b| b.is_zero().into())
    }

    pub fn add<CS: ConstraintSystem<Scalar>>(
        self,
        other: &Self,
        mut cs: CS,
    ) -> Result<Self, SynthesisError> {
        let value = self.value.and_then(|a| other.value.map(|b| a + b));
        if self.variable == other.variable {
            let elt = Elt {
                coef: self.coef + other.coef,
                value,
                variable: self.variable,
            };
            Ok(elt)
        } else {
            let variable = cs.alloc(|| "sum", || value.ok_or(SynthesisError::AssignmentMissing))?;
            cs.enforce(
                || "enforce_sum",
                |lc| lc + CS::one(),
                |lc| lc + variable,
                |lc| lc + (self.coef, self.variable) + (other.coef, other.variable),
            );

            let elt = Elt {
                coef: Scalar::ONE,
                value,
                variable,
            };
            Ok(elt)
        }
    }

    pub fn sub<CS: ConstraintSystem<Scalar>>(
        self,
        other: &Self,
        mut cs: CS,
    ) -> Result<Self, SynthesisError> {
        let value = self.value.and_then(|a| other.value.map(|b| a - b));
        if self.variable == other.variable {
            let elt = Elt {
                coef: self.coef - other.coef,
                value,
                variable: self.variable,
            };
            Ok(elt)
        } else {
            let variable =
                cs.alloc(|| "diff", || value.ok_or(SynthesisError::AssignmentMissing))?;
            cs.enforce(
                || "enforce_diff",
                |lc| lc + CS::one(),
                |lc| lc + variable,
                |lc| lc + (self.coef, self.variable) - (other.coef, other.variable),
            );

            let elt = Elt {
                coef: Scalar::ONE,
                value,
                variable,
            };
            Ok(elt)
        }
    }

    pub fn mul<CS: ConstraintSystem<Scalar>>(
        self,
        other: &Self,
        mut cs: CS,
    ) -> Result<Self, SynthesisError> {
        let value = self.value.and_then(|a| other.value.map(|b| a * b));
        if self.variable == CS::one() {
            let elt = Elt {
                coef: self.coef * other.coef,
                value,
                variable: other.variable,
            };
            return Ok(elt);
        }
        if other.variable == CS::one() {
            let elt = Elt {
                coef: self.coef * other.coef,
                value,
                variable: self.variable,
            };
            return Ok(elt);
        }
        let variable = cs.alloc(|| "mul", || value.ok_or(SynthesisError::AssignmentMissing))?;
        cs.enforce(
            || "enforce_mul",
            |lc| lc + (self.coef, self.variable),
            |lc| lc + (other.coef, other.variable),
            |lc| lc + variable,
        );

        let elt = Elt {
            coef: Scalar::ONE,
            value,
            variable,
        };
        Ok(elt)
    }

    pub fn div<CS: ConstraintSystem<Scalar>>(
        self,
        other: &Self,
        mut cs: CS,
    ) -> Result<Self, SynthesisError> {
        if let Some(true) = other.is_zero() {
            return Err(SynthesisError::DivisionByZero);
        }

        let value = self.value.and_then(|a| {
            other.value.map(|b| {
                let b_inv = b.invert().unwrap();
                a * b_inv
            })
        });
        if self.variable == CS::one() {
            let elt = Elt {
                coef: self.coef * other.coef.invert().unwrap(),
                value,
                variable: other.variable,
            };
            return Ok(elt);
        }
        if other.variable == CS::one() {
            let elt = Elt {
                coef: self.coef * other.coef.invert().unwrap(),
                value,
                variable: self.variable,
            };
            return Ok(elt);
        }
        let variable = cs.alloc(|| "div", || value.ok_or(SynthesisError::AssignmentMissing))?;
        cs.enforce(
            || "enforce_div",
            |lc| lc + variable,
            |lc| lc + (other.coef, other.variable),
            |lc| lc + (self.coef, self.variable),
        );

        let elt = Elt {
            coef: Scalar::ONE,
            value,
            variable,
        };
        Ok(elt)
    }
}
