#![allow(unreachable_pub)]
#![allow(dead_code)]

//! First implementation of `Elt`, a generalization of `AllocatedNum`. It tries
//! to be the most general version of what could be considered a field element,
//! without needing to allocate. Because of the ubiquitous usage of linear
//! combinations, it might be too slow to synthesize.

use crate::field::LurkField;
use bellperson::LinearCombination;
use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    ConstraintSystem, SynthesisError,
};
use ff::PrimeField;

#[derive(Clone)]
pub enum Elt<Scalar: PrimeField> {
    Linear(Option<Scalar>, LinearCombination<Scalar>),
    Constant(Scalar),
}

impl<Scalar: PrimeField> From<AllocatedNum<Scalar>> for Elt<Scalar> {
    fn from(num: AllocatedNum<Scalar>) -> Elt<Scalar> {
        Elt::Linear(
            num.get_value(),
            LinearCombination::<Scalar>::from_variable(num.get_variable()),
        )
    }
}

impl<Scalar: PrimeField> From<Scalar> for Elt<Scalar> {
    fn from(num: Scalar) -> Elt<Scalar> {
        Elt::Constant(num)
    }
}

impl<Scalar: PrimeField> Elt<Scalar> {
    pub fn get_value(&self) -> Option<&Scalar> {
        match self {
            Elt::Constant(a) => Some(a),
            Elt::Linear(v, _) => v.as_ref(),
        }
    }

    pub fn is_zero(&self) -> Option<bool> {
        self.get_value().map(|b| b.is_zero().into())
    }

    pub fn lc<CS: ConstraintSystem<Scalar>>(&self) -> LinearCombination<Scalar> {
        match self {
            Elt::Constant(a) => LinearCombination::from_coeff(CS::one(), *a),
            Elt::Linear(_, lc) => lc.clone(),
        }
    }

    pub fn add<CS: ConstraintSystem<Scalar>>(self, other: &Self) -> Self {
        use Elt::*;
        match (self, other) {
            (Constant(a), Constant(b)) => Constant(a + b),
            (Constant(a), Linear(v_b, lc_b)) => {
                Linear(v_b.map(|b| a + b), lc_b.clone() + (a, CS::one()))
            }
            (Linear(v_a, lc_a), Constant(b)) => Linear(v_a.map(|a| a + b), lc_a + (*b, CS::one())),
            (Linear(v_a, lc_a), Linear(v_b, lc_b)) => {
                Linear(v_a.and_then(|a| v_b.map(|b| a + b)), lc_a + lc_b)
            }
        }
    }

    pub fn sub<CS: ConstraintSystem<Scalar>>(self, other: &Self) -> Self {
        use Elt::*;
        match (self, other) {
            (Constant(a), Constant(b)) => Constant(a - b),
            (Constant(a), Linear(v_b, lc_b)) => {
                Linear(v_b.map(|b| a - b), lc_b.clone() - (a, CS::one()))
            }
            (Linear(v_a, lc_a), Constant(b)) => Linear(v_a.map(|a| a - b), lc_a - (*b, CS::one())),
            (Linear(v_a, lc_a), Linear(v_b, lc_b)) => {
                Linear(v_a.and_then(|a| v_b.map(|b| a - b)), lc_a - lc_b)
            }
        }
    }
}

fn scale_lc_mut<F: PrimeField>(scalar: F, lc: &mut LinearCombination<F>) {
    for (_variable, fr) in lc.iter_mut() {
        fr.mul_assign(&scalar);
    }
}

fn scale_lc<F: PrimeField>(scalar: F, lc: &LinearCombination<F>) -> LinearCombination<F> {
    let mut lc = lc.clone();
    scale_lc_mut(scalar, &mut lc);
    lc
}

pub(crate) fn mul<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &Elt<F>,
    b: &Elt<F>,
) -> Result<Elt<F>, SynthesisError> {
    use Elt::*;
    match (a, b) {
        (Constant(a), Constant(b)) => Ok(Constant(*a * *b)),
        (Constant(a), Linear(v_b, lc_b)) => Ok(Linear(v_b.map(|b| *a * b), scale_lc(*a, lc_b))),
        (Linear(v_a, lc_a), Constant(b)) => Ok(Linear(v_a.map(|a| a * b), scale_lc(*b, lc_a))),
        (Linear(v_a, lc_a), Linear(v_b, lc_b)) => {
            let v_c = v_a.and_then(|a| v_b.map(|b| a * b));
            let alloc_c = AllocatedNum::alloc(cs.namespace(|| "alloc_mul"), || Ok(v_c.unwrap()))?;
            cs.enforce(
                || "enforce_mul",
                |_| lc_a.clone(),
                |_| lc_b.clone(),
                |lc| lc + alloc_c.get_variable(),
            );
            Ok(Linear(
                v_c,
                LinearCombination::from_variable(alloc_c.get_variable()),
            ))
        }
    }
}

pub(crate) fn div<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &Elt<F>,
    b: &Elt<F>,
) -> Result<Elt<F>, SynthesisError> {
    use Elt::*;
    if let Some(true) = b.is_zero() {
        return Err(SynthesisError::DivisionByZero);
    }
    match (a, b) {
        (Constant(a), Constant(b)) => Ok(Constant(*a * b.invert().unwrap())),
        (Linear(v_a, lc_a), Constant(b)) => {
            let b_inv = b.invert().unwrap();
            Ok(Linear(v_a.map(|a| a * b_inv), scale_lc(b_inv, lc_a)))
        }
        (Constant(a), Linear(v_b, lc_b)) => {
            let v_c = v_b.map(|b| *a * b.invert().unwrap());
            let alloc_c = AllocatedNum::alloc(cs.namespace(|| "alloc_div"), || Ok(v_c.unwrap()))?;
            cs.enforce(
                || "enforce_div",
                |lc| lc + alloc_c.get_variable(),
                |_| lc_b.clone(),
                |lc| lc + (*a, CS::one()),
            );
            Ok(Linear(
                v_c,
                LinearCombination::from_variable(alloc_c.get_variable()),
            ))
        }
        (Linear(v_a, lc_a), Linear(v_b, lc_b)) => {
            let v_c = v_a.and_then(|a| v_b.map(|b| a * b));
            let alloc_c = AllocatedNum::alloc(cs.namespace(|| "alloc_div"), || Ok(v_c.unwrap()))?;
            cs.enforce(
                || "enforce_div",
                |lc| lc + alloc_c.get_variable(),
                |_| lc_b.clone(),
                |_| lc_a.clone(),
            );
            Ok(Linear(
                v_c,
                LinearCombination::from_variable(alloc_c.get_variable()),
            ))
        }
    }
}

pub(crate) fn boolean_to_elt<F: PrimeField, CS: ConstraintSystem<F>>(
    bit: &Boolean,
) -> Result<Elt<F>, SynthesisError>
where
    CS: ConstraintSystem<F>,
{
    let from_bool = |b| if b { F::ONE } else { F::ZERO };
    match bit {
        Boolean::Is(alloc_b) => {
            let value = alloc_b.get_value().map(from_bool);
            let lc = LinearCombination::from_variable(alloc_b.get_variable());
            Ok(Elt::Linear(value, lc))
        }
        Boolean::Not(alloc_b) => {
            let value = alloc_b.get_value().map(|b| from_bool(!b));
            let lc_one = LinearCombination::from_variable(CS::one());
            Ok(Elt::Linear(value, lc_one - alloc_b.get_variable()))
        }
        Boolean::Constant(b) => Ok(Elt::Constant(from_bool(*b))),
    }
}

/// Enforce equality of two allocated numbers given an implication premise
pub(crate) fn implies_equal<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    premise: &Boolean,
    a: &Elt<F>,
    b: &Elt<F>,
) {
    let premise = |_| premise.lc(CS::one(), F::ONE);
    let diff = |_| a.lc::<CS>() - &b.lc::<CS>();
    let zero = |lc| lc;
    // premise * diff = zero
    cs.enforce(|| "implication", premise, diff, zero);
}
