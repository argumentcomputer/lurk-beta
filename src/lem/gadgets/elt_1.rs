#![allow(unreachable_pub)]
#![allow(dead_code)]

//! First implementation of `Elt`, a generalization of `AllocatedNum`. It tries
//! to be the most general version of what could be considered a field element,
//! without needing to allocate. Because of the ubiquitous usage of linear
//! combinations, it might be too slow to synthesize.

use crate::field::LurkField;
use bellperson::LinearCombination;
use bellperson::{
    gadgets::{
        boolean::{AllocatedBit, Boolean},
        num::AllocatedNum,
    },
    ConstraintSystem, SynthesisError,
};
use ff::{PrimeField, PrimeFieldBits};

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
    pub fn to_num<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
    ) -> Result<AllocatedNum<Scalar>, SynthesisError> {
        let val = self.get_value().cloned();
        let num = AllocatedNum::alloc(cs.namespace(|| "alloc elt"), || {
            val.ok_or(SynthesisError::AssignmentMissing)
        })?;
        cs.enforce(
            || "enforce elt",
            |_| self.lc::<CS>(),
            |lc| lc + CS::one(),
            |lc| lc + num.get_variable(),
        );
        Ok(num)
    }

    pub fn zero() -> Self {
        Elt::Constant(Scalar::ZERO)
    }

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

    pub fn add<CS: ConstraintSystem<Scalar>>(&self, other: &Self) -> Self {
        use Elt::*;
        match (self, other) {
            (Constant(a), Constant(b)) => Constant(*a + b),
            (Constant(a), Linear(v_b, lc_b)) => {
                Linear(v_b.map(|b| *a + b), lc_b.clone() + (*a, CS::one()))
            }
            (Linear(v_a, lc_a), Constant(b)) => {
                Linear(v_a.map(|a| a + b), lc_a.clone() + (*b, CS::one()))
            }
            (Linear(v_a, lc_a), Linear(v_b, lc_b)) => {
                Linear(v_a.and_then(|a| v_b.map(|b| a + b)), lc_a.clone() + lc_b)
            }
        }
    }

    pub fn sub<CS: ConstraintSystem<Scalar>>(&self, other: &Self) -> Self {
        use Elt::*;
        match (self, other) {
            (Constant(a), Constant(b)) => Constant(*a - b),
            (Constant(a), Linear(v_b, lc_b)) => {
                Linear(v_b.map(|b| *a - b), lc_b.clone() - (*a, CS::one()))
            }
            (Linear(v_a, lc_a), Constant(b)) => {
                Linear(v_a.map(|a| a - b), lc_a.clone() - (*b, CS::one()))
            }
            (Linear(v_a, lc_a), Linear(v_b, lc_b)) => {
                Linear(v_a.and_then(|a| v_b.map(|b| a - b)), lc_a.clone() - lc_b)
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

pub fn mul<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &Elt<F>,
    b: &Elt<F>,
) -> Result<Elt<F>, SynthesisError> {
    use Elt::*;
    use SynthesisError::*;
    match (a, b) {
        (Constant(a), Constant(b)) => Ok(Constant(*a * *b)),
        (Constant(a), Linear(v_b, lc_b)) => Ok(Linear(v_b.map(|b| *a * b), scale_lc(*a, lc_b))),
        (Linear(v_a, lc_a), Constant(b)) => Ok(Linear(v_a.map(|a| a * b), scale_lc(*b, lc_a))),
        (Linear(v_a, lc_a), Linear(v_b, lc_b)) => {
            let v_c = v_a.and_then(|a| v_b.map(|b| a * b));
            let alloc_c = AllocatedNum::alloc(cs.namespace(|| "alloc_mul"), || {
                v_c.ok_or(AssignmentMissing)
            })?;
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

pub fn div<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &Elt<F>,
    b: &Elt<F>,
) -> Result<Elt<F>, SynthesisError> {
    use Elt::*;
    use SynthesisError::*;
    if let Some(true) = b.is_zero() {
        return Err(DivisionByZero);
    }
    match (a, b) {
        (Constant(a), Constant(b)) => Ok(Constant(*a * b.invert().unwrap())),
        (Linear(v_a, lc_a), Constant(b)) => {
            let b_inv = b.invert().unwrap();
            Ok(Linear(v_a.map(|a| a * b_inv), scale_lc(b_inv, lc_a)))
        }
        (Constant(a), Linear(v_b, lc_b)) => {
            let v_c = v_b.map(|b| *a * b.invert().unwrap());
            let alloc_c = AllocatedNum::alloc(cs.namespace(|| "alloc_div"), || {
                v_c.ok_or(AssignmentMissing)
            })?;
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
            let alloc_c = AllocatedNum::alloc(cs.namespace(|| "alloc_div"), || {
                v_c.ok_or(AssignmentMissing)
            })?;
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

pub fn boolean_to_elt<F: PrimeField, CS: ConstraintSystem<F>>(bit: &Boolean) -> Elt<F> {
    let from_bool = |b| if b { F::ONE } else { F::ZERO };
    match bit {
        Boolean::Is(alloc_b) => {
            let value = alloc_b.get_value().map(from_bool);
            let lc = LinearCombination::from_variable(alloc_b.get_variable());
            Elt::Linear(value, lc)
        }
        Boolean::Not(alloc_b) => {
            let value = alloc_b.get_value().map(|b| from_bool(!b));
            let lc_one = LinearCombination::from_variable(CS::one());
            Elt::Linear(value, lc_one - alloc_b.get_variable())
        }
        Boolean::Constant(b) => Elt::Constant(from_bool(*b)),
    }
}

// Apart from arithmetic, conversion and miscellaneous gadgets, we try to follow a pattern.
// Gadgets should be built from small building blocks, and they usually constrain the inputs
// and might return allocated variables. The ones that do not return an allocated variable
// of some sort have two different flavours: `implies` and `enforce` gadgets. The `implies`
// gadgets take a boolean premise, and should only constrain the inputs IF the premise is has
// a true value. `enforce` gadgets will constrain regardless, and if possible, they should be
// defined from a more general `implies` gadget where the premise is a true constant, i.e.
// `Bool::constant(true)`. The gadgets that return allocated variables will be preceeded by
// `alloc`. One might get away with only `implies`/`enforce` gadgets by allocating unconstrained
// variables and constraining them later with these gadgets.

/// Enforce equality of two allocated numbers given an implication premise
pub fn implies_equal<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    prem: &Boolean,
    a: &Elt<F>,
    b: &Elt<F>,
) {
    let prem = |_| prem.lc(CS::one(), F::ONE);
    let diff = |_| a.lc::<CS>() - &b.lc::<CS>();
    let zero = |lc| lc;
    // prem * diff = zero
    cs.enforce(|| "implication", prem, diff, zero);
}

pub fn implies_unequal<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    prem: &Boolean,
    a: &Elt<F>,
    b: &Elt<F>,
) -> Result<(), SynthesisError> {
    use SynthesisError::*;
    // We know that `a != b` iff `a-b` has an inverse, i.e. that there exists
    // `c` such that `c * (a-b) = 1`. Thus, we can add the constraint that there
    // must exist `c` such that `c * (a-b) = prem`, enforcing the difference
    // only when `prem = 1`; otherwise the constraint is trivially satisfied
    // for `c = 0`
    let q = cs.alloc(
        || "q",
        || {
            let prem = prem.get_value().ok_or(AssignmentMissing)?;
            if prem {
                let a = a.get_value().ok_or(AssignmentMissing)?;
                let b = b.get_value().ok_or(AssignmentMissing)?;
                let inv: Option<_> = (*a - *b).invert().into();
                inv.ok_or(DivisionByZero)
            } else {
                Ok(F::ZERO)
            }
        },
    )?;
    let maybe_inv = |lc| lc + q;
    let diff = |_| a.lc::<CS>() - &b.lc::<CS>();
    let prem = |_| prem.lc(CS::one(), F::ONE);

    cs.enforce(|| "implication", maybe_inv, diff, prem);
    Ok(())
}

/// If premise is true, enforce v is the bit decomposition of num, therefore we have that 0 <= num < 2ˆ(sizeof(v)).
pub fn implies_pack<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    premise: &Boolean,
    v: &[Boolean],
    num: &Elt<F>,
) -> Result<(), SynthesisError> {
    let mut coeff = F::ONE;
    let mut pack = LinearCombination::<F>::zero();
    for b in v {
        pack = pack + &b.lc(CS::one(), coeff);
        coeff = coeff.double();
    }
    let diff = |_| pack - &num.lc::<CS>();
    let premise_lc = |_| premise.lc(CS::one(), F::ONE);
    let zero = |lc| lc;

    cs.enforce(|| "pack", diff, premise_lc, zero);

    Ok(())
}

pub(crate) fn enforce_pack<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: CS,
    v: &[Boolean],
    num: &Elt<F>,
) -> Result<(), SynthesisError> {
    implies_pack(cs, &Boolean::Constant(true), v, num)
}

/// If premise is true, enforce `a` fits into 64 bits. It shows a non-deterministic
/// partial bit decomposition in order to constraint correct behavior.
pub fn implies_u64<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    premise: &Boolean,
    a: &Elt<F>,
) -> Result<(), SynthesisError> {
    let mut a_u64 = a.get_value().and_then(|a| a.to_u64()).unwrap_or(0);

    let mut bits: Vec<Boolean> = Vec::with_capacity(64);
    for i in 0..64 {
        let b = a_u64 & 1;
        let b_bool = Boolean::Is(AllocatedBit::alloc(
            cs.namespace(|| format!("b.{i}")),
            Some(b == 1),
        )?);
        bits.push(b_bool);

        a_u64 /= 2;
    }

    // premise -> a = sum(bits)
    implies_pack(
        cs.namespace(|| "u64 bit decomposition check"),
        premise,
        &bits,
        a,
    )?;

    Ok(())
}

pub fn alloc_is_equal<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    a: &Elt<F>,
    b: &Elt<F>,
) -> Result<Boolean, SynthesisError> {
    // If both are constants, then there's no need to allocate anything
    if let (Elt::Constant(a), Elt::Constant(b)) = (a, b) {
        return Ok(Boolean::Constant(a == b));
    }
    let is_eq_val = a.get_value().and_then(|a| b.get_value().map(|b| a == b));
    let is_eq = Boolean::Is(AllocatedBit::alloc(cs.namespace(|| "is_eq"), is_eq_val)?);
    implies_equal(cs.namespace(|| "a = b"), &is_eq, a, b);
    implies_unequal(cs.namespace(|| "a != b"), &is_eq.not(), a, b)?;
    Ok(is_eq)
}

pub fn alloc_pick<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    condition: &Boolean,
    a: &Elt<F>,
    b: &Elt<F>,
) -> Result<Elt<F>, SynthesisError> {
    // If condition is a constant, then there's no need to allocate anything
    if let Boolean::Constant(condition) = condition {
        return Ok(if *condition { a.clone() } else { b.clone() });
    }
    let c = AllocatedNum::alloc(cs.namespace(|| "pick result"), || {
        if condition
            .get_value()
            .ok_or(SynthesisError::AssignmentMissing)?
        {
            a.get_value()
                .ok_or(SynthesisError::AssignmentMissing)
                .copied()
        } else {
            b.get_value()
                .ok_or(SynthesisError::AssignmentMissing)
                .copied()
        }
    })?;
    // Constrain (b - a) * condition = (b - c), ensuring c = a iff
    // condition is true, otherwise c = b.
    let a_lc = a.lc::<CS>();
    let b_lc = b.lc::<CS>();
    cs.enforce(
        || "pick",
        |lc| lc + &b_lc - &a_lc,
        |_| condition.lc(CS::one(), F::ONE),
        |lc| lc + &b_lc - c.get_variable(),
    );

    Ok(Elt::from(c))
}

pub fn elt_to_bits_le_strict<F: PrimeFieldBits, CS: ConstraintSystem<F>>(
    mut cs: CS,
    num: &Elt<F>,
) -> Result<Vec<Boolean>, SynthesisError> {
    pub fn kary_and<F: PrimeField, CS: ConstraintSystem<F>>(
        mut cs: CS,
        v: &[AllocatedBit],
    ) -> Result<AllocatedBit, SynthesisError> {
        assert!(!v.is_empty());

        // Let's keep this simple for now and just AND them all
        // manually
        let mut cur = None;

        for (i, v) in v.iter().enumerate() {
            if cur.is_none() {
                cur = Some(v.clone());
            } else {
                cur = Some(AllocatedBit::and(
                    cs.namespace(|| format!("and {}", i)),
                    cur.as_ref().unwrap(),
                    v,
                )?);
            }
        }

        Ok(cur.expect("v.len() > 0"))
    }

    // We want to ensure that the bit representation of a is
    // less than or equal to r - 1.
    let a = num.get_value().map(|e| e.to_le_bits());
    let b = (-F::ONE).to_le_bits();

    // Get the bits of `a` in big-endian order.
    let mut a = a.as_ref().map(|e| e.into_iter().rev());

    let mut result = vec![];

    // Runs of ones in r
    let mut last_run = None;
    let mut current_run = vec![];

    let mut found_one = false;
    let mut i = 0;
    for b in b.into_iter().rev() {
        let a_bit: Option<bool> = a.as_mut().map(|e| *e.next().unwrap());

        // Skip over unset bits at the beginning
        found_one |= b;
        if !found_one {
            // a_bit should also be false
            if let Some(a_bit) = a_bit {
                assert!(!a_bit);
            }
            continue;
        }

        if b {
            // This is part of a run of ones. Let's just
            // allocate the boolean with the expected value.
            let a_bit = AllocatedBit::alloc(cs.namespace(|| format!("bit {}", i)), a_bit)?;
            // ... and add it to the current run of ones.
            current_run.push(a_bit.clone());
            result.push(a_bit);
        } else {
            if !current_run.is_empty() {
                // This is the start of a run of zeros, but we need
                // to k-ary AND against `last_run` first.

                if last_run.is_some() {
                    current_run.push(last_run.clone().unwrap());
                }
                last_run = Some(kary_and(
                    cs.namespace(|| format!("run ending at {}", i)),
                    &current_run,
                )?);
                current_run.truncate(0);
            }

            // If `last_run` is true, `a` must be false, or it would
            // not be in the field.
            //
            // If `last_run` is false, `a` can be true or false.

            let a_bit = AllocatedBit::alloc_conditionally(
                cs.namespace(|| format!("bit {}", i)),
                a_bit,
                last_run.as_ref().expect("char always starts with a one"),
            )?;
            result.push(a_bit);
        }

        i += 1;
    }

    // char is prime, so we'll always end on
    // a run of zeros.
    assert_eq!(current_run.len(), 0);

    // Now, we have `result` in big-endian order.
    // However, now we have to unpack self!

    let mut lc = LinearCombination::zero();
    let mut coeff = F::ONE;

    for bit in result.iter().rev() {
        lc = lc + (coeff, bit.get_variable());

        coeff = coeff.double();
    }

    lc = lc - &num.lc::<CS>();

    cs.enforce(|| "unpacking constraint", |lc| lc, |lc| lc, |_| lc);

    // Convert into booleans, and reverse for little-endian bit order
    Ok(result.into_iter().map(Boolean::from).rev().collect())
}

/// Allocate Boolean for predicate "num is negative".
/// We have that a number is defined to be negative if the parity bit (the
/// least significant bit) is odd after doubling, meaning that the field element
/// (after doubling) is larger than the underlying prime p that defines the
/// field, then a modular reduction must have been carried out, changing the parity that
/// should be even (since we multiplied by 2) to odd. In other words, we define
/// negative numbers to be those field elements that are larger than p/2.
pub fn alloc_is_negative<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    num: &Elt<F>,
) -> Result<Boolean, SynthesisError> {
    match num.clone().add::<CS>(num) {
        Elt::Constant(val) => Ok(Boolean::Constant(val.is_negative())),
        double => {
            let double_bits =
                elt_to_bits_le_strict(cs.namespace(|| "double num bits"), &double).unwrap();

            let lsb_2num = double_bits.get(0);
            let num_is_negative = lsb_2num.unwrap();

            Ok(num_is_negative.clone())
        }
    }
}

pub fn implies_popcount<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: CS,
    premise: &Boolean,
    sum: &Elt<F>,
    v: &[Boolean],
) {
    let popcount = v.iter().fold(Elt::zero(), |acc, bit| {
        acc.add::<CS>(&boolean_to_elt::<F, CS>(bit))
    });
    implies_equal(cs, premise, sum, &popcount);
}
