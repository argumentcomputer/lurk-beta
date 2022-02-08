// Initially taken from: rust-fil-proofs/storage-proofs-core/src/gadgets/

use bellperson::{
    gadgets::{
        boolean::{AllocatedBit, Boolean},
        num::AllocatedNum,
    },
    ConstraintSystem, SynthesisError,
};
use ff::PrimeField;

/// Adds a constraint to CS, enforcing an equality relationship between the allocated numbers a and b.
///
/// a == b
pub fn equal<F: PrimeField, A, AR, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    annotation: A,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    // debug_assert_eq!(a.get_value(), b.get_value());
    // a * 1 = b
    cs.enforce(
        annotation,
        |lc| lc + a.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + b.get_variable(),
    );
}

/// Adds a constraint to CS, enforcing a add relationship between the allocated numbers a, b, and sum.
///
/// a + b = sum
pub fn sum<F: PrimeField, A, AR, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    annotation: A,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
    sum: &AllocatedNum<F>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    // (a + b) * 1 = sum
    cs.enforce(
        annotation,
        |lc| lc + a.get_variable() + b.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + sum.get_variable(),
    );
}

pub fn add<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let res = AllocatedNum::alloc(cs.namespace(|| "add_num"), || {
        let mut tmp = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        tmp.add_assign(&b.get_value().ok_or(SynthesisError::AssignmentMissing)?);

        Ok(tmp)
    })?;

    // a + b = res
    sum(&mut cs, || "sum constraint", a, b, &res);

    Ok(res)
}

/// Adds a constraint to CS, enforcing a difference relationship between the allocated numbers a, b, and difference.
///
/// a - b = difference
pub fn difference<F: PrimeField, A, AR, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    annotation: A,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
    difference: &AllocatedNum<F>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    //    difference = a-b
    // => difference + b = a
    // => (difference + b) * 1 = a
    cs.enforce(
        annotation,
        |lc| lc + difference.get_variable() + b.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + a.get_variable(),
    );
}

pub fn sub<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let res = AllocatedNum::alloc(cs.namespace(|| "sub_num"), || {
        let mut tmp = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        tmp.sub_assign(&b.get_value().ok_or(SynthesisError::AssignmentMissing)?);

        Ok(tmp)
    })?;

    // a - b = res
    difference(&mut cs, || "subtraction constraint", a, b, &res);

    Ok(res)
}

/// Adds a constraint to CS, enforcing a product relationship between the allocated numbers a, b, and product.
///
/// a * b = product
pub fn product<F: PrimeField, A, AR, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    annotation: A,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
    product: &AllocatedNum<F>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    // a * b = product
    cs.enforce(
        annotation,
        |lc| lc + a.get_variable(),
        |lc| lc + b.get_variable(),
        |lc| lc + product.get_variable(),
    );
}

pub fn mul<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let res = AllocatedNum::alloc(cs.namespace(|| "mul_num"), || {
        let mut tmp = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        tmp.mul_assign(&b.get_value().ok_or(SynthesisError::AssignmentMissing)?);

        Ok(tmp)
    })?;

    // a * b = res
    product(&mut cs, || "multiplication constraint", a, b, &res);

    Ok(res)
}

pub fn div<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let res = AllocatedNum::alloc(cs.namespace(|| "div_num"), || {
        let mut tmp = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        let inv = (b.get_value().ok_or(SynthesisError::AssignmentMissing)?).invert();

        if inv.is_some().into() {
            inv.map(|i| tmp.mul_assign(i));
            Ok(tmp)
        } else {
            Err(SynthesisError::DivisionByZero)
        }
    })?;

    // a = b * res
    product(&mut cs, || "division constraint", &res, b, a);

    Ok(res)
}

/// Select the nth element of `from`, where `path_bits` represents n, least-significant bit first.
/// The returned result contains the selected element, and constraints are enforced.
/// `from.len()` must be a power of two.
#[allow(dead_code)]
pub fn select<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    from: &[AllocatedNum<F>],
    path_bits: &[Boolean],
) -> Result<AllocatedNum<F>, SynthesisError> {
    let pathlen = path_bits.len();
    assert_eq!(1 << pathlen, from.len());

    let mut state = from.to_vec();
    let mut half_size = from.len() / 2;

    // We reverse the path bits because the contained algorithm consumes most significant bit first.
    for (i, bit) in path_bits.iter().rev().enumerate() {
        let mut new_state = Vec::with_capacity(half_size);
        for j in 0..half_size {
            new_state.push(pick(
                cs.namespace(|| format!("pick {}, {}", i, j)),
                bit,
                &state[half_size + j],
                &state[j],
            )?);
        }
        state = new_state;
        half_size /= 2;
    }

    Ok(state.remove(0))
}

/// Takes two allocated numbers (`a`, `b`) and returns `a` if the condition is true, and `b` otherwise.
pub fn pick<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    condition: &Boolean,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError>
where
    CS: ConstraintSystem<F>,
{
    let c = AllocatedNum::alloc(cs.namespace(|| "pick result"), || {
        if condition
            .get_value()
            .ok_or(SynthesisError::AssignmentMissing)?
        {
            Ok(a.get_value().ok_or(SynthesisError::AssignmentMissing)?)
        } else {
            Ok(b.get_value().ok_or(SynthesisError::AssignmentMissing)?)
        }
    })?;

    // Constrain (b - a) * condition = (b - c), ensuring c = a iff
    // condition is true, otherwise c = b.
    cs.enforce(
        || "pick",
        |lc| lc + b.get_variable() - a.get_variable(),
        |_| condition.lc(CS::one(), F::one()),
        |lc| lc + b.get_variable() - c.get_variable(),
    );

    Ok(c)
}

// This could now use alloc_is_zero to avoid duplication.
pub fn alloc_equal<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) -> Result<Boolean, SynthesisError> {
    let equal = a.get_value() == b.get_value();

    // Difference between `a` and `b`. This will be zero if `a` and `b` are equal.
    let diff = sub(cs.namespace(|| "a - b"), a, b)?;

    // result = (a == b)
    let result = AllocatedBit::alloc(cs.namespace(|| "a = b"), Some(equal))?;

    // result * diff = 0
    // This means that at least one of result or diff is zero.
    cs.enforce(
        || "result or diff is 0",
        |lc| lc + result.get_variable(),
        |lc| lc + diff.get_variable(),
        |lc| lc,
    );

    // Inverse of `diff`, if it exists, otherwise one.
    let q = cs.alloc(
        || "q",
        || {
            if let Some(tmp0) = diff.get_value() {
                let tmp1 = tmp0.invert();
                if tmp1.is_some().into() {
                    Ok(tmp1.unwrap())
                } else {
                    Ok(F::one())
                }
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        },
    )?;

    // (diff + result) * q = 1.
    // This enforces that diff and result are not both 0.
    cs.enforce(
        || "(diff + result) * q = 1",
        |lc| lc + diff.get_variable() + result.get_variable(),
        |lc| lc + q,
        |lc| lc + CS::one(),
    );

    // Taken together, these constraints enforce that exactly one of `diff` and `result` is 0.
    // Since result is constrained to be boolean, that means `result` is true iff `diff` is 0.
    // `Diff` is 0 iff `a == b`.
    // Therefore, `result = (a == b)`.

    Ok(Boolean::Is(result))
}

pub fn alloc_is_zero<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    x: &AllocatedNum<F>,
) -> Result<Boolean, SynthesisError> {
    let is_zero = x.get_value().map(|x| x == F::zero());

    // result = (x == 0)
    let result = AllocatedBit::alloc(cs.namespace(|| "x = 0"), is_zero)?;

    // result * x = 0
    // This means that at least one of result or x is zero.
    cs.enforce(
        || "result or x is 0",
        |lc| lc + result.get_variable(),
        |lc| lc + x.get_variable(),
        |lc| lc,
    );

    // Inverse of `x`, if it exists, otherwise one.
    let q = cs.alloc(
        || "q",
        || {
            if let Some(tmp0) = x.get_value() {
                let tmp1 = tmp0.invert();
                if tmp1.is_some().into() {
                    Ok(tmp1.unwrap())
                } else {
                    Ok(F::one())
                }
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        },
    )?;

    // (x + result) * q = 1.
    // This enforces that x and result are not both 0.
    cs.enforce(
        || "(x + result) * q = 1",
        |lc| lc + x.get_variable() + result.get_variable(),
        |lc| lc + q,
        |lc| lc + CS::one(),
    );

    // Taken together, these constraints enforce that exactly one of `x` and `result` is 0.
    // Since result is constrained to be boolean, that means `result` is true iff `x` is 0.

    Ok(Boolean::Is(result))
}

pub fn enforce_implication<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    a: &Boolean,
    b: &Boolean,
) -> Result<(), SynthesisError> {
    let implication = implies(cs.namespace(|| "construct implication"), a, b)?;
    enforce_true(cs.namespace(|| "enforce implication"), &implication)?;
    Ok(())
}

pub fn enforce_true<CS: ConstraintSystem<F>, F: PrimeField>(
    cs: CS,
    prop: &Boolean,
) -> Result<(), SynthesisError> {
    // if let Some(val) = prop.get_value() {
    //     debug_assert!(val);
    // }
    Boolean::enforce_equal(cs, &Boolean::Constant(true), prop)
}

#[allow(dead_code)]
pub fn enforce_false<CS: ConstraintSystem<F>, F: PrimeField>(
    cs: CS,
    prop: &Boolean,
) -> Result<(), SynthesisError> {
    Boolean::enforce_equal(cs, &Boolean::Constant(false), prop)
}

// a => b
// not (a and (not b))
pub fn implies<CS: ConstraintSystem<F>, F: PrimeField>(
    cs: CS,
    a: &Boolean,
    b: &Boolean,
) -> Result<Boolean, SynthesisError> {
    Ok(Boolean::and(cs, a, &b.not())?.not())
}

pub fn or<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    a: &Boolean,
    b: &Boolean,
) -> Result<Boolean, SynthesisError> {
    Ok(Boolean::not(&Boolean::and(
        cs.namespace(|| "not and (not a) (not b)"),
        &Boolean::not(a),
        &Boolean::not(b),
    )?))
}

#[allow(dead_code)]
pub fn must_be_simple_bit(x: &Boolean) -> AllocatedBit {
    match x {
        Boolean::Constant(_) => panic!("Expected a non-constant Boolean."),
        Boolean::Is(b) => b.clone(),
        Boolean::Not(_) => panic!("Expected a non-negated Boolean."),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use bellperson::util_cs::test_cs::TestConstraintSystem;
    use blstrs::Scalar as Fr;
    use ff::Field;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;
    use std::ops::{AddAssign, SubAssign};

    use crate::TEST_SEED;

    #[test]
    fn add_constraint() {
        let mut rng = &mut XorShiftRng::from_seed(TEST_SEED);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Fr::random(&mut rng)))
                .expect("alloc failed");
            let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Fr::random(&mut rng)))
                .expect("alloc failed");

            let res = add(cs.namespace(|| "a+b"), &a, &b).expect("add failed");

            let mut tmp = a.get_value().expect("get_value failed");
            tmp.add_assign(&b.get_value().expect("get_value failed"));

            assert_eq!(res.get_value().expect("get_value failed"), tmp);
            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn sub_constraint() {
        let mut rng = &mut XorShiftRng::from_seed(TEST_SEED);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Fr::random(&mut rng)))
                .expect("alloc failed");
            let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Fr::random(&mut rng)))
                .expect("alloc failed");

            let res = sub(cs.namespace(|| "a-b"), &a, &b).expect("subtraction failed");

            let mut tmp = a.get_value().expect("get_value failed");
            tmp.sub_assign(&b.get_value().expect("get_value failed"));

            assert_eq!(res.get_value().expect("get_value failed"), tmp);
            assert!(cs.is_satisfied());
        }
    }
}
