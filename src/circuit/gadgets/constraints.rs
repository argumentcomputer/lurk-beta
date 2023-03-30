// Initially taken from: rust-fil-proofs/storage-proofs-core/src/gadgets/

use crate::field::LurkField;
use bellperson::LinearCombination;
use bellperson::{
    gadgets::{
        boolean::{AllocatedBit, Boolean},
        num::{AllocatedNum, Num},
    },
    ConstraintSystem, SynthesisError,
};
use ff::PrimeField;

/// Adds a constraint to CS, enforcing an equality relationship between the allocated numbers a and b.
///
/// a == b
pub fn enforce_equal<F: PrimeField, A, AR, CS: ConstraintSystem<F>>(
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
pub fn enforce_sum<F: PrimeField, A, AR, CS: ConstraintSystem<F>>(
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
    enforce_sum(&mut cs, || "sum constraint", a, b, &res);

    Ok(res)
}

/// Adds a constraint to CS, enforcing that the addition of the allocated numbers in vector `v`
/// is equal to `sum`.
///
/// summation(v) = sum
#[allow(dead_code)]
pub fn popcount<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    v: &[Boolean],
    sum: &AllocatedNum<F>,
) -> Result<(), SynthesisError> {
    let mut v_lc = LinearCombination::<F>::zero();
    for b in v {
        v_lc = add_to_lc::<F, CS>(b, v_lc, F::one())?;
    }

    // (summation(v)) * 1 = sum
    cs.enforce(
        || "popcount",
        |_| v_lc,
        |lc| lc + CS::one(),
        |lc| lc + sum.get_variable(),
    );

    Ok(())
}

pub fn add_to_lc<F: PrimeField, CS: ConstraintSystem<F>>(
    b: &Boolean,
    lc: LinearCombination<F>,
    scalar: F,
) -> Result<LinearCombination<F>, SynthesisError> {
    let mut v_lc = lc;
    match b {
        Boolean::Constant(c) => {
            if *c {
                v_lc = v_lc + (scalar, CS::one())
            } else {
                v_lc = v_lc + (F::zero(), CS::one())
            }
        }
        Boolean::Is(ref v) => v_lc = v_lc + (scalar, v.get_variable()),
        Boolean::Not(ref v) => v_lc = v_lc + (scalar, CS::one()) - (scalar, v.get_variable()),
    };

    Ok(v_lc)
}

// Enforce v is the bit decomposition of num, therefore we have that 0 <= num < 2ˆ(sizeof(v)).
pub fn enforce_pack<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    v: &[Boolean],
    num: &AllocatedNum<F>,
) -> Result<(), SynthesisError> {
    let mut coeff = F::one();

    let mut v_lc = LinearCombination::<F>::zero();
    for b in v {
        v_lc = add_to_lc::<F, CS>(b, v_lc, coeff)?;
        coeff = coeff.double();
    }

    cs.enforce(
        || "pack",
        |_| v_lc,
        |lc| lc + CS::one(),
        |lc| lc + num.get_variable(),
    );

    Ok(())
}

/// Adds a constraint to CS, enforcing a difference relationship between the allocated numbers a, b, and difference.
///
/// a - b = difference
pub fn enforce_difference<F: PrimeField, A, AR, CS: ConstraintSystem<F>>(
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
    enforce_difference(&mut cs, || "subtraction constraint", a, b, &res);

    Ok(res)
}

/// Adds a constraint to CS, enforcing a linear relationship between the
/// allocated numbers a, b, c and num.  Namely, the linear equation
/// a * b + c = num is enforced.
///
/// a * b = num - c
pub fn linear<F: PrimeField, A, AR, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    annotation: A,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
    c: &AllocatedNum<F>,
    num: &AllocatedNum<F>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
    // a * b = product
    cs.enforce(
        annotation,
        |lc| lc + a.get_variable(),
        |lc| lc + b.get_variable(),
        |lc| lc + num.get_variable() - c.get_variable(),
    );
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
                cs.namespace(|| format!("pick {i}, {j}")),
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

/// Takes two numbers (`a`, `b`) and returns `a` if the condition is true, and `b` otherwise.
pub fn pick_const<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    condition: &Boolean,
    a: F,
    b: F,
) -> Result<AllocatedNum<F>, SynthesisError>
where
    CS: ConstraintSystem<F>,
{
    let c = AllocatedNum::alloc(cs.namespace(|| "pick result"), || {
        if condition
            .get_value()
            .ok_or(SynthesisError::AssignmentMissing)?
        {
            Ok(a)
        } else {
            Ok(b)
        }
    })?;

    // Constrain (b - a) * condition = (b - c), ensuring c = a iff
    // condition is true, otherwise c = b.
    cs.enforce(
        || "pick",
        |lc| lc + (b, CS::one()) - (a, CS::one()),
        |_| condition.lc(CS::one(), F::one()),
        |lc| lc + (b, CS::one()) - c.get_variable(),
    );

    Ok(c)
}

/// Convert from Boolean to AllocatedNum
pub fn boolean_to_num<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    bit: &Boolean,
) -> Result<AllocatedNum<F>, SynthesisError>
where
    CS: ConstraintSystem<F>,
{
    let num = AllocatedNum::alloc(cs.namespace(|| "Allocate num"), || {
        if bit.get_value().ok_or(SynthesisError::AssignmentMissing)? {
            Ok(F::one())
        } else {
            Ok(F::zero())
        }
    })?;

    // Constrain (bit) * 1 = num, ensuring bit = num
    cs.enforce(
        || "Bit is equal to Num",
        |_| bit.lc(CS::one(), F::one()),
        |lc| lc + CS::one(),
        |lc| lc + num.get_variable(),
    );

    Ok(num)
}

// This could now use alloc_is_zero to avoid duplication.
pub fn alloc_equal<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) -> Result<Boolean, SynthesisError> {
    let equal = a.get_value().and_then(|x| b.get_value().map(|y| x == y));

    // Difference between `a` and `b`. This will be zero if `a` and `b` are equal.
    let diff = sub(cs.namespace(|| "a - b"), a, b)?;

    // result = (a == b)
    let result = AllocatedBit::alloc(cs.namespace(|| "a = b"), equal)?;

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
            let tmp0 = diff.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let tmp1 = tmp0.invert();

            if tmp1.is_some().into() {
                Ok(tmp1.unwrap())
            } else {
                Ok(F::one())
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

// Like `alloc_equal`, but with second argument a constant.
pub fn alloc_equal_const<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    a: &AllocatedNum<F>,
    b: F,
) -> Result<Boolean, SynthesisError> {
    let equal = a.get_value().map(|x| x == b);

    // Difference between `a` and `b`. This will be zero if `a` and `b` are equal.
    let diff = a.get_value().map(|x| x - b); //sub(cs.namespace(|| "a - b"), a, b)?;

    // result = (a == b)
    let result = AllocatedBit::alloc(cs.namespace(|| "a = b"), equal)?;

    // result * diff = 0
    // This means that at least one of result or diff is zero.
    cs.enforce(
        || "result or diff is 0",
        |lc| lc + result.get_variable(),
        |lc| lc + a.get_variable() - (b, CS::one()),
        |lc| lc,
    );

    // Inverse of `diff`, if it exists, otherwise one.
    let q = cs.alloc(
        || "q",
        || {
            let tmp0 = diff.ok_or(SynthesisError::AssignmentMissing)?;
            let tmp1 = tmp0.invert();

            if tmp1.is_some().into() {
                Ok(tmp1.unwrap())
            } else {
                Ok(F::one())
            }
        },
    )?;

    // ((a - b) + result) * q = 1.
    // This enforces that diff (a - b) and result are not both 0.
    cs.enforce(
        || "((a-b) + result) * q = 1",
        |lc| lc + a.get_variable() - (b, CS::one()) + result.get_variable(),
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
    cs: CS,
    x: &AllocatedNum<F>,
) -> Result<Boolean, SynthesisError> {
    alloc_num_is_zero(cs, Num::from(x.clone()))
}

pub fn alloc_num_is_zero<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    num: Num<F>,
) -> Result<Boolean, SynthesisError> {
    let num_value = num.get_value();
    let x = num_value.unwrap_or_else(|| F::zero());
    let is_zero = num_value.map(|n| n == F::zero());

    // result = (x == 0)
    let result = AllocatedBit::alloc(cs.namespace(|| "x = 0"), is_zero)?;

    // result * x = 0
    // This means that at least one of result or x is zero.
    cs.enforce(
        || "result or x is 0",
        |lc| lc + result.get_variable(),
        |_| num.lc(F::one()),
        |lc| lc,
    );

    // Inverse of `x`, if it exists, otherwise one.
    let q = cs.alloc(
        || "q",
        || {
            let tmp = x.invert();
            if tmp.is_some().into() {
                Ok(tmp.unwrap())
            } else {
                Ok(F::one())
            }
        },
    )?;

    // (x + result) * q = 1.
    // This enforces that x and result are not both 0.
    cs.enforce(
        || "(x + result) * q = 1",
        |_| num.lc(F::one()) + result.get_variable(),
        |lc| lc + q,
        |lc| lc + CS::one(),
    );

    // Taken together, these constraints enforce that exactly one of `x` and `result` is 0.
    // Since result is constrained to be boolean, that means `result` is true iff `x` is 0.

    Ok(Boolean::Is(result))
}

pub fn or_v<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    v: &[&Boolean],
) -> Result<Boolean, SynthesisError> {
    assert!(
        v.len() >= 4,
        "with less than 4 elements, or_v is more expensive than repeated or"
    );

    // Count the number of true values in v.
    let count_true = v.iter().fold(Num::zero(), |acc, b| {
        acc.add_bool_with_coeff(CS::one(), b, F::one())
    });

    // If the number of true values is zero, then none of the values is true.
    // Therefore, nor(v0, v1, ..., vn) is true.
    let nor = alloc_num_is_zero(&mut cs.namespace(|| "nor"), count_true)?;

    Ok(nor.not())
}

pub fn and_v<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    v: &[&Boolean],
) -> Result<Boolean, SynthesisError> {
    assert!(
        v.len() >= 4,
        "with less than 4 elements, and_v is more expensive than repeated and"
    );

    // Count the number of false values in v.
    let count_false = v.iter().fold(Num::zero(), |acc, b| {
        acc.add_bool_with_coeff(CS::one(), &b.not(), F::one())
    });

    // If the number of false values is zero, then all of the values are true.
    // Therefore, and(v0, v1, ..., vn) is true.
    let and = alloc_num_is_zero(&mut cs.namespace(|| "nor_of_nots"), count_false)?;

    Ok(and)
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

// Allocate Boolean for predicate "num is negative".
// We have that a number is defined to be negative if the parity bit (the
// least significant bit) is odd after doubling, meaning that the field element
// (after doubling) is larger than the underlying prime p that defines the
// field, then a modular reduction must have been carried out, changing the parity that
// should be even (since we multiplied by 2) to odd. In other words, we define
// negative numbers to be those field elements that are larger than p/2.
pub fn allocate_is_negative<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    num: &AllocatedNum<F>,
) -> Result<Boolean, SynthesisError> {
    let double_num = add(&mut cs.namespace(|| "double num"), num, num)?;
    let double_num_bits = double_num
        .to_bits_le_strict(&mut cs.namespace(|| "double num bits"))
        .unwrap();

    let lsb_2num = double_num_bits.get(0);
    let num_is_negative = lsb_2num.unwrap();

    Ok(num_is_negative.clone())
}

#[cfg(test)]
mod tests {
    use super::*;

    use bellperson::util_cs::test_cs::TestConstraintSystem;
    use blstrs::Scalar as Fr;
    use proptest::prelude::*;
    use std::ops::{AddAssign, SubAssign};

    use crate::field::FWrap;

    proptest! {

        #[test]
        fn prop_add_constraint((x, y) in any::<(FWrap<Fr>, FWrap<Fr>)>()) {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(x.0))
                .expect("alloc failed");
            let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(y.0))
                .expect("alloc failed");

            let res = add(cs.namespace(|| "a+b"), &a, &b).expect("add failed");

            let mut tmp = a.get_value().expect("get_value failed");
            tmp.add_assign(&b.get_value().expect("get_value failed"));

            assert_eq!(res.get_value().expect("get_value failed"), tmp);
            assert!(cs.is_satisfied());

        }

        #[test]
        fn prop_sub_constraint((x, y) in any::<(FWrap<Fr>, FWrap<Fr>)>()) {

               let mut cs = TestConstraintSystem::<Fr>::new();

            let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(x.0))
                .expect("alloc failed");
            let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(y.0))
                .expect("alloc failed");

            let res = sub(cs.namespace(|| "a-b"), &a, &b).expect("subtraction failed");

            let mut tmp = a.get_value().expect("get_value failed");
            tmp.sub_assign(&b.get_value().expect("get_value failed"));

            assert_eq!(res.get_value().expect("get_value failed"), tmp);
            assert!(cs.is_satisfied());

        }

        #[test]
        fn prop_alloc_equal_const((x, y) in any::<(FWrap<Fr>, FWrap<Fr>)>()) {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let a = AllocatedNum::alloc(&mut cs.namespace(|| "a"), || Ok(x.0)).unwrap();

            let equal =
                alloc_equal_const(&mut cs.namespace(|| "alloc_equal_const"), &a, x.0).unwrap();
            let equal2 =
                alloc_equal_const(&mut cs.namespace(|| "alloc_equal_const 2"), &a, y.0).unwrap();
            // a must always equal x.
            assert!(equal.get_value().unwrap());

            // a must equal y only if y happens to equal x (very unlikely!), otherwise a must *not* equal y.
            assert_eq!(equal2.get_value().unwrap(), x == y);
            assert!(cs.is_satisfied());
        }

        #[test]
        // needs to return Result because the macros use ?.
        fn test_and_or_v((x0, x1, x2, x3, x4) in any::<(bool, bool, bool, bool, bool)>()) {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let a = Boolean::Constant(x0);
            let b = Boolean::Constant(x1);
            let c = Boolean::Constant(x2);
            let d = Boolean::Constant(x3);
            let e = Boolean::Constant(x4);

            let and0 = and!(cs, &a, &b, &c).unwrap();
            let and1 = and!(cs, &a, &b, &c, &d).unwrap();
            let and2 = and!(cs, &a, &b, &c, &d, &e).unwrap();

            let or0 = or!(cs, &a, &b, &c).unwrap();
            let or1 = or!(cs, &a, &b, &c, &d).unwrap();
            let or2 = or!(cs, &a, &b, &c, &d, &e).unwrap();

            let expected_and0 = x0 && x1 && x2;
            let expected_and1 = x0 && x1 && x2 && x3;
            let expected_and2 = x0 && x1 && x2 && x3 && x4;

            let expected_or0 = x0 || x1 || x2;
            let expected_or1 = x0 || x1 || x2 || x3;
            let expected_or2 = x0 || x1 || x2 || x3 || x4;

            assert_eq!(expected_and0, and0.get_value().unwrap());
            assert_eq!(expected_and1, and1.get_value().unwrap());
            assert_eq!(expected_and2, and2.get_value().unwrap());
            assert_eq!(expected_or0, or0.get_value().unwrap());
            assert_eq!(expected_or1, or1.get_value().unwrap());
            assert_eq!(expected_or2, or2.get_value().unwrap());
            assert!(cs.is_satisfied());
        }
    }
}
