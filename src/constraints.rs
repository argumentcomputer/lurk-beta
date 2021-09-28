// Initially taken from: rust-fil-proofs/storage-proofs-core/src/gadgets/

use bellperson::{
    bls::Engine,
    gadgets::boolean::{AllocatedBit, Boolean},
    gadgets::num::AllocatedNum,
    ConstraintSystem, SynthesisError,
};

use ff::Field;

/// Adds a constraint to CS, enforcing an equality relationship between the allocated numbers a and b.
///
/// a == b
pub fn equal<E: Engine, A, AR, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    annotation: A,
    a: &AllocatedNum<E>,
    b: &AllocatedNum<E>,
) where
    A: FnOnce() -> AR,
    AR: Into<String>,
{
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
pub fn sum<E: Engine, A, AR, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    annotation: A,
    a: &AllocatedNum<E>,
    b: &AllocatedNum<E>,
    sum: &AllocatedNum<E>,
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

pub fn add<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    a: &AllocatedNum<E>,
    b: &AllocatedNum<E>,
) -> Result<AllocatedNum<E>, SynthesisError> {
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
pub fn difference<E: Engine, A, AR, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    annotation: A,
    a: &AllocatedNum<E>,
    b: &AllocatedNum<E>,
    difference: &AllocatedNum<E>,
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

pub fn sub<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    a: &AllocatedNum<E>,
    b: &AllocatedNum<E>,
) -> Result<AllocatedNum<E>, SynthesisError> {
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
pub fn product<E: Engine, A, AR, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    annotation: A,
    a: &AllocatedNum<E>,
    b: &AllocatedNum<E>,
    product: &AllocatedNum<E>,
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

pub fn mul<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    a: &AllocatedNum<E>,
    b: &AllocatedNum<E>,
) -> Result<AllocatedNum<E>, SynthesisError> {
    let res = AllocatedNum::alloc(cs.namespace(|| "mul_num"), || {
        let mut tmp = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        tmp.sub_assign(&b.get_value().ok_or(SynthesisError::AssignmentMissing)?);

        Ok(tmp)
    })?;

    // a * b = res
    product(&mut cs, || "multiplication constraint", a, b, &res);

    Ok(res)
}

/// Select the nth element of `from`, where `path_bits` represents n, least-significant bit first.
/// The returned result contains the selected element, and constraints are enforced.
/// `from.len()` must be a power of two.
pub fn select<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    from: &[AllocatedNum<E>],
    path_bits: &[Boolean],
) -> Result<AllocatedNum<E>, SynthesisError> {
    let pathlen = path_bits.len();
    assert_eq!(1 << pathlen, from.len());

    let mut state = Vec::new();
    for elt in from {
        state.push(elt.clone())
    }
    let mut half_size = from.len() / 2;

    // We reverse the path bits because the contained algorithm consumes most significant bit first.
    for (i, bit) in path_bits.iter().rev().enumerate() {
        let mut new_state = Vec::new();
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
pub fn pick<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    condition: &Boolean,
    a: &AllocatedNum<E>,
    b: &AllocatedNum<E>,
) -> Result<AllocatedNum<E>, SynthesisError>
where
    CS: ConstraintSystem<E>,
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
        |_| condition.lc(CS::one(), E::Fr::one()),
        |lc| lc + b.get_variable() - c.get_variable(),
    );

    Ok(c)
}

// This could now use alloc_is_zero to avoid duplication.
pub fn alloc_equal<CS: ConstraintSystem<E>, E: Engine>(
    mut cs: CS,
    a: &AllocatedNum<E>,
    b: &AllocatedNum<E>,
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
    let q = if let Some(inv) = diff.get_value().unwrap().inverse() {
        inv
    } else {
        E::Fr::one()
    };

    // (diff + result) * q = 1.
    // This enforces that diff and result are not both 0.
    cs.enforce(
        || "(diff + result) * q = 1",
        |lc| lc + diff.get_variable() + result.get_variable(),
        |_| Boolean::Constant(true).lc(CS::one(), q),
        |lc| lc + CS::one(),
    );

    // Taken together, these constraints enforce that exactly one of `diff` and `result` is 0.
    // Since result is constrained to be boolean, that means `result` is true iff `diff` is 0.
    // `Diff` is 0 iff `a == b`.
    // Therefore, `result = (a == b)`.

    Ok(Boolean::Is(result))
}

pub fn alloc_is_zero<CS: ConstraintSystem<E>, E: Engine>(
    mut cs: CS,
    x: &AllocatedNum<E>,
) -> Result<Boolean, SynthesisError> {
    let is_zero = x.get_value().unwrap() == E::Fr::zero();

    // result = (x == 0)
    let result = AllocatedBit::alloc(cs.namespace(|| "x = 0"), Some(is_zero))?;

    // result * x = 0
    // This means that at least one of result or x is zero.
    cs.enforce(
        || "result or x is 0",
        |lc| lc + result.get_variable(),
        |lc| lc + x.get_variable(),
        |lc| lc,
    );

    // Inverse of `x`, if it exists, otherwise one.
    let q = if let Some(inv) = x.get_value().unwrap().inverse() {
        inv
    } else {
        E::Fr::one()
    };

    // (x + result) * q = 1.
    // This enforces that x and result are not both 0.
    cs.enforce(
        || "(x + result) * q = 1",
        |lc| lc + x.get_variable() + result.get_variable(),
        |_| Boolean::Constant(true).lc(CS::one(), q),
        |lc| lc + CS::one(),
    );

    // Taken together, these constraints enforce that exactly one of `x` and `result` is 0.
    // Since result is constrained to be boolean, that means `result` is true iff `x` is 0.

    Ok(Boolean::Is(result))
}

fn enforce_implication<CS: ConstraintSystem<E>, E: Engine>(
    mut cs: CS,
    a: &Boolean,
    b: &Boolean,
) -> Result<(), SynthesisError> {
    let implication = implies(cs.namespace(|| "construct implication"), a, b)?;
    enforce_true(cs.namespace(|| "enforce implication"), &implication);
    Ok(())
}

fn enforce_true<CS: ConstraintSystem<E>, E: Engine>(cs: CS, prop: &Boolean) {
    Boolean::enforce_equal(cs, &Boolean::Constant(true), prop).unwrap(); // FIXME: unwrap
}

fn enforce_false<CS: ConstraintSystem<E>, E: Engine>(cs: CS, prop: &Boolean) {
    Boolean::enforce_equal(cs, &Boolean::Constant(false), prop).unwrap(); // FIXME: unwrap
}

// a => b
// not (a and (not b))
fn implies<CS: ConstraintSystem<E>, E: Engine>(
    cs: CS,
    a: &Boolean,
    b: &Boolean,
) -> Result<Boolean, SynthesisError> {
    Ok(Boolean::and(cs, a, &b.not())?.not())
}

fn or<CS: ConstraintSystem<E>, E: Engine>(
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

fn must_be_simple_bit(x: &Boolean) -> AllocatedBit {
    match x {
        Boolean::Constant(_) => panic!("Expected a non-constant Boolean."),
        Boolean::Is(b) => b.clone(),
        Boolean::Not(_) => panic!("Expected a non-negated Boolean."),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use bellperson::{
        bls::{Bls12, Fr},
        util_cs::test_cs::TestConstraintSystem,
    };
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use crate::TEST_SEED;

    #[test]
    fn add_constraint() {
        let rng = &mut XorShiftRng::from_seed(TEST_SEED);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Fr::random(rng)))
                .expect("alloc failed");
            let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Fr::random(rng)))
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
        let rng = &mut XorShiftRng::from_seed(TEST_SEED);

        for _ in 0..100 {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = AllocatedNum::alloc(cs.namespace(|| "a"), || Ok(Fr::random(rng)))
                .expect("alloc failed");
            let b = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(Fr::random(rng)))
                .expect("alloc failed");

            let res = sub(cs.namespace(|| "a-b"), &a, &b).expect("subtraction failed");

            let mut tmp = a.get_value().expect("get_value failed");
            tmp.sub_assign(&b.get_value().expect("get_value failed"));

            assert_eq!(res.get_value().expect("get_value failed"), tmp);
            assert!(cs.is_satisfied());
        }
    }
}
