// Initially taken from: rust-fil-proofs/storage-proofs-core/src/gadgets/

use crate::circuit::add_clause_single;
use crate::circuit::gadgets::case::multi_case_aux;
use crate::circuit::gadgets::case::CaseClause;
use crate::circuit::gadgets::data::GlobalAllocations;
use crate::circuit::gadgets::pointer::AllocatedPtr;
use crate::field::LurkField;
use crate::store::ScalarPointer;
use crate::store::{Op2, Tag};
use crate::store::Store;
use bellperson::LinearCombination;
use bellperson::{
    gadgets::{
        boolean::{AllocatedBit, Boolean},
        num::AllocatedNum,
    },
    ConstraintSystem, SynthesisError,
};
use ff::PrimeField;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::FromPrimitive;

#[derive(Default)]
struct CompResults<'a, F: LurkField> {
    same_sign: Vec<CaseClause<'a, F>>,
    a_neg_and_b_not_neg: Vec<CaseClause<'a, F>>,
    a_not_neg_and_b_neg: Vec<CaseClause<'a, F>>,
}
impl<'a, F: LurkField> CompResults<'a, F> {
    fn add_clauses_comp(
        &mut self,
        key: F,
        result_same_sign: &'a AllocatedNum<F>,
        result_a_neg_and_b_not_neg: &'a AllocatedNum<F>,
        result_a_not_neg_and_b_neg: &'a AllocatedNum<F>,
    ) {
        add_clause_single(&mut self.same_sign, key, result_same_sign);
        add_clause_single(
            &mut self.a_neg_and_b_not_neg,
            key,
            result_a_neg_and_b_not_neg,
        );
        add_clause_single(
            &mut self.a_not_neg_and_b_neg,
            key,
            result_a_not_neg_and_b_neg,
        );
    }
}

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

/// Adds a constraint to CS, enforcing that the addition of the allocated numbers in vector `v` is equal to `sum`.
///
/// summation(v) = sum
pub fn boolean_summation<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    v: &Vec<Boolean>,
    sum: &AllocatedNum<F>,
) {
    let v_lc = LinearCombination::<F>::zero();
    for i in 0..v.len() {
        match v[i] {
            Boolean::Constant(c) => {
                if c {
                    v_lc.clone() + (F::one(), CS::one())
                } else {
                    v_lc.clone()
                }
            }
            Boolean::Is(ref v) => v_lc.clone() + (F::one(), v.get_variable()),
            Boolean::Not(ref v) => {
                v_lc.clone() + (F::one(), CS::one()) - (F::one(), v.get_variable())
            }
        };
    }

    // (summation(v)) * 1 = sum
    cs.enforce(
        || "boolean summation",
        |_| v_lc,
        |lc| lc + CS::one(),
        |lc| lc + sum.get_variable(),
    );
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
            let tmp0 = x.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            let tmp1 = tmp0.invert();
            if tmp1.is_some().into() {
                Ok(tmp1.unwrap())
            } else {
                Ok(F::one())
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

// This function helps to enforce a  comparison relation between a and b.
// It receives as input argument `diff`, which must be constrained to be
// equal to the difference (a - b).
// The last argument is `op2`, which can be <, <=, >, >=
pub fn comparison_helper<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
    diff: &AllocatedNum<F>,
    op2: &AllocatedNum<F>,
) -> Result<(Boolean, AllocatedPtr<F>, Boolean), SynthesisError> {
    let a_is_negative = allocate_is_negative(&mut cs.namespace(|| "enforce a is negative"), a)?;
    let b_is_negative = allocate_is_negative(&mut cs.namespace(|| "enforce b is negative"), b)?;
    let diff_is_negative =
        allocate_is_negative(&mut cs.namespace(|| "enforce diff is negative"), diff)?;

    let diff_is_zero = alloc_is_zero(&mut cs.namespace(|| "diff is zero"), diff)?;

    let diff_is_not_positive = or(
        &mut cs.namespace(|| "diff is not positive"),
        &diff_is_negative,
        &diff_is_zero,
    )?;

    let diff_is_positive = diff_is_not_positive.not();

    let diff_is_not_negative = diff_is_negative.not();

    let not_one_negative_and_other_not_negative = Boolean::xor(
        &mut cs.namespace(|| "not one negative and other not negative"),
        &a_is_negative,
        &b_is_negative,
    )?
    .not();

    let a_negative_and_b_not_negative = Boolean::and(
        &mut cs.namespace(|| "a negative and b not negative"),
        &a_is_negative,
        &b_is_negative.not(),
    )?;

    let alloc_num_diff_is_negative = boolean_to_num(
        &mut cs.namespace(|| "Allocate num for diff_is_negative"),
        &diff_is_negative,
    )?;

    let alloc_num_diff_is_not_positive = boolean_to_num(
        &mut cs.namespace(|| "Allocate num for diff_is_not_positive"),
        &diff_is_not_positive,
    )?;

    let alloc_num_diff_is_positive = boolean_to_num(
        &mut cs.namespace(|| "Allocate num for diff_is_positive"),
        &diff_is_positive,
    )?;

    let alloc_num_diff_is_not_negative = boolean_to_num(
        &mut cs.namespace(|| "Allocate num for diff_is_not_negative"),
        &diff_is_not_negative,
    )?;

    let mut comp_results = CompResults::default();
    comp_results.add_clauses_comp(
        Op2::Less.as_field(),
        &alloc_num_diff_is_negative,
        &g.true_num,
        &g.false_num,
    );
    comp_results.add_clauses_comp(
        Op2::LessEqual.as_field(),
        &alloc_num_diff_is_not_positive,
        &g.true_num,
        &g.false_num,
    );
    comp_results.add_clauses_comp(
        Op2::Greater.as_field(),
        &alloc_num_diff_is_positive,
        &g.false_num,
        &g.true_num,
    );
    comp_results.add_clauses_comp(
        Op2::GreaterEqual.as_field(),
        &alloc_num_diff_is_not_negative,
        &g.false_num,
        &g.true_num,
    );

    let comparison_defaults = [&g.default_num, &g.default_num, &g.default_num];

    let comp_clauses = [
        &comp_results.same_sign[..],
        &comp_results.a_neg_and_b_not_neg[..],
        &comp_results.a_not_neg_and_b_neg[..],
    ];

    let comparison_result = multi_case_aux(
        &mut cs.namespace(|| "comparison multicase results"),
        op2,
        &comp_clauses,
        &comparison_defaults,
        g,
    )?;

    let comp_val_same_sign_num = comparison_result.0[0].clone();
    let comp_val_a_neg_and_b_not_neg_num = comparison_result.0[1].clone();
    let comp_val_a_not_neg_and_b_neg_num = comparison_result.0[2].clone();
    let is_comparison_tag = comparison_result.1.not();

    let comp_val1 = pick(
        &mut cs.namespace(|| "comp_val1"),
        &a_negative_and_b_not_negative,
        &comp_val_a_neg_and_b_not_neg_num,
        &comp_val_a_not_neg_and_b_neg_num,
    )?;
    let comp_val2 = pick(
        &mut cs.namespace(|| "comp_val2"),
        &not_one_negative_and_other_not_negative,
        &comp_val_same_sign_num,
        &comp_val1,
    )?;

    let comp_val_is_zero = alloc_is_zero(&mut cs.namespace(|| "comp_val_is_zero"), &comp_val2)?;

    let comp_val = AllocatedPtr::pick(
        &mut cs.namespace(|| "comp_val"),
        &comp_val_is_zero,
        &g.nil_ptr,
        &g.t_ptr,
    )?;

    Ok((is_comparison_tag, comp_val, diff_is_negative))
}

// Enforce 0 <= num < 2ˆn.
pub fn enforce_at_most_n_bits<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    num: AllocatedNum<F>,
    n: usize,
) -> Result<(), SynthesisError> {
    let num_bits = num.to_bits_le(&mut cs.namespace(|| "u64 remainder bit decomp"))?;
    let v = num_bits[n..255].to_vec();
    boolean_summation(&mut cs.namespace(|| "add all MSBs"), &v, &g.false_num);
    Ok(())
}

// Enforce div and mod operation for U64. We need to show that
// arg1 = q * arg2 + r, such that 0 <= r < arg2.
pub fn enforce_u64_div_mod<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    cond: Boolean,
    arg1: &AllocatedPtr<F>,
    arg2: &AllocatedPtr<F>,
    store: &Store<F>,
) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>), SynthesisError> {
    let arg1_u64 = match arg1.hash().get_value() {
        Some(v) => v.to_u64_unchecked(),
        None => 0, // Blank and Dummy
    };
    let arg2_u64 = match arg2.hash().get_value() {
        Some(v) => v.to_u64_unchecked(),
        None => 0, // Blank and Dummy
    };

    let (q, r) = if arg2_u64 != 0 {
        (arg1_u64 / arg2_u64, arg1_u64 % arg2_u64)
    } else {
        (0, 0)
    };

    let r_ptr = store.get_u64(r);
    let alloc_r =
        AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "u64 remainder"), store, || Ok(&r_ptr))?;

    let q_ptr = store.get_u64(q);
    let alloc_q =
        AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "u64 quotient"), store, || Ok(&q_ptr))?;

    let arg1_u64_ptr = store.get_u64(arg1_u64);
    let alloc_arg1 = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "alloc arg1"), store, || {
        Ok(&arg1_u64_ptr)
    })?;

    let arg2_u64_ptr = store.get_u64(arg2_u64);
    let alloc_arg2 = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "alloc arg2"), store, || {
        Ok(&arg2_u64_ptr)
    })?;

    // a = b * q + r
    let product_u64mod = mul(
        &mut cs.namespace(|| "product(q,arg2)"),
        alloc_q.hash(),
        alloc_arg2.hash(),
    )?;
    let sum_u64mod = add(
        &mut cs.namespace(|| "sum remainder mod u64"),
        &product_u64mod,
        alloc_r.hash(),
    )?;
    let u64mod_decomp = alloc_equal(
        &mut cs.namespace(|| "check u64 mod decomposition"),
        &sum_u64mod,
        alloc_arg1.hash(),
    )?;
    let b_is_zero = alloc_is_zero(&mut cs.namespace(|| "b is zero"), arg2.hash())?;
    let b_is_not_zero_and_cond = Boolean::and(
        &mut cs.namespace(|| "b is not zero and cond"),
        &b_is_zero.not(),
        &cond,
    )?;
    enforce_implication(
        &mut cs.namespace(|| "enforce u64 mod decomposition"),
        &b_is_not_zero_and_cond,
        &u64mod_decomp,
    )?;

    enforce_less_than_bound(
        &mut cs.namespace(|| "remainder in range b"),
        cond,
        alloc_r.clone(),
        alloc_arg2.clone(),
    )?;

    let arg1_u64_tag = alloc_equal(
        &mut cs.namespace(|| "arg1 u64 tag"),
        alloc_arg1.tag(),
        &g.u64_tag,
    )?;
    let arg2_u64_tag = alloc_equal(
        &mut cs.namespace(|| "arg2 u64 tag"),
        alloc_arg2.tag(),
        &g.u64_tag,
    )?;
    enforce_true(&mut cs.namespace(|| "check arg1 u64 tag"), &arg1_u64_tag)?;
    enforce_true(&mut cs.namespace(|| "check arg2 u64 tag"), &arg2_u64_tag)?;

    Ok((alloc_q, alloc_r))
}

// Enforce the num < bound. This is done by proving (bound - num) is positive.
// `num` and `bound` must be a positive field element.
pub fn enforce_less_than_bound<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    cond: Boolean,
    num: AllocatedPtr<F>,
    bound: AllocatedPtr<F>,
) -> Result<(), SynthesisError> {
    let diff_bound_num = sub(
        &mut cs.namespace(|| "bound minus num"),
        bound.hash(),
        num.hash(),
    )?;

    let diff_bound_num_is_negative = allocate_is_negative(
        &mut cs.namespace(|| "diff bound num is negative"),
        &diff_bound_num,
    )?;

    enforce_implication(
        &mut cs.namespace(|| "enforce u64 range"),
        &cond,
        &diff_bound_num_is_negative.not(),
    )
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

// ATTENTION:
// Convert from bn to num. This allocation is NOT constrained here.
// In the circuit we use it to prove u64 decomposition, since using bn
// we have division with remainder, which is used to find the quotient
// after dividing by 2ˆ64. Therefore we constrain this relation afterwards.
pub fn allocate_unconstrained_bignum<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    bn: BigUint,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let bytes_le = bn.to_bytes_le();
    let mut bytes_padded = [0u8; 32];
    bytes_padded[0..bytes_le.len()].copy_from_slice(&bytes_le);
    let ff = F::from_bytes(&bytes_padded).unwrap();
    let num = AllocatedNum::alloc(&mut cs.namespace(|| "num"), || Ok(ff)).unwrap();
    Ok(num)
}

// Convert from num to u64.
pub fn u64_op<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    maybe_u64: &AllocatedPtr<F>,
    store: &Store<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    /*let p64_bn = match g.power2_64_num.get_value() {
        Some(v) => BigUint::from_bytes_le(v.to_repr().as_ref()),
        // Since it is will be in the denominator, it can't be zero
        None => BigUint::one(), // blank and dummy
    };*/
    let p64_bn = BigUint::pow(&BigUint::from_u32(2).unwrap(), 64);
    let v = match maybe_u64.hash().get_value() {
        Some(v) => v,
        None => F::zero(),
    };
    let u64_ptr = store.get_u64(v.to_u64_unchecked());
    let field_bn = BigUint::from_bytes_le(v.to_repr().as_ref());

    let (q_bn, r_bn) = field_bn.div_rem(&p64_bn);

    let q_num = allocate_unconstrained_bignum(&mut cs.namespace(|| "q"), q_bn)?;
    let r_num = allocate_unconstrained_bignum(&mut cs.namespace(|| "r"), r_bn)?;
    //let p64_num = allocate_unconstrained_bignum(&mut cs.namespace(|| "p64"), p64_bn)?;
    //let p64_num = g.power2_64_num;

    // a = b.q + r
    let product = mul(
        &mut cs.namespace(|| "product(q,pow(2,64))"),
        &q_num,
        &g.power2_64_num,
    )?;
    let sum = add(&mut cs.namespace(|| "sum remainder"), &product, &r_num)?;
    let u64_decomp = alloc_equal(
        &mut cs.namespace(|| "check u64 decomposition"),
        &sum,
        maybe_u64.hash(),
    )?;
    enforce_true(
        &mut cs.namespace(|| "enforce u64 decomposition"),
        &u64_decomp,
    )?;

    // enforce remainder range
    enforce_at_most_n_bits(
        &mut cs.namespace(|| "remainder u64 range"),
        g,
        r_num.clone(),
        64,
    )?;

    let output = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "u64_op"), store, || Ok(&u64_ptr))?;
    let u64_is_remainder = alloc_equal(
        &mut cs.namespace(|| "check u64 value is the remainder"),
        &r_num,
        output.hash(),
    )?;
    enforce_true(
        &mut cs.namespace(|| "enforce u64 decomposition output"),
        &u64_is_remainder,
    )?;
    Ok(output)
}

pub fn hide<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    secret: &AllocatedNum<F>,
    maybe_payload: &AllocatedPtr<F>,
    store: &Store<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    AllocatedPtr::construct_commitment(
        &mut cs.namespace(|| "commitment hash"),
        g,
        store,
        secret,
        maybe_payload,
    )
}

pub fn num<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    maybe_num: &AllocatedPtr<F>,
    store: &Store<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let num_ptr = if let Some(ptr) = maybe_num.ptr(store).as_ref() {
        let scalar_ptr = store.get_expr_hash(ptr).expect("expr hash missing");
        match store.get_num(crate::Num::Scalar::<F>(*scalar_ptr.value())) {
            Some(n) => n,
            None => store.get_nil(),
        }
    } else {
        store.get_nil()
    };
    AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "num"), store, || Ok(&num_ptr))
}

pub fn comm<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    maybe_comm: &AllocatedPtr<F>,
    store: &Store<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let hash = match maybe_comm.hash().get_value() {
        Some(h) => h,
        None => F::zero(), // dummy value
    };
    let comm_ptr = match store.get_maybe_opaque(Tag::Comm, hash) {
        Some(c) => c,
        None => store.get_nil(),
    };
    AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "open"), store, || Ok(&comm_ptr))
}

pub fn char_op<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    maybe_char: &AllocatedPtr<F>,
    store: &Store<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let char_ptr = if let Some(ptr) = maybe_char.ptr(store).as_ref() {
        let scalar_ptr = store.get_expr_hash(ptr).expect("expr hash missing");
        match scalar_ptr.value().to_u32() {
            Some(n) => store.get_char(char::from_u32(n).unwrap()),
            None => store.get_nil(),
        }
    } else {
        store.get_nil()
    };
    AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "char_op"), store, || Ok(&char_ptr))
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

    #[test]
    fn test_enforce_less_than_bound_corner_case() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let most_positive = crate::Num::<Fr>::most_positive();
        let most_positive_ptr = s.num(most_positive);
        let alloc_most_positive =
            AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "most positive"), s, || {
                Ok(&most_positive_ptr)
            })
            .unwrap();
        let num = s.num(42);
        let alloc_num =
            AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "num"), s, || Ok(&num)).unwrap();
        let cond = Boolean::Constant(true);

        let res = enforce_less_than_bound(
            &mut cs.namespace(|| "enforce less than bound"),
            cond,
            alloc_num,
            alloc_most_positive,
        );
        assert!(res.is_ok());
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_enforce_less_than_bound() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        let num = s.num(42);
        let alloc_num =
            AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "num"), s, || Ok(&num)).unwrap();
        let bound = s.num(43);
        let alloc_bound =
            AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "bound"), s, || Ok(&bound)).unwrap();
        let cond = Boolean::Constant(true);

        let res = enforce_less_than_bound(
            &mut cs.namespace(|| "enforce less than bound"),
            cond,
            alloc_num,
            alloc_bound,
        );
        assert!(res.is_ok());
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_enforce_less_than_bound_negative() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        let num = s.num(43);
        let alloc_num =
            AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "num"), s, || Ok(&num)).unwrap();
        let bound = s.num(42);
        let alloc_bound =
            AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "bound"), s, || Ok(&bound)).unwrap();
        let cond = Boolean::Constant(true);

        let res = enforce_less_than_bound(
            &mut cs.namespace(|| "enforce less than bound"),
            cond,
            alloc_num,
            alloc_bound,
        );
        assert!(res.is_ok());
        assert!(!cs.is_satisfied());
    }

    #[test]
    fn test_enforce_n_bits() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();

        let num = crate::Num::<Fr>::Scalar(Fr::from_u64(42).unwrap()); // 42 = 101010
        let alloc_num =
            AllocatedNum::alloc(&mut cs.namespace(|| "num"), || Ok(num.into_scalar())).unwrap();

        let res = enforce_at_most_n_bits(
            &mut cs.namespace(|| "enforce at most n bits"),
            &g,
            alloc_num,
            6,
        );
        assert!(res.is_ok());
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_enforce_n_bits_negative() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();

        let num = crate::Num::<Fr>::Scalar(Fr::from_u64(42).unwrap()); // 42 = 101010
        let alloc_num =
            AllocatedNum::alloc(&mut cs.namespace(|| "num"), || Ok(num.into_scalar())).unwrap();

        let res = enforce_at_most_n_bits(
            &mut cs.namespace(|| "enforce at most n bits"),
            &g,
            alloc_num,
            5,
        );
        assert!(res.is_ok());
        assert!(!cs.is_satisfied());
    }

    #[test]
    fn test_enforce_u64_div_mod() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();

        let a = s.num(42);
        let alloc_a = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "a"), s, || Ok(&a)).unwrap();
        let b = s.num(5);
        let alloc_b = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "b"), s, || Ok(&b)).unwrap();

        let cond = Boolean::Constant(true);

        let (q, r) = enforce_u64_div_mod(
            &mut cs.namespace(|| "enforce u64 div mod"),
            &g,
            cond,
            &alloc_a,
            &alloc_b,
            s,
        )
        .unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(q.hash().get_value(), Fr::from_u64(8));
        assert_eq!(r.hash().get_value(), Fr::from_u64(2));
    }

    #[test]
    fn test_enforce_u64_div_mod_zero() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();

        let a = s.num(42);
        let alloc_a = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "a"), s, || Ok(&a)).unwrap();
        let b = s.num(0);
        let alloc_b = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "b"), s, || Ok(&b)).unwrap();

        let cond = Boolean::Constant(true);

        let (q, r) = enforce_u64_div_mod(
            &mut cs.namespace(|| "enforce u64 div mod"),
            &g,
            cond,
            &alloc_a,
            &alloc_b,
            s,
        )
        .unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(q.hash().get_value(), Fr::from_u64(0));
        assert_eq!(r.hash().get_value(), Fr::from_u64(0));
    }

    #[test]
    fn test_u64_op() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();

        let a = s.num(42);
        let alloc_a = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "a"), s, || Ok(&a)).unwrap();

        let a_u64 = u64_op(&mut cs.namespace(|| "u64 op"), &g, &alloc_a, s).unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(a_u64.hash().get_value(), Fr::from_u64(42));
    }

    #[test]
    fn test_u64_op_coercion() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();
        let alloc_pow2_64 = AllocatedPtr::from_parts(&g.num_tag, &g.power2_64_num);

        let a_u64 = u64_op(&mut cs.namespace(|| "u64 op"), &g, &alloc_pow2_64, s).unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(a_u64.hash().get_value(), Fr::from_u64(0));
    }

    #[test]
    fn test_enforce_comparison() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();

        let a = s.num(42);
        let alloc_a = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "a"), s, || Ok(&a)).unwrap();
        let b = s.num(43);
        let alloc_b = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "b"), s, || Ok(&b)).unwrap();
        let diff = sub(&mut cs.namespace(|| "sub"), alloc_a.hash(), alloc_b.hash()).unwrap();

        let (_, comp_val, _) = comparison_helper(
            &mut cs.namespace(|| "enforce u64 div mod"),
            &g,
            &alloc_a.hash(),
            &alloc_b.hash(),
            &diff,
            &g.op2_less_tag,
        )
        .unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(comp_val.hash().get_value(), g.t_ptr.hash().get_value());
    }

    #[test]
    fn test_enforce_boolean_summation() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let a = s.num(42);
        let alloc_a = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "a"), s, || Ok(&a)).unwrap();
        let bits = alloc_a
            .hash()
            .to_bits_le(&mut cs.namespace(|| "bits"))
            .unwrap();
        let popcount = s.num(3);
        let alloc_popcount =
            AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "popcount"), s, || Ok(&popcount)).unwrap();

        boolean_summation(
            &mut cs.namespace(|| "boolean summation"),
            &bits,
            &alloc_popcount.hash(),
        );
        assert!(cs.is_satisfied());
    }
}
