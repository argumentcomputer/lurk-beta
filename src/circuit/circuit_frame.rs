use std::fmt::Debug;
use std::marker::PhantomData;

use bellpepper::util_cs::Comparable;
use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};

use crate::{
    circuit::gadgets::{
        data::GlobalAllocations,
        pointer::AllocatedPtr,
    },
    field::LurkField,
    hash_witness::ConsName,
};

use super::gadgets::constraints::{
    self, alloc_equal, alloc_is_zero, enforce_implication, or, sub,
};
use crate::circuit::circuit_frame::constraints::{
    allocate_is_negative, boolean_to_num, enforce_pack, enforce_product_and_sum, mul,
};
use crate::circuit::gadgets::hashes::AllocatedConsWitness;
use crate::coprocessor::Coprocessor;
use crate::eval::{Witness, IO};
use crate::lurk_sym_ptr;
use crate::store::Store;

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::FromPrimitive;

#[derive(Clone, Copy, Debug)]
pub struct CircuitFrame<'a, F: LurkField, C: Coprocessor<F>> {
    pub store: Option<&'a Store<F>>,
    pub input: Option<IO<F>>,
    pub output: Option<IO<F>>,
    pub witness: Option<Witness<F>>,
    _p: PhantomData<C>,
}

impl<'a, F: LurkField, C: Coprocessor<F>> CircuitFrame<'a, F, C> {
    pub fn blank() -> Self {
        Self {
            store: None,
            input: None,
            output: None,
            witness: None,
            _p: Default::default(),
        }
    }
}

impl<F: LurkField, C: Coprocessor<F>> CircuitFrame<'_, F, C> {
    pub fn precedes(&self, maybe_next: &Self) -> bool {
        self.output == maybe_next.input
    }
}

// Lurk supported uint coercion
#[derive(Copy, Clone)]
enum UnsignedInt {
    U32,
    U64,
}

impl UnsignedInt {
    fn num_bits(&self) -> u32 {
        match self {
            UnsignedInt::U32 => 32,
            UnsignedInt::U64 => 64,
        }
    }
}

fn to_unsigned_integer_helper<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    field_elem: &AllocatedNum<F>,
    field_bn: &BigUint,
    field_elem_bits: &[Boolean],
    size: UnsignedInt,
) -> AllocatedNum<F> {
    let power_of_two_bn = BigUint::pow(&BigUint::from_u32(2).unwrap(), size.num_bits());

    let (q_bn, r_bn) = field_bn.div_rem(&power_of_two_bn);
    let q_num = allocate_unconstrained_bignum(&mut cs.namespace(|| "q"), &q_bn);
    let r_num = allocate_unconstrained_bignum(&mut cs.namespace(|| "r"), &r_bn);
    let pow2_size = match size {
        UnsignedInt::U32 => &g.power2_32_num,
        UnsignedInt::U64 => &g.power2_64_num,
    };

    // field element = pow(2, size).q + r
    enforce_product_and_sum(
        &mut cs,
        || "product(q,pow(2,size)) + r",
        &q_num,
        pow2_size,
        &r_num,
        field_elem,
    );

    let r_bits = &field_elem_bits[0..size.num_bits() as usize];
    enforce_pack(
        &mut cs.namespace(|| "enforce unsigned pack"),
        r_bits,
        &r_num,
    );

    r_num
}

// Convert from num to unsigned integers by taking the least significant bits.
// The output is a pair of allocated numbers, where the first one corresponds to
// the u32 coercion, while the second corresponds to the u64 coercion.
fn to_unsigned_integers<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    maybe_unsigned: &AllocatedNum<F>,
) -> Result<(AllocatedNum<F>, AllocatedNum<F>), SynthesisError> {
    let field_elem = maybe_unsigned.get_value().unwrap_or(
        // dummy
        F::ZERO,
    );
    let field_bn = BigUint::from_bytes_le(field_elem.to_repr().as_ref());
    // Since bit decomposition is expensive, we compute it only once here
    let field_elem_bits =
        maybe_unsigned.to_bits_le(&mut cs.namespace(|| "field element bit decomp"))?;

    let r32_num = to_unsigned_integer_helper(
        &mut cs.namespace(|| "enforce u32"),
        g,
        maybe_unsigned,
        &field_bn,
        &field_elem_bits,
        UnsignedInt::U32,
    );
    let r64_num = to_unsigned_integer_helper(
        &mut cs.namespace(|| "enforce u64"),
        g,
        maybe_unsigned,
        &field_bn,
        &field_elem_bits,
        UnsignedInt::U64,
    );

    Ok((r32_num, r64_num))
}

// Convert from num to u64.
fn to_u64<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    maybe_u64: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let field_elem = maybe_u64.get_value().unwrap_or(F::ZERO); //
    let field_bn = BigUint::from_bytes_le(field_elem.to_repr().as_ref());
    let field_elem_bits = maybe_u64.to_bits_le(&mut cs.namespace(|| "field element bit decomp"))?;

    let r64_num = to_unsigned_integer_helper(
        &mut cs.namespace(|| "enforce u64"),
        g,
        maybe_u64,
        &field_bn,
        &field_elem_bits,
        UnsignedInt::U64,
    );

    Ok(r64_num)
}

// Enforce div and mod operation for U64. We need to show that
// arg1 = q * arg2 + r, such that 0 <= r < arg2.
fn enforce_u64_div_mod<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    cond: &Boolean,
    arg1: &AllocatedPtr<F>,
    arg2: &AllocatedPtr<F>,
) -> Result<(AllocatedNum<F>, AllocatedNum<F>), SynthesisError> {
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
        (0, 0) // Dummy
    };

    let alloc_r_num =
        AllocatedNum::alloc_infallible(&mut cs.namespace(|| "r num"), || F::from_u64(r));
    let alloc_q_num =
        AllocatedNum::alloc_infallible(&mut cs.namespace(|| "q num"), || F::from_u64(q));
    let alloc_arg1_num =
        AllocatedNum::alloc_infallible(&mut cs.namespace(|| "arg1 num"), || F::from_u64(arg1_u64));
    let alloc_arg2_num =
        AllocatedNum::alloc_infallible(&mut cs.namespace(|| "arg2 num"), || F::from_u64(arg2_u64));

    // a = b * q + r
    let product_u64mod = mul(
        &mut cs.namespace(|| "product(q,arg2)"),
        &alloc_q_num,
        &alloc_arg2_num,
    )?;
    let sum_u64mod =
        product_u64mod.add(&mut cs.namespace(|| "sum remainder mod u64"), &alloc_r_num)?;
    let u64mod_decomp = alloc_equal(
        &mut cs.namespace(|| "check u64 mod decomposition"),
        &sum_u64mod,
        &alloc_arg1_num,
    )?;
    let b_is_zero = alloc_is_zero(&mut cs.namespace(|| "b is zero"), arg2.hash())?;
    let b_is_not_zero_and_cond = Boolean::and(
        &mut cs.namespace(|| "b is not zero and cond"),
        &b_is_zero.not(),
        cond,
    )?;
    enforce_implication(
        &mut cs.namespace(|| "enforce u64 mod decomposition"),
        &b_is_not_zero_and_cond,
        &u64mod_decomp,
    );

    enforce_less_than_bound(
        &mut cs.namespace(|| "remainder in range b"),
        cond,
        &alloc_r_num,
        &alloc_arg2_num,
    )?;

    Ok((alloc_q_num, alloc_r_num))
}

// Given that `cond` is satisfied, enforce the num < bound.
// This is done by proving (bound - num) is positive.
// `num` and `bound` must be a positive field element.
// `cond` is a Boolean condition that enforces the validation iff it is True.
fn enforce_less_than_bound<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    cond: &Boolean,
    num: &AllocatedNum<F>,
    bound: &AllocatedNum<F>,
) -> Result<(), SynthesisError> {
    let diff_bound_num = sub(&mut cs.namespace(|| "bound minus num"), bound, num)?;

    let diff_bound_num_is_negative = allocate_is_negative(
        &mut cs.namespace(|| "diff bound num is negative"),
        &diff_bound_num,
    )?;

    enforce_implication(
        &mut cs.namespace(|| "enforce u64 range"),
        cond,
        &diff_bound_num_is_negative.not(),
    );
    Ok(())
}

// ATTENTION:
// Convert from bn to num. This allocation is NOT constrained here.
// In the circuit we use it to prove u64 decomposition, since using bn
// we have division with remainder, which is used to find the quotient
// after dividing by 2ˆ64. Therefore we constrain this relation afterwards.
fn allocate_unconstrained_bignum<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    bn: &BigUint,
) -> AllocatedNum<F> {
    let bytes_le = bn.to_bytes_le();
    let mut bytes_padded = [0u8; 32];
    bytes_padded[0..bytes_le.len()].copy_from_slice(&bytes_le);
    let ff = F::from_bytes(&bytes_padded).unwrap();
    AllocatedNum::alloc_infallible(&mut cs.namespace(|| "num"), || ff)
}

fn car_cdr_named<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    maybe_cons: &AllocatedPtr<F>,
    name: ConsName,
    allocated_cons_witness: &mut AllocatedConsWitness<'_, F>,
    not_dummy: &Boolean,
    _store: &Store<F>,
) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>), SynthesisError> {
    let maybe_cons_is_nil = maybe_cons.is_nil(&mut cs.namespace(|| "maybe_cons_is_nil"), g)?;

    let cons_not_dummy = and!(cs, &maybe_cons_is_nil.not(), not_dummy)?;

    let expect_dummy = !(cons_not_dummy.get_value().unwrap_or(false));

    let (allocated_car, allocated_cdr, allocated_digest) =
        allocated_cons_witness.get_cons(name, expect_dummy);

    let real_cons = alloc_equal(
        &mut cs.namespace(|| "cons is real"),
        maybe_cons.hash(),
        allocated_digest,
    )?;

    if cons_not_dummy.get_value().unwrap_or(false) && !real_cons.get_value().unwrap_or(true) {
        tracing::debug!(
            "{:?} {:?}",
            maybe_cons.hash().get_value(),
            &allocated_digest.get_value()
        );
        panic!("tried to take car_cdr of a non-dummy cons ({name:?}) but supplied wrong value");
    }

    implies!(cs, &cons_not_dummy, &real_cons);

    let res_car = pick_ptr!(cs, &maybe_cons_is_nil, &g.nil_ptr, &allocated_car)?;
    let res_cdr = pick_ptr!(cs, &maybe_cons_is_nil, &g.nil_ptr, &allocated_cdr)?;

    Ok((res_car, res_cdr))
}

fn extend_named<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    env: &AllocatedPtr<F>,
    var: &AllocatedPtr<F>,
    val: &AllocatedPtr<F>,
    name: ConsName,
    allocated_cons_witness: &mut AllocatedConsWitness<'_, F>,
    not_dummy: &Boolean,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let new_binding = AllocatedPtr::construct_cons_named(
        &mut cs.namespace(|| "extend binding"),
        g,
        var,
        val,
        ConsName::Binding,
        allocated_cons_witness,
        not_dummy,
    )?;
    AllocatedPtr::construct_cons_named(
        cs,
        g,
        &new_binding,
        env,
        name,
        allocated_cons_witness,
        not_dummy,
    )
}

fn extend_rec<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    env: &AllocatedPtr<F>,
    var: &AllocatedPtr<F>,
    val: &AllocatedPtr<F>,
    allocated_cons_witness: &mut AllocatedConsWitness<'_, F>,
    not_dummy: &Boolean,
    store: &Store<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let (binding_or_env, rest) = car_cdr_named(
        &mut cs.namespace(|| "car_cdr env"),
        g,
        env,
        ConsName::Env,
        allocated_cons_witness,
        not_dummy,
        store,
    )?;
    let (var_or_binding, _val_or_more_bindings) = car_cdr_named(
        &mut cs.namespace(|| "car_cdr binding_or_env"),
        g,
        &binding_or_env,
        ConsName::EnvCar,
        allocated_cons_witness,
        not_dummy,
        store,
    )?;

    let var_or_binding_is_cons =
        var_or_binding.is_cons(&mut cs.namespace(|| "var_or_binding_is_cons"))?;

    let cons = AllocatedPtr::construct_cons_named(
        &mut cs.namespace(|| "cons var val"),
        g,
        var,
        val,
        ConsName::NewRecCadr,
        allocated_cons_witness,
        not_dummy,
    )?;

    let cons_branch_not_dummy = and!(cs, &var_or_binding_is_cons, not_dummy)?;
    let non_cons_branch_not_dummy = and!(cs, &var_or_binding_is_cons.not(), not_dummy)?;
    let list = AllocatedPtr::construct_cons_named(
        &mut cs.namespace(|| "list cons"),
        g,
        &cons,
        &g.nil_ptr,
        ConsName::NewRec,
        allocated_cons_witness,
        &non_cons_branch_not_dummy,
    )?;

    let new_env_if_sym_or_nil = AllocatedPtr::construct_cons_named(
        &mut cs.namespace(|| "new_env_if_sym_or_nil"),
        g,
        &list,
        env,
        ConsName::ExtendedRec,
        allocated_cons_witness,
        &non_cons_branch_not_dummy,
    )?;

    let cons2 = AllocatedPtr::construct_cons_named(
        &mut cs.namespace(|| "cons cons binding_or_env"),
        g,
        &cons,
        &binding_or_env,
        ConsName::NewRec,
        allocated_cons_witness,
        &cons_branch_not_dummy,
    )?;

    let cons3 = AllocatedPtr::construct_cons_named(
        &mut cs.namespace(|| "cons cons2 rest"),
        g,
        &cons2,
        &rest,
        ConsName::ExtendedRec,
        allocated_cons_witness,
        &cons_branch_not_dummy,
    )?;

    let is_sym = var_or_binding.is_sym(&mut cs.namespace(|| "var_or_binding is sym"))?;
    let is_nil = var_or_binding.is_nil(&mut cs.namespace(|| "var_or_binding is nil"), g)?;
    let is_sym_or_nil = or!(cs, &is_sym, &is_nil)?;
    let is_cons = var_or_binding_is_cons;

    let new_env_if_cons = AllocatedPtr::pick(
        &mut cs.namespace(|| "new_env_if_cons"),
        &is_cons,
        &cons3,
        &g.error_ptr, // This is being used as a signal, since extend_rec is expected to return a valid env.
    )?;

    AllocatedPtr::pick(
        &mut cs.namespace(|| "extend_rec result"),
        &is_sym_or_nil,
        &new_env_if_sym_or_nil,
        &new_env_if_cons,
    )
}

pub fn destructure_list<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    store: &Store<F>,
    g: &GlobalAllocations<F>,
    n: usize,
    list: &AllocatedPtr<F>,
) -> Result<(Vec<AllocatedPtr<F>>, AllocatedNum<F>), SynthesisError> {
    let mut elements = Vec::with_capacity(n);

    let actual_length = destructure_list_aux(cs, store, g, n, list, &mut elements, &g.false_num)?;

    Ok((elements, actual_length))
}

fn destructure_list_aux<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    store: &Store<F>,
    g: &GlobalAllocations<F>,
    n: usize,
    list: &AllocatedPtr<F>,
    elements: &mut Vec<AllocatedPtr<F>>,
    length_so_far: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let is_cons = alloc_equal(&mut cs.namespace(|| "is_cons"), list.tag(), &g.cons_tag)?;
    let increment = boolean_to_num(&mut cs.namespace(|| "increment"), &is_cons)?;

    let new_length_so_far =
        increment.add(&mut cs.namespace(|| "new_length_so_far"), length_so_far)?;

    if n == 0 {
        return Ok(new_length_so_far.clone());
    };

    let (element, tail) = car_cdr(
        &mut cs.namespace(|| format!("element-{}", n)),
        g,
        list,
        store,
        &is_cons,
    )?;

    elements.push(element);

    destructure_list_aux(
        &mut cs.namespace(|| format!("tail-{}", n)),
        store,
        g,
        n - 1,
        &tail,
        elements,
        &new_length_so_far,
    )
}

/// Returns allocated car and cdr of `maybe_cons` if `not_dummy`.  If `maybe_cons` is not a cons and `not_dummy` is true, the circuit will not be satisfied.
pub(crate) fn car_cdr<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    maybe_cons: &AllocatedPtr<F>,
    store: &Store<F>,
    not_dummy: &Boolean,
) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>), SynthesisError> {
    let (car, cdr) = if let Some(ptr) = maybe_cons.ptr(store).as_ref() {
        if not_dummy.get_value().expect("not_dummy is missing") {
            store
                .car_cdr(ptr)
                .map_err(|_| SynthesisError::AssignmentMissing)?
        } else {
            let nil_ptr = lurk_sym_ptr!(store, nil);
            (nil_ptr, nil_ptr)
        }
    } else {
        let nil_ptr = lurk_sym_ptr!(store, nil);
        (nil_ptr, nil_ptr)
    };

    let allocated_car = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "car"), store, || Ok(&car))?;
    let allocated_cdr = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "cdr"), store, || Ok(&cdr))?;

    let constructed_cons = AllocatedPtr::construct_cons(
        &mut cs.namespace(|| "cons"),
        g,
        store,
        &allocated_car,
        &allocated_cdr,
    )?;

    let real_cons = alloc_equal(
        &mut cs.namespace(|| "cons is real"),
        maybe_cons.hash(),
        constructed_cons.hash(),
    )?;

    // If `maybe_cons` is not a cons, then it is dummy. No check is necessary.
    // Otherwise, we must enforce equality of hashes.
    enforce_implication(
        &mut cs.namespace(|| "is cons implies real cons"),
        not_dummy,
        &real_cons,
    );

    Ok((allocated_car, allocated_cdr))
}

/// Prints out the full CS for debugging purposes
#[allow(dead_code)]
pub(crate) fn print_cs<F: LurkField, C: Comparable<F>>(this: &C) -> String {
    let mut out = String::new();
    out += &format!("num_inputs: {}\n", this.num_inputs());
    out += &format!("num_constraints: {}\n", this.num_constraints());
    out += "\ninputs:\n";
    for (i, input) in this.inputs().iter().enumerate() {
        out += &format!("{i}: {input}\n");
    }
    out += "\nconstraints:\n";
    for (i, cs) in this.constraints().iter().enumerate() {
        out += &format!(
            "{}: {}:\n  {:?}\n  {:?}\n  {:?}\n",
            i,
            cs.3,
            cs.0.iter().collect::<Vec<_>>(),
            cs.1.iter().collect::<Vec<_>>(),
            cs.2.iter().collect::<Vec<_>>()
        );
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::circuit_frame::constraints::{popcount_equal};
    use crate::store::Store;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use ff::{Field, PrimeField};
    use pasta_curves::pallas::Scalar as Fr;

    #[test]
    fn test_u64_op() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &Store::<Fr>::default();

        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();

        let a = s.num(42);
        let alloc_a = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "a"), s, || Ok(&a)).unwrap();

        let a_u64 = to_u64(&mut cs.namespace(|| "u64 op"), &g, alloc_a.hash()).unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(a_u64.get_value(), Some(Fr::from_u64(42)));
    }

    #[test]
    fn test_u64_op_coercion() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();
        let alloc_pow2_64 = AllocatedPtr::from_parts(g.num_tag.clone(), g.power2_64_num.clone());

        let a_u64 = to_u64(&mut cs.namespace(|| "u64 op"), &g, alloc_pow2_64.hash()).unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(a_u64.get_value(), Some(Fr::from_u64(0)));
    }

    #[test]
    fn test_enforce_less_than_bound_corner_case() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let alloc_most_positive =
            AllocatedNum::alloc_infallible(&mut cs.namespace(|| "most positive"), || {
                Fr::most_positive()
            });
        let alloc_num =
            AllocatedNum::alloc_infallible(&mut cs.namespace(|| "num"), || Fr::from_u64(42));
        let cond = Boolean::Constant(true);

        let res = enforce_less_than_bound(
            &mut cs.namespace(|| "enforce less than bound"),
            &cond,
            &alloc_num,
            &alloc_most_positive,
        );
        assert!(res.is_ok());
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_enforce_less_than_bound() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let alloc_num =
            AllocatedNum::alloc_infallible(&mut cs.namespace(|| "num"), || Fr::from_u64(42));
        let alloc_bound =
            AllocatedNum::alloc_infallible(&mut cs.namespace(|| "bound"), || Fr::from_u64(43));
        let cond = Boolean::Constant(true);

        let res = enforce_less_than_bound(
            &mut cs.namespace(|| "enforce less than bound"),
            &cond,
            &alloc_num,
            &alloc_bound,
        );
        assert!(res.is_ok());
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_enforce_less_than_bound_negative() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let alloc_num =
            AllocatedNum::alloc_infallible(&mut cs.namespace(|| "num"), || Fr::from_u64(43));
        let alloc_bound =
            AllocatedNum::alloc_infallible(&mut cs.namespace(|| "bound"), || Fr::from_u64(42));
        let cond = Boolean::Constant(true);

        let res = enforce_less_than_bound(
            &mut cs.namespace(|| "enforce less than bound"),
            &cond,
            &alloc_num,
            &alloc_bound,
        );
        assert!(res.is_ok());
        assert!(!cs.is_satisfied());
    }

    #[test]
    fn test_enforce_u64_div_mod() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let a = s.num(42);
        let alloc_a = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "a"), s, || Ok(&a)).unwrap();
        let b = s.num(5);
        let alloc_b = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "b"), s, || Ok(&b)).unwrap();

        let cond = Boolean::Constant(true);

        let (q, r) = enforce_u64_div_mod(
            &mut cs.namespace(|| "enforce u64 div mod"),
            &cond,
            &alloc_a,
            &alloc_b,
        )
        .unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(q.get_value(), Some(Fr::from_u64(8)));
        assert_eq!(r.get_value(), Some(Fr::from_u64(2)));
    }

    #[test]
    fn test_enforce_u64_div_mod_zero() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let a = s.num(42);
        let alloc_a = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "a"), s, || Ok(&a)).unwrap();
        let b = s.num(0);
        let alloc_b = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "b"), s, || Ok(&b)).unwrap();

        let cond = Boolean::Constant(true);

        let (q, r) = enforce_u64_div_mod(
            &mut cs.namespace(|| "enforce u64 div mod"),
            &cond,
            &alloc_a,
            &alloc_b,
        )
        .unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(q.get_value(), Some(Fr::from_u64(0)));
        assert_eq!(r.get_value(), Some(Fr::from_u64(0)));
    }

    #[test]
    fn test_enforce_popcount() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        for x in 0..128 {
            let alloc_a =
                AllocatedNum::alloc(&mut cs.namespace(|| x.to_string()), || Ok(Fr::from(x)))
                    .unwrap();
            let bits = alloc_a
                .to_bits_le(&mut cs.namespace(|| format!("bits_{x}")))
                .unwrap();
            let popcount_result =
                AllocatedNum::alloc(&mut cs.namespace(|| format!("alloc popcount {x}")), || {
                    Ok(Fr::from(u64::from(x.count_ones())))
                })
                .unwrap();

            popcount_equal(
                &mut cs.namespace(|| format!("popcount {x}")),
                &bits,
                popcount_result.get_variable(),
            );
        }

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_to_u32() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();

        let a = Fr::from_u64(2);
        let v = a + Fr::pow_vartime(&Fr::from_u64(2), [32]);
        let field_bn = BigUint::from_bytes_le(v.to_repr().as_ref());

        let a_plus_power2_32_num =
            AllocatedNum::alloc_infallible(&mut cs.namespace(|| "pow(2, 32) + 2"), || v);

        let bits = a_plus_power2_32_num
            .to_bits_le(&mut cs.namespace(|| "bits"))
            .unwrap();

        let res = to_unsigned_integer_helper(
            &mut cs,
            &g,
            &a_plus_power2_32_num,
            &field_bn,
            &bits,
            UnsignedInt::U32,
        );

        assert_eq!(a, res.get_value().unwrap());
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_to_u64() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();

        let a = Fr::from_u64(2);
        let v = a + Fr::pow_vartime(&Fr::from_u64(2), [64]);
        let field_bn = BigUint::from_bytes_le(v.to_repr().as_ref());

        let a_plus_power2_64_num =
            AllocatedNum::alloc_infallible(&mut cs.namespace(|| "pow(2, 64) + 2"), || v);

        let bits = a_plus_power2_64_num
            .to_bits_le(&mut cs.namespace(|| "bits"))
            .unwrap();

        let res = to_unsigned_integer_helper(
            &mut cs,
            &g,
            &a_plus_power2_64_num,
            &field_bn,
            &bits,
            UnsignedInt::U64,
        );

        assert_eq!(a, res.get_value().unwrap());
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_enforce_pack() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let a_num =
            AllocatedNum::alloc_infallible(&mut cs.namespace(|| "a num"), || Fr::from_u64(42));
        let bits = a_num.to_bits_le(&mut cs.namespace(|| "bits")).unwrap();
        enforce_pack(&mut cs, &bits, &a_num);
        assert!(cs.is_satisfied());
    }
}
