use std::fmt::Debug;
use std::marker::PhantomData;

use bellpepper::util_cs::Comparable;
use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};

use crate::{
    circuit::gadgets::{data::GlobalAllocations, pointer::AllocatedPtr},
    field::LurkField,
};

use super::gadgets::constraints::{self, alloc_equal, enforce_implication};
use crate::circuit::circuit_frame::constraints::boolean_to_num;
use crate::coprocessor::Coprocessor;
use crate::eval::{Witness, IO};
use crate::lurk_sym_ptr;
use crate::store::Store;

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
    use crate::circuit::circuit_frame::constraints::popcount_equal;
    use crate::circuit::gadgets::constraints::implies_pack;
    use bellpepper_core::test_cs::TestConstraintSystem;

    use pasta_curves::pallas::Scalar as Fr;

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
    fn test_enforce_pack() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let a_num =
            AllocatedNum::alloc_infallible(&mut cs.namespace(|| "a num"), || Fr::from_u64(42));
        let bits = a_num.to_bits_le(&mut cs.namespace(|| "bits")).unwrap();
        implies_pack(&mut cs, &Boolean::Constant(true), &bits, &a_num);
        assert!(cs.is_satisfied());
    }
}
