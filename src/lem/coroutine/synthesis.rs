use anyhow::{Context, Result};
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError::AssignmentMissing};
use std::sync::Arc;

use super::toplevel::{Toplevel, ToplevelCircuitQuery};

use crate::field::LurkField;

use crate::circuit::gadgets::constraints::{
    alloc_equal, alloc_is_zero, div, enforce_selector_with_premise, implies_equal,
    implies_equal_const, implies_unequal_const, mul, or, pick, sub,
};
use crate::circuit::gadgets::pointer::AllocatedPtr;
use crate::coroutine::memoset::{CircuitQuery, CircuitScope, LogMemoCircuit};
use crate::lem::circuit::{BoundAllocations, GlobalAllocator};
use crate::lem::store::Store;
use crate::lem::tag::Tag;
use crate::lem::{Block, Ctrl, Func, Op};
use crate::tag::ExprTag::{Num, Sym};

/// The collection of all return values and `not_dummy`s of all
/// branches in a block and the index of the uniquely selected
/// return value, i.e. the one where the `not_dummy` is true.
/// This index is only used to copy the correct values when
/// allocating return variables, so that the constrains are
/// satisfied.
struct SelectedBranch<F: LurkField> {
    selected_index: Option<usize>,
    branches: Vec<(Boolean, Vec<AllocatedPtr<F>>)>,
}

/// Allocates variables for the return values and constrains them
/// properly, given the collection of all return values for each
/// branch. In the case where there is a unique branch, there is
/// no need to allocate new variables.
fn allocate_return<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    selected_branch: SelectedBranch<F>,
) -> Result<Vec<AllocatedPtr<F>>> {
    let SelectedBranch {
        selected_index,
        mut branches,
    } = selected_branch;
    assert!(!branches.is_empty());
    if branches.len() == 1 {
        let (_, output) = branches.pop().unwrap();
        return Ok(output);
    }
    // If there is no selected branch, just choose whichever branch
    let (_, selected_branch_output) = &branches[selected_index.unwrap_or(0)];
    let mut output = Vec::with_capacity(selected_branch_output.len());
    for (i, z) in selected_branch_output.iter().enumerate() {
        let z_ptr = || z.get_value::<Tag>().ok_or(AssignmentMissing);
        let ptr = AllocatedPtr::alloc(ns!(cs, format!("matched output {i}")), z_ptr)?;
        output.push(ptr);
    }
    for (branch_idx, (select, ptrs)) in branches.iter().enumerate() {
        for (ptr_idx, (ptr, ret_ptr)) in ptrs.iter().zip(output.iter()).enumerate() {
            ptr.implies_ptr_equal(ns!(cs, format!("{branch_idx}:{ptr_idx}")), select, ret_ptr);
        }
    }
    Ok(output)
}

pub(crate) fn synthesize_call<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    func: &Func,
    not_dummy: &Boolean,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    scope: &mut CircuitScope<F, LogMemoCircuit<F>, Arc<Toplevel<F>>>,
    bound_allocations: &mut BoundAllocations<F>,
    acc: &mut AllocatedPtr<F>,
    sub_provenances: &mut Vec<AllocatedPtr<F>>,
) -> Result<Vec<AllocatedPtr<F>>> {
    let mut selected_branch = SelectedBranch {
        selected_index: None,
        branches: vec![],
    };
    synthesize_run(
        cs,
        &func.body,
        not_dummy,
        g,
        store,
        scope,
        bound_allocations,
        acc,
        sub_provenances,
        &mut selected_branch,
    )?;
    allocate_return(cs, selected_branch)
}

fn synthesize_run<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    block: &Block,
    not_dummy: &Boolean,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    scope: &mut CircuitScope<F, LogMemoCircuit<F>, Arc<Toplevel<F>>>,
    bound_allocations: &mut BoundAllocations<F>,
    acc: &mut AllocatedPtr<F>,
    sub_provenances: &mut Vec<AllocatedPtr<F>>,
    selected_branch: &mut SelectedBranch<F>,
) -> Result<()> {
    for (op_idx, op) in block.ops.iter().enumerate() {
        let mut cs = cs.namespace(|| format!("op:{op_idx}"));
        match op {
            Op::Crout(out, name, inp) => {
                let args = bound_allocations.get_many_ptr(inp)?;
                let sub_query = ToplevelCircuitQuery::new(name.clone(), args, &scope.content)?;
                let alloc_query = sub_query.synthesize_query(&mut cs, g, store)?;
                let ((sub_result, sub_provenance), next_acc) = scope
                    .synthesize_internal_query(
                        ns!(cs, "recursive query"),
                        g,
                        store,
                        &alloc_query,
                        acc,
                        not_dummy,
                    )
                    .context("internal query failed")?;

                *acc = AllocatedPtr::pick(ns!(cs, "pick acc"), not_dummy, &next_acc, acc)?;
                let nil = g.alloc_ptr(ns!(cs, "nil"), &store.intern_nil(), store);
                let sub_provenance = AllocatedPtr::pick(
                    ns!(cs, "dependency provenance"),
                    not_dummy,
                    &sub_provenance,
                    &nil,
                )?;
                sub_provenances.push(sub_provenance);
                bound_allocations.insert_ptr(out.clone(), sub_result);
            }
            Op::Cproc(..) => unimplemented!(),
            Op::Call(out, func, inp) => {
                // Get the pointers for the input, i.e. the arguments
                let args = bound_allocations.get_many_ptr(inp)?;
                // Now we bind the `Func`'s input parameters to the arguments in the call.
                func.bind_input(&args, bound_allocations);
                // Finally, we synthesize the call
                let output_ptrs = synthesize_call(
                    ns!(cs, "call"),
                    func,
                    not_dummy,
                    g,
                    store,
                    scope,
                    bound_allocations,
                    acc,
                    sub_provenances,
                )?;
                // and bind the outputs
                for (var, ptr) in out.iter().zip(output_ptrs.into_iter()) {
                    bound_allocations.insert_ptr(var.clone(), ptr);
                }
            }
            Op::Cons2(_img, _tag, _preimg) => todo!(),
            Op::Cons3(_img, _tag, _preimg) => todo!(),
            Op::Cons4(_img, _tag, _preimg) => todo!(),
            Op::Decons2(_preimg, _img) => todo!(),
            Op::Decons3(_preimg, _img) => todo!(),
            Op::Decons4(_preimg, _img) => todo!(),
            Op::PushBinding(_img, _preimg) => todo!(),
            Op::PopBinding(_preimg, _img) => todo!(),
            Op::Copy(tgt, src) => {
                bound_allocations.insert(tgt.clone(), bound_allocations.get(src).cloned()?);
            }
            Op::Zero(tgt, tag) => {
                bound_allocations
                    .insert_ptr(tgt.clone(), g.alloc_z_ptr_from_parts(&mut cs, tag, F::ZERO));
            }
            Op::Hash3Zeros(tgt, tag) => {
                bound_allocations.insert_ptr(
                    tgt.clone(),
                    g.alloc_z_ptr_from_parts(&mut cs, tag, *store.hash3zeros()),
                );
            }
            Op::Hash4Zeros(tgt, tag) => {
                bound_allocations.insert_ptr(
                    tgt.clone(),
                    g.alloc_z_ptr_from_parts(&mut cs, tag, *store.hash4zeros()),
                );
            }
            Op::Hash6Zeros(tgt, tag) => {
                bound_allocations.insert_ptr(
                    tgt.clone(),
                    g.alloc_z_ptr_from_parts(&mut cs, tag, *store.hash6zeros()),
                );
            }
            Op::Hash8Zeros(tgt, tag) => {
                bound_allocations.insert_ptr(
                    tgt.clone(),
                    g.alloc_z_ptr_from_parts(&mut cs, tag, *store.hash8zeros()),
                );
            }
            Op::Lit(tgt, lit) => {
                let allocated_ptr = g.alloc_ptr(&mut cs, &lit.to_ptr(store), store);
                bound_allocations.insert_ptr(tgt.clone(), allocated_ptr);
            }
            Op::Cast(tgt, tag, src) => {
                let src = bound_allocations.get_ptr(src)?;
                let tag = g.alloc_tag_cloned(&mut cs, tag);
                let allocated_ptr = AllocatedPtr::from_parts(tag, src.hash().clone());
                bound_allocations.insert_ptr(tgt.clone(), allocated_ptr);
            }
            Op::EqTag(tgt, a, b) => {
                let a = bound_allocations.get_ptr(a)?;
                let b = bound_allocations.get_ptr(b)?;
                let a_num = a.tag();
                let b_num = b.tag();
                let eq = alloc_equal(cs.namespace(|| "equal_tag"), a_num, b_num)?;
                bound_allocations.insert_bool(tgt.clone(), eq);
            }
            Op::EqVal(tgt, a, b) => {
                let a = bound_allocations.get_ptr(a)?;
                let b = bound_allocations.get_ptr(b)?;
                let a_num = a.hash();
                let b_num = b.hash();
                let eq = alloc_equal(cs.namespace(|| "equal_val"), a_num, b_num)?;
                bound_allocations.insert_bool(tgt.clone(), eq);
            }
            Op::Not(tgt, a) => {
                let a = bound_allocations.get_bool(a)?;
                bound_allocations.insert_bool(tgt.clone(), a.not());
            }
            Op::And(tgt, a, b) => {
                let a = bound_allocations.get_bool(a)?;
                let b = bound_allocations.get_bool(b)?;
                let c = Boolean::and(ns!(cs, "and"), a, b)?;
                bound_allocations.insert_bool(tgt.clone(), c);
            }
            Op::Or(tgt, a, b) => {
                let a = bound_allocations.get_bool(a)?;
                let b = bound_allocations.get_bool(b)?;
                let c = or(cs.namespace(|| "or"), a, b)?;
                bound_allocations.insert_bool(tgt.clone(), c);
            }
            Op::Add(tgt, a, b) => {
                let a = bound_allocations.get_ptr(a)?;
                let b = bound_allocations.get_ptr(b)?;
                let a_num = a.hash();
                let b_num = b.hash();
                let c_num = a_num.add(cs.namespace(|| "add"), b_num)?;
                let tag = g.alloc_tag_cloned(&mut cs, &Num);
                let c = AllocatedPtr::from_parts(tag, c_num);
                bound_allocations.insert_ptr(tgt.clone(), c);
            }
            Op::Sub(tgt, a, b) => {
                let a = bound_allocations.get_ptr(a)?;
                let b = bound_allocations.get_ptr(b)?;
                let a_num = a.hash();
                let b_num = b.hash();
                let c_num = sub(cs.namespace(|| "sub"), a_num, b_num)?;
                let tag = g.alloc_tag_cloned(&mut cs, &Num);
                let c = AllocatedPtr::from_parts(tag, c_num);
                bound_allocations.insert_ptr(tgt.clone(), c);
            }
            Op::Mul(tgt, a, b) => {
                let a = bound_allocations.get_ptr(a)?;
                let b = bound_allocations.get_ptr(b)?;
                let a_num = a.hash();
                let b_num = b.hash();
                let c_num = mul(cs.namespace(|| "mul"), a_num, b_num)?;
                let tag = g.alloc_tag_cloned(&mut cs, &Num);
                let c = AllocatedPtr::from_parts(tag, c_num);
                bound_allocations.insert_ptr(tgt.clone(), c);
            }
            Op::Div(tgt, a, b) => {
                let a = bound_allocations.get_ptr(a)?;
                let b = bound_allocations.get_ptr(b)?;
                let a_num = a.hash();
                let b_num = b.hash();

                let b_is_zero = &alloc_is_zero(cs.namespace(|| "b_is_zero"), b_num)?;
                let one = g.alloc_const(&mut cs, F::ONE);

                let divisor = pick(
                    cs.namespace(|| "maybe-dummy divisor"),
                    b_is_zero,
                    one,
                    b_num,
                )?;

                let quotient = div(cs.namespace(|| "quotient"), a_num, &divisor)?;

                let tag = g.alloc_tag_cloned(&mut cs, &Num);
                let c = AllocatedPtr::from_parts(tag, quotient);
                bound_allocations.insert_ptr(tgt.clone(), c);
            }
            Op::Lt(_tgt, _a, _b) => todo!(),
            Op::Trunc(_tgt, _a, _n) => todo!(),
            Op::DivRem64(_tgt, _a, _b) => todo!(),
            Op::Emit(_) | Op::Unit(_) => (),
            Op::Hide(_tgt, _sec, _pay) => todo!(),
            Op::Open(_sec, _pay, _comm) => todo!(),
        }
    }

    let mut synthesize_match = |matched: &AllocatedNum<F>,
                                cases: &[(F, &Block)],
                                def: &Option<Box<Block>>,
                                bound_allocations: &mut BoundAllocations<F>|
     -> Result<()> {
        // * One `Boolean` for each case
        // * Maybe one `Boolean` for the default case
        let selector_size = cases.len() + usize::from(def.is_some());
        let mut selector = Vec::with_capacity(selector_size);
        for (i, (f, block)) in cases.iter().enumerate() {
            // For each case, we compute `not_dummy_and_has_match: Boolean`
            // and accumulate them on a `selector` vector
            let not_dummy_and_has_match_bool = not_dummy.get_value().and_then(|not_dummy| {
                matched
                    .get_value()
                    .map(|matched_f| not_dummy && &matched_f == f)
            });
            let not_dummy_and_has_match = Boolean::Is(AllocatedBit::alloc(
                cs.namespace(|| format!("{i}.allocated_bit")),
                not_dummy_and_has_match_bool,
            )?);

            // If `not_dummy_and_has_match` is true, then we enforce a match
            implies_equal_const(
                ns!(cs, format!("{i}.implies_equal_const")),
                &not_dummy_and_has_match,
                matched,
                *f,
            );

            selector.push(not_dummy_and_has_match.clone());

            synthesize_run(
                ns!(cs, format!("{i}")),
                block,
                &not_dummy_and_has_match,
                g,
                store,
                scope,
                bound_allocations,
                acc,
                sub_provenances,
                selected_branch,
            )?;
        }

        if let Some(def) = def {
            // Compute `default: Boolean`, which tells whether the default case was chosen or not
            let is_default_bool = selector.iter().fold(not_dummy.get_value(), |acc, b| {
                // all the booleans in `selector` have to be false up to this point
                // in order for the default case to be selected
                acc.and_then(|acc| b.get_value().map(|b| acc && !b))
            });
            let is_default = Boolean::Is(AllocatedBit::alloc(
                cs.namespace(|| "_.allocated_bit"),
                is_default_bool,
            )?);

            for (i, (f, _)) in cases.iter().enumerate() {
                // if the default path was taken, then there can be no tag in `cases`
                // that equals the tag of the pointer being matched on
                implies_unequal_const(
                    ns!(cs, format!("{i}.implies_unequal_const")),
                    &is_default,
                    matched,
                    *f,
                )?;
            }

            synthesize_run(
                ns!(cs, "_"),
                def,
                &is_default,
                g,
                store,
                scope,
                bound_allocations,
                acc,
                sub_provenances,
                selected_branch,
            )?;

            // Pushing `is_default` to `selector` to enforce summation = 1
            selector.push(is_default);
        }

        // Now we need to enforce that exactly one path was taken. We do that by enforcing
        // that the sum of the previously collected `Boolean`s is one. But, of course, this
        // is irrelevant if we're on a virtual path and thus we use an implication gadget.
        enforce_selector_with_premise(
            ns!(cs, "enforce_selector_with_premise"),
            not_dummy,
            &selector,
        );
        Ok(())
    };

    match &block.ctrl {
        Ctrl::Return(return_vars) => {
            let output = bound_allocations.get_many_ptr(return_vars)?;
            // If `not_dummy` is true, then this is the uniquely selected
            // branch. The values from `output` will be copied if there is
            // a need to allocate return variables.
            if not_dummy.get_value() == Some(true) {
                let index = selected_branch.branches.len();
                selected_branch.selected_index = Some(index);
            }
            selected_branch.branches.push((not_dummy.clone(), output));
        }
        Ctrl::If(b, true_block, false_block) => {
            let b = bound_allocations.get_bool(b)?;
            let b_not_dummy = Boolean::and(ns!(cs, "b and not_dummy"), b, not_dummy)?;
            let not_b_not_dummy =
                Boolean::and(ns!(cs, "not_b and not_dummy"), &b.not(), not_dummy)?;
            synthesize_run(
                ns!(cs, "if_eq.true"),
                true_block,
                &b_not_dummy,
                g,
                store,
                scope,
                bound_allocations,
                acc,
                sub_provenances,
                selected_branch,
            )?;
            synthesize_run(
                ns!(cs, "if_eq.false"),
                false_block,
                &not_b_not_dummy,
                g,
                store,
                scope,
                bound_allocations,
                acc,
                sub_provenances,
                selected_branch,
            )?;
        }
        Ctrl::MatchTag(match_var, cases, def) => {
            let matched = bound_allocations.get_ptr(match_var)?.tag().clone();
            let cases_vec = cases
                .iter()
                .map(|(tag, block)| (tag.to_field::<F>(), block))
                .collect::<Vec<_>>();
            synthesize_match(&matched, &cases_vec, def, bound_allocations)?;
        }
        Ctrl::MatchSymbol(match_var, cases, def) => {
            let match_var_ptr = bound_allocations.get_ptr(match_var)?.clone();

            let mut cases_vec = Vec::with_capacity(cases.len());
            for (sym, block) in cases {
                let sym_ptr = store.intern_symbol(sym);
                let sym_hash = *store.hash_ptr(&sym_ptr).value();
                cases_vec.push((sym_hash, block));
            }

            synthesize_match(match_var_ptr.hash(), &cases_vec, def, bound_allocations)?;

            let sym_tag = g.alloc_tag(cs, &Sym);
            implies_equal(
                ns!(cs, format!("implies equal {match_var}.tag")),
                not_dummy,
                match_var_ptr.tag(),
                sym_tag,
            );
        }
    }
    Ok(())
}
