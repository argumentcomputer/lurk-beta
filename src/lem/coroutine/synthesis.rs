use anyhow::{Context, Result};
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError::AssignmentMissing};
use neptune::circuit2::poseidon_hash_allocated as poseidon_hash;
use std::sync::Arc;

use super::toplevel::{Toplevel, ToplevelCircuitQuery};

use crate::field::{FWrap, LurkField};

use crate::circuit::gadgets::constraints::{
    alloc_equal, alloc_is_zero, div, enforce_product_and_sum, enforce_selector_with_premise,
    implies_equal, implies_equal_const, implies_pack, implies_u64, implies_unequal_const, mul, or,
    pick, sub,
};
use crate::circuit::gadgets::pointer::AllocatedPtr;
use crate::coroutine::memoset::{CircuitQuery, CircuitScope, LogMemoCircuit};
use crate::lem::circuit::{BoundAllocations, GlobalAllocator};
use crate::lem::pointers::{IVal, Ptr};
use crate::lem::store::Store;
use crate::lem::tag::Tag;
use crate::lem::{Block, Ctrl, Func, Op, Var};
use crate::tag::ExprTag::{Comm, Env, Num, Sym};

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
        let z_ptr = || z.get_value().ok_or(AssignmentMissing);
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

pub(crate) fn synthesize_call<'a, F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    func: &Func,
    not_dummy: &Boolean,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    scope: &mut CircuitScope<'a, F, LogMemoCircuit<'a, F>, Arc<Toplevel<F>>>,
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

fn synthesize_run<'a, F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    block: &Block,
    not_dummy: &Boolean,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    scope: &mut CircuitScope<'a, F, LogMemoCircuit<'a, F>, Arc<Toplevel<F>>>,
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
                let sub_query = ToplevelCircuitQuery::new(name.clone(), args, &scope.runtime_data)?;
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
            // TODO: Slot allocation for hashes and bit decompositions
            Op::Cons2(img, tag, preimg) => {
                synthesize_cons(&mut cs, img, tag, preimg, store, bound_allocations, g)?;
            }
            Op::Cons3(img, tag, preimg) => {
                synthesize_cons(&mut cs, img, tag, preimg, store, bound_allocations, g)?;
            }
            Op::Cons4(img, tag, preimg) => {
                synthesize_cons(&mut cs, img, tag, preimg, store, bound_allocations, g)?;
            }
            Op::Decons2(preimg, img) => {
                synthesize_decons(&mut cs, not_dummy, preimg, img, store, bound_allocations)?
            }
            Op::Decons3(preimg, img) => {
                synthesize_decons(&mut cs, not_dummy, preimg, img, store, bound_allocations)?
            }
            Op::Decons4(preimg, img) => {
                synthesize_decons(&mut cs, not_dummy, preimg, img, store, bound_allocations)?
            }
            Op::PushBinding(img, [var, val, env]) => {
                let var = bound_allocations.get_ptr(var)?;
                let val = bound_allocations.get_ptr(val)?;
                let env = bound_allocations.get_ptr(env)?;
                let preimg = vec![
                    var.hash().clone(),
                    val.tag().clone(),
                    val.hash().clone(),
                    env.hash().clone(),
                ];
                let env_tag = g.alloc_tag_cloned(&mut cs, &Env);
                implies_equal(ns!(cs, format!("env_tag")), not_dummy, env.tag(), &env_tag);
                let res = poseidon_hash(
                    ns!(cs, "poseidon_hash"),
                    preimg,
                    store.core.hasher.constants.c4(),
                )?;
                let tag = g.alloc_tag_cloned(&mut cs, &Env);
                let ptr = AllocatedPtr::from_parts(tag, res);
                bound_allocations.insert_ptr(img.clone(), ptr);
            }
            Op::PopBinding(preimg, img) => {
                let img = bound_allocations.get_ptr(img)?;
                let preimg_alloc_nums = if let Some(img_val) = img.get_value() {
                    let [a, b, c] = store.pop_binding(&store.to_ptr(&img_val)).unwrap();
                    let a = store.hash_ptr(a);
                    let b = store.hash_ptr(b);
                    let c = store.hash_ptr(c);
                    [*a.hash(), b.tag_field(), *b.hash(), *c.hash()]
                        .into_iter()
                        .enumerate()
                        .map(|(i, f)| {
                            let cs = ns!(cs, format!("preimg {i}"));
                            AllocatedNum::alloc_infallible(cs, || f)
                        })
                        .collect::<Vec<_>>()
                } else {
                    (0..4)
                        .map(|i| {
                            let cs = ns!(cs, format!("preimg {i}"));
                            AllocatedNum::alloc_infallible(cs, || F::ZERO)
                        })
                        .collect::<Vec<_>>()
                };

                let hash = poseidon_hash(
                    ns!(cs, "poseidon_hash"),
                    preimg_alloc_nums.clone(),
                    store.core.hasher.constants.c6(),
                )?;

                implies_equal(
                    ns!(cs, format!("implies equal img.hash")),
                    not_dummy,
                    &hash,
                    img.hash(),
                );

                let sym_tag = g.alloc_tag_cloned(&mut cs, &Sym);
                let sym_hash = &preimg_alloc_nums[0];
                let sym_ptr = AllocatedPtr::from_parts(sym_tag, sym_hash.clone());
                bound_allocations.insert_ptr(preimg[0].clone(), sym_ptr);
                let val_tag = &preimg_alloc_nums[1];
                let val_hash = &preimg_alloc_nums[2];
                let val_ptr = AllocatedPtr::from_parts(val_tag.clone(), val_hash.clone());
                bound_allocations.insert_ptr(preimg[1].clone(), val_ptr);
                let env_tag = g.alloc_tag_cloned(&mut cs, &Env);
                let env_hash = &preimg_alloc_nums[3];
                let env_ptr = AllocatedPtr::from_parts(env_tag, env_hash.clone());
                bound_allocations.insert_ptr(preimg[2].clone(), env_ptr);
            }
            Op::Copy(tgt, src) => {
                let ptr = bound_allocations.get(src).cloned()?;
                bound_allocations.insert(tgt.clone(), ptr);
            }
            Op::Zero(tgt, tag) => {
                let ptr = g.alloc_z_ptr_from_parts(&mut cs, tag, F::ZERO);
                bound_allocations.insert_ptr(tgt.clone(), ptr);
            }
            Op::Hash3Zeros(tgt, tag) => {
                let ptr = g.alloc_z_ptr_from_parts(&mut cs, tag, *store.hash3zeros());
                bound_allocations.insert_ptr(tgt.clone(), ptr);
            }
            Op::Hash4Zeros(tgt, tag) => {
                let ptr = g.alloc_z_ptr_from_parts(&mut cs, tag, *store.hash4zeros());
                bound_allocations.insert_ptr(tgt.clone(), ptr);
            }
            Op::Hash6Zeros(tgt, tag) => {
                let ptr = g.alloc_z_ptr_from_parts(&mut cs, tag, *store.hash6zeros());
                bound_allocations.insert_ptr(tgt.clone(), ptr);
            }
            Op::Hash8Zeros(tgt, tag) => {
                let ptr = g.alloc_z_ptr_from_parts(&mut cs, tag, *store.hash8zeros());
                bound_allocations.insert_ptr(tgt.clone(), ptr);
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
            Op::Lt(tgt, a, b) => {
                // To find out whether a < b, we will use the following reasoning:
                // 1) when a and b have the same sign, a < b iff a - b is negative
                // 2) when a and b have different signs, a < b iff a is negative
                // 3) a number is negative iff its double is odd
                // 4) a number is odd iff its least significant bit is 1

                // Retrieve a, b, a-b
                let a_num = bound_allocations.get_ptr(a)?.hash();
                let b_num = bound_allocations.get_ptr(b)?.hash();
                let diff = sub(cs.namespace(|| "diff"), a_num, b_num)?;
                // Double a, b, a-b
                let double_a = a_num.add(cs.namespace(|| "double_a"), a_num)?;
                let double_b = b_num.add(cs.namespace(|| "double_b"), b_num)?;
                let double_diff = diff.add(cs.namespace(|| "double_diff"), &diff)?;

                let double_a_bits = double_a.to_bits_le_strict(ns!(cs, "double_a_bits"))?;
                let double_b_bits = double_b.to_bits_le_strict(ns!(cs, "double_b_bits"))?;
                let double_diff_bits =
                    double_diff.to_bits_le_strict(ns!(cs, "double_diff_bits"))?;

                // The number is negative if the least significant bit of its double is 1
                let a_is_negative = double_a_bits.first().unwrap();
                let b_is_negative = double_b_bits.first().unwrap();
                let diff_is_negative = double_diff_bits.first().unwrap();

                // Two numbers have the same sign if both are negative or both are positive, i.e.
                let same_sign =
                    Boolean::xor(cs.namespace(|| "same_sign"), a_is_negative, b_is_negative)?.not();

                // Finally, a < b iff (same_sign && diff < 0) || (!same_sign && a < 0)
                let and1 = Boolean::and(ns!(cs, "and1"), &same_sign, diff_is_negative)?;
                let and2 = Boolean::and(ns!(cs, "and2"), &same_sign.not(), a_is_negative)?;
                let lt = or(ns!(cs, "or"), &and1, &and2)?;
                bound_allocations.insert_bool(tgt.clone(), lt.clone());
            }
            Op::Trunc(tgt, a, n) => {
                assert!(*n <= 64);
                let a = bound_allocations.get_ptr(a)?;
                let trunc_bits = a.hash().to_bits_le_strict(ns!(cs, "trunc_bits"))?;
                let trunc_bits = &trunc_bits[0..*n as usize];
                let trunc = AllocatedNum::alloc(cs.namespace(|| "trunc"), || {
                    let b = if *n < 64 { (1 << *n) - 1 } else { u64::MAX };
                    a.hash()
                        .get_value()
                        .map(|a| F::from_u64(a.to_u64_unchecked() & b))
                        .ok_or(AssignmentMissing)
                })?;
                implies_pack(
                    cs.namespace(|| "implies_trunc"),
                    not_dummy,
                    trunc_bits,
                    &trunc,
                );
                let tag = g.alloc_tag_cloned(&mut cs, &Num);
                let c = AllocatedPtr::from_parts(tag, trunc);
                bound_allocations.insert_ptr(tgt.clone(), c);
            }
            Op::DivRem64(tgt, a, b) => {
                let a = bound_allocations.get_ptr(a)?.hash();
                let b = bound_allocations.get_ptr(b)?.hash();
                let div_rem = a.get_value().and_then(|a| {
                    b.get_value().map(|b| {
                        if not_dummy.get_value().unwrap() {
                            let a = a.to_u64_unchecked();
                            let b = b.to_u64_unchecked();
                            (F::from_u64(a / b), F::from_u64(a % b))
                        } else {
                            (F::ZERO, a)
                        }
                    })
                });
                let div =
                    AllocatedNum::alloc_infallible(cs.namespace(|| "div"), || div_rem.unwrap().0);
                let rem =
                    AllocatedNum::alloc_infallible(cs.namespace(|| "rem"), || div_rem.unwrap().1);

                let diff = sub(cs.namespace(|| "diff for slot {slot}"), b, &rem)?;
                implies_u64(cs.namespace(|| "div_u64"), not_dummy, &div)?;
                implies_u64(cs.namespace(|| "rem_u64"), not_dummy, &rem)?;
                implies_u64(cs.namespace(|| "diff_u64"), not_dummy, &diff)?;

                enforce_product_and_sum(&mut cs, || "enforce a = b * div + rem", b, &div, &rem, a);
                let tag = g.alloc_tag_cloned(&mut cs, &Num);
                let div_ptr = AllocatedPtr::from_parts(tag.clone(), div);
                let rem_ptr = AllocatedPtr::from_parts(tag, rem);
                bound_allocations.insert_ptr(tgt[0].clone(), div_ptr);
                bound_allocations.insert_ptr(tgt[1].clone(), rem_ptr);
            }
            Op::Emit(_) | Op::Unit(_) => (),
            Op::Recv(_) => todo!("not supported yet"),
            Op::Hide(tgt, sec, pay) => {
                let sec = bound_allocations.get_ptr(sec)?;
                let pay = bound_allocations.get_ptr(pay)?;
                let sec_tag = g.alloc_tag(&mut cs, &Num);

                let preimg = vec![sec.hash().clone(), pay.tag().clone(), pay.hash().clone()];
                let hash = poseidon_hash(
                    ns!(cs, "poseidon_hash"),
                    preimg,
                    store.core.hasher.constants.c3(),
                )?;

                implies_equal(
                    ns!(cs, "implies equal secret.tag"),
                    not_dummy,
                    sec.tag(),
                    sec_tag,
                );
                let tag = g.alloc_tag_cloned(&mut cs, &Comm);
                let allocated_ptr = AllocatedPtr::from_parts(tag, hash.clone());
                bound_allocations.insert_ptr(tgt.clone(), allocated_ptr);
            }
            Op::Open(sec, pay, comm) => {
                let comm = bound_allocations.get_ptr(comm)?;
                let preimg_alloc_nums = if let Some(hash) = comm.hash().get_value() {
                    let (FWrap(secret), payload) = store.open(hash).unwrap();
                    let (payload_tag, FWrap(payload_hash)) = store.hash_ptr(payload).into_parts();
                    let mut alloc = |idx, f| {
                        AllocatedNum::alloc_infallible(ns!(cs, format!("preimg {idx}")), || f)
                    };
                    let secret = alloc(0, *secret);
                    let payload_tag = alloc(1, payload_tag.to_field());
                    let payload_hash = alloc(2, payload_hash);
                    vec![secret, payload_tag, payload_hash]
                } else {
                    (0..3)
                        .map(|i| {
                            let cs = ns!(cs, format!("preimg {i}"));
                            AllocatedNum::alloc_infallible(cs, || F::ZERO)
                        })
                        .collect()
                };

                let hash = poseidon_hash(
                    ns!(cs, "poseidon_hash"),
                    preimg_alloc_nums.clone(),
                    store.core.hasher.constants.c3(),
                )?;

                let comm_tag = g.alloc_tag(&mut cs, &Comm);
                implies_equal(
                    ns!(cs, "implies equal comm.tag"),
                    not_dummy,
                    comm.tag(),
                    comm_tag,
                );
                implies_equal(
                    ns!(cs, "implies equal comm.hash"),
                    not_dummy,
                    &hash,
                    comm.hash(),
                );
                let sec_tag = g.alloc_tag_cloned(&mut cs, &Num);
                let allocated_sec_ptr =
                    AllocatedPtr::from_parts(sec_tag, preimg_alloc_nums[0].clone());
                let allocated_pay_ptr = AllocatedPtr::from_parts(
                    preimg_alloc_nums[1].clone(),
                    preimg_alloc_nums[2].clone(),
                );
                bound_allocations.insert_ptr(sec.clone(), allocated_sec_ptr);
                bound_allocations.insert_ptr(pay.clone(), allocated_pay_ptr);
            }
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
        Ctrl::MatchValue(match_var, lit_type, cases, def) => {
            let tag = lit_type.tag();
            let match_var_ptr = bound_allocations.get_ptr(match_var)?.clone();

            let mut cases_vec = Vec::with_capacity(cases.len());
            for (lit, block) in cases {
                let lit_ptr = lit.to_ptr(store);
                let lit_hash = *store.hash_ptr(&lit_ptr).hash();
                cases_vec.push((lit_hash, block));
            }

            synthesize_match(match_var_ptr.hash(), &cases_vec, def, bound_allocations)?;

            let lit_tag = g.alloc_tag(cs, &tag);
            implies_equal(
                ns!(cs, format!("implies equal {match_var}.tag")),
                not_dummy,
                match_var_ptr.tag(),
                lit_tag,
            );
        }
    }
    Ok(())
}

fn retrieve_nums<F: LurkField>(
    vars: &[Var],
    bound_allocations: &BoundAllocations<F>,
) -> Result<Vec<AllocatedNum<F>>> {
    let mut nums = Vec::with_capacity(vars.len() * 2);
    for var in vars {
        let p = bound_allocations.get_ptr(var)?;
        nums.push(p.tag().clone());
        nums.push(p.hash().clone());
    }
    Ok(nums)
}

fn synthesize_cons<const N: usize, F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    img: &Var,
    tag: &Tag,
    preimg: &[Var; N],
    store: &Store<F>,
    bound_allocations: &mut BoundAllocations<F>,
    g: &GlobalAllocator<F>,
) -> Result<()> {
    let preimg = retrieve_nums(preimg, bound_allocations)?;
    let constants = &store.core.hasher.constants;
    let hash = match N {
        2 => poseidon_hash(ns!(cs, "poseidon_hash"), preimg, constants.c4())?,
        3 => poseidon_hash(ns!(cs, "poseidon_hash"), preimg, constants.c6())?,
        4 => poseidon_hash(ns!(cs, "poseidon_hash"), preimg, constants.c8())?,
        _ => unimplemented!(),
    };
    let tag = g.alloc_tag_cloned(cs, tag);
    let ptr = AllocatedPtr::from_parts(tag, hash);
    bound_allocations.insert_ptr(img.clone(), ptr);
    Ok(())
}

fn synthesize_decons<const N: usize, F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    not_dummy: &Boolean,
    preimg: &[Var; N],
    img: &Var,
    store: &Store<F>,
    bound_allocations: &mut BoundAllocations<F>,
) -> Result<()> {
    let img = bound_allocations.get_ptr(img)?;
    let preimg_alloc_nums = if Some(true) == not_dummy.get_value() {
        let img_z_ptr = img.get_value().unwrap();
        let ptrs: &[Ptr] = match store.to_ptr_val(img_z_ptr.val()) {
            IVal::Tuple2(idx) => store.expect_tuple2(idx),
            IVal::Tuple3(idx) => store.expect_tuple3(idx),
            IVal::Tuple4(idx) => store.expect_tuple4(idx),
            _ => panic!("Invalid decons"),
        };
        assert_eq!(ptrs.len(), N);
        let mut allocations = Vec::with_capacity(2 * N);
        for (i, ptr) in ptrs.iter().enumerate() {
            let (tag, FWrap(hash)) = store.hash_ptr(ptr).into_parts();
            allocations.push(AllocatedNum::alloc_infallible(
                ns!(cs, format!("preimg {}", 2 * i)),
                || tag.to_field(),
            ));
            allocations.push(AllocatedNum::alloc_infallible(
                ns!(cs, format!("preimg {}", 2 * i + 1)),
                || hash,
            ));
        }
        allocations
    } else {
        (0..2 * N)
            .map(|i| {
                let cs = ns!(cs, format!("preimg {i}"));
                AllocatedNum::alloc_infallible(cs, || F::ZERO)
            })
            .collect()
    };

    let preimg_clone = preimg_alloc_nums.clone();
    let constants = &store.core.hasher.constants;
    let hash = match N {
        2 => poseidon_hash(ns!(cs, "poseidon_hash"), preimg_clone, constants.c4())?,
        3 => poseidon_hash(ns!(cs, "poseidon_hash"), preimg_clone, constants.c6())?,
        4 => poseidon_hash(ns!(cs, "poseidon_hash"), preimg_clone, constants.c8())?,
        _ => unimplemented!(),
    };

    implies_equal(
        ns!(cs, "implies equal img.hash"),
        not_dummy,
        img.hash(),
        &hash,
    );

    for (i, var) in preimg.iter().enumerate() {
        let tag = preimg_alloc_nums[2 * i].clone();
        let hash = preimg_alloc_nums[2 * i + 1].clone();
        let alloc_ptr = AllocatedPtr::from_parts(tag, hash);
        bound_allocations.insert_ptr(var.clone(), alloc_ptr);
    }
    Ok(())
}
