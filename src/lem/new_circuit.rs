#![allow(dead_code)]
#![allow(unused_imports)]
use std::collections::{HashMap, HashSet, VecDeque};

use anyhow::{bail, Context, Result};
use bellpepper_core::{
    ConstraintSystem, SynthesisError,
    {
        boolean::{AllocatedBit, Boolean},
        num::AllocatedNum,
    },
};

use crate::circuit::gadgets::data::hash_poseidon;
use crate::lem::gadgets::elt_1::*;

use crate::{
    field::{FWrap, LurkField},
    tag::ExprTag::*,
};

use ff::PrimeField;

use super::{
    interpreter::{Frame, PreimageData},
    pointers::{Ptr, ZPtr},
    slot::*,
    store::Store,
    var_map::VarMap,
    Block, Ctrl, Func, Op, Tag, Var,
};

#[derive(Clone)]
pub(crate) enum CircuitPtr<F: PrimeField> {
    Ptr(Elt<F>, Elt<F>),
    Bool(Boolean),
}

type BoundAllocations<F> = VarMap<CircuitPtr<F>>;

impl<F: PrimeField> BoundAllocations<F> {
    fn get_many_ptr(&self, args: &[Var]) -> Result<Vec<(&Elt<F>, &Elt<F>)>> {
        args.iter().map(|arg| self.get_ptr(arg)).collect()
    }

    fn get_ptr(&self, var: &Var) -> Result<(&Elt<F>, &Elt<F>)> {
        if let CircuitPtr::Ptr(tag, hash) = self.get(var)? {
            return Ok((tag, hash));
        }
        bail!("Expected {var} to be a pointer")
    }

    fn get_bool(&self, var: &Var) -> Result<&Boolean> {
        if let CircuitPtr::Bool(b) = self.get(var)? {
            return Ok(b);
        }
        bail!("Expected {var} to be a boolean")
    }
}

fn alloc_zptr<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    z_ptr: &ZPtr<F>,
) -> Result<(AllocatedNum<F>, AllocatedNum<F>)> {
    let tag = AllocatedNum::alloc(cs.namespace(|| "alloc tag"), || Ok(z_ptr.tag.to_field()))?;
    let hash = AllocatedNum::alloc(cs.namespace(|| "alloc hash"), || Ok(z_ptr.hash))?;
    Ok((tag, hash))
}

fn alloc_func_input<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    func: &Func,
    store: &mut Store<F>,
    frame: &Frame<F>,
    bound_allocations: &mut BoundAllocations<F>,
) -> Result<()> {
    for (i, ptr) in frame.input.iter().enumerate() {
        let param = &func.input_params[i];
        let z_ptr = &store.hash_ptr(ptr)?;
        let (tag, hash) = alloc_zptr(cs.namespace(|| format!("param {i}")), z_ptr)?;
        let ptr = CircuitPtr::Ptr(Elt::from(tag), Elt::from(hash));
        bound_allocations.insert(param.clone(), ptr);
    }
    Ok(())
}

/// Allocates an unconstrained pointer for each output of the frame
fn alloc_frame_output<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    store: &mut Store<F>,
    frame: &Frame<F>,
) -> Result<Vec<AllocatedNum<F>>> {
    let mut outputs = Vec::with_capacity(frame.output.len());
    for i in 0..frame.output.len() {
        let (tag, hash) = alloc_zptr(
            cs.namespace(|| format!("output {i}")),
            &store.hash_ptr(&frame.output[i])?,
        )?;
        outputs.push(tag);
        outputs.push(hash);
    }
    Ok(outputs)
}

/// Synthesizes a `Func`
pub(crate) fn synthesize_func<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    func: &Func,
    store: &mut Store<F>,
    frame: &Frame<F>,
    bound_allocations: &mut BoundAllocations<F>,
) -> Result<Vec<AllocatedNum<F>>> {
    alloc_func_input(
        cs.namespace(|| "synth input"),
        func,
        store,
        frame,
        bound_allocations,
    )?;
    let outputs = alloc_frame_output(cs.namespace(|| "synth output"), store, frame)?;
    assert_eq!(outputs.len(), func.output_size * 2);
    let advices = &mut build_func_advices(cs.namespace(|| "advices"), func, store, frame)?;
    let slot_pos = &mut SlotsCounter::default();
    synthesize_func_aux(
        cs,
        &func.body,
        &Boolean::Constant(true),
        store,
        bound_allocations,
        &outputs,
        slot_pos,
        advices,
    )?;
    Ok(outputs)
}

pub(crate) fn synthesize_func_aux<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    block: &Block,
    not_dummy: &Boolean,
    store: &mut Store<F>,
    bound_allocations: &mut BoundAllocations<F>,
    outputs: &Vec<AllocatedNum<F>>,
    slot_pos: &mut SlotsCounter,
    advices: &mut Advices<F>,
) -> Result<()> {
    for (i, op) in block.ops.iter().enumerate() {
        let mut cs = cs.namespace(|| format!("op {i}"));
        macro_rules! hash_helper {
            ( $tgt: expr, $tag: expr, $args: expr, $slot: expr ) => {
                // Retrieve allocated preimage
                let preimg = bound_allocations.get_many_ptr($args)?;

                // Retrieve the preallocated preimage and image for this slot
                let (slot_preimg, slot_img_hash) = match $slot {
                    SlotType::Hash2 => &advices.hash2[slot_pos.consume_hash2()],
                    SlotType::Hash3 => &advices.hash3[slot_pos.consume_hash3()],
                    SlotType::Hash4 => &advices.hash4[slot_pos.consume_hash4()],
                    _ => panic!("Invalid slot type for hash_helper macro"),
                };

                // For each component of the preimage, add implication constraints
                // for its tag and hash
                for (preimg_idx, (preimg_tag, preimg_hash)) in preimg.iter().enumerate() {
                    let ptr_idx = 2 * preimg_idx;
                    let slot_preimg_tag = Elt::from(slot_preimg[ptr_idx].clone());
                    let slot_preimg_hash = Elt::from(slot_preimg[ptr_idx + 1].clone());
                    implies_equal(
                        cs.namespace(|| format!("implies equal tag {preimg_idx}")),
                        not_dummy,
                        preimg_tag,
                        &slot_preimg_tag,
                    );
                    implies_equal(
                        cs.namespace(|| format!("implies equal hash {preimg_idx}")),
                        not_dummy,
                        preimg_hash,
                        &slot_preimg_hash,
                    );
                }

                // Allocate the image tag if it hasn't been allocated before,
                // create the full image pointer and add it to bound allocations
                let img_tag = Elt::Constant($tag.to_field());
                let img_hash = Elt::from(slot_img_hash.clone());
                let img_ptr = CircuitPtr::Ptr(img_tag, img_hash);
                bound_allocations.insert($tgt, img_ptr);
            };
        }
        macro_rules! unhash_helper {
            ( $tgt: expr, $arg: expr, $slot: expr ) => {
                // Retrieve allocated image
                let (_, img_hash) = bound_allocations.get_ptr($arg)?;

                // Retrieve the preallocated preimage and image for this slot
                let (slot_preimg, slot_img_hash) = match $slot {
                    SlotType::Hash2 => &advices.hash2[slot_pos.consume_hash2()],
                    SlotType::Hash3 => &advices.hash3[slot_pos.consume_hash3()],
                    SlotType::Hash4 => &advices.hash4[slot_pos.consume_hash4()],
                    _ => panic!("Invalid slot type for unhash_helper macro"),
                };

                // Add the implication constraint for the image
                let slot_img_hash = Elt::from(slot_img_hash.clone());
                implies_equal(
                    cs.namespace(|| "implies equal img hash"),
                    not_dummy,
                    img_hash,
                    &slot_img_hash,
                );

                // Retrieve preimage hashes and tags create the full preimage pointers
                // and add them to bound allocations
                for preimg_idx in 0..slot_preimg.len() / 2 {
                    let preimg_tag = Elt::from(slot_preimg[2 * preimg_idx].clone());
                    let preimg_hash = Elt::from(slot_preimg[2 * preimg_idx + 1].clone());
                    let preimg_ptr = CircuitPtr::Ptr(preimg_tag.clone(), preimg_hash.clone());
                    bound_allocations.insert($tgt[preimg_idx].clone(), preimg_ptr);
                }
            };
        }

        match op {
            Op::Hash2(img, tag, preimg) => {
                hash_helper!(img.clone(), tag, preimg, SlotType::Hash2);
            }
            Op::Hash3(img, tag, preimg) => {
                hash_helper!(img.clone(), tag, preimg, SlotType::Hash3);
            }
            Op::Hash4(img, tag, preimg) => {
                hash_helper!(img.clone(), tag, preimg, SlotType::Hash4);
            }
            Op::Unhash2(preimg, img) => {
                unhash_helper!(preimg, img, SlotType::Hash2);
            }
            Op::Unhash3(preimg, img) => {
                unhash_helper!(preimg, img, SlotType::Hash3);
            }
            Op::Unhash4(preimg, img) => {
                unhash_helper!(preimg, img, SlotType::Hash4);
            }
            Op::Call(out, func, inp) => {
                todo!()
            }
            Op::Null(tgt, tag) => {
                let ptr = CircuitPtr::Ptr(Elt::Constant(tag.to_field()), Elt::Constant(F::ZERO));
                bound_allocations.insert(tgt.clone(), ptr);
            }
            Op::Lit(tgt, lit) => {
                let lit_ptr = lit.to_ptr(store);
                let ptr = CircuitPtr::Ptr(
                    Elt::Constant(lit_ptr.tag().to_field()),
                    Elt::Constant(store.hash_ptr(&lit_ptr)?.hash),
                );
                bound_allocations.insert(tgt.clone(), ptr);
            }
            Op::Cast(tgt, tag, src) => {
                let (_, src_hash) = bound_allocations.get_ptr(src)?;
                let ptr = CircuitPtr::Ptr(Elt::Constant(tag.to_field()), src_hash.clone());
                bound_allocations.insert(tgt.clone(), ptr);
            }
            // TODO Operations on numbers/booleans should except numbers/booleans as variables
            // and should also return the appropriate type
            Op::EqTag(tgt, a, b) => {
                let (a_num, _) = bound_allocations.get_ptr(a)?;
                let (b_num, _) = bound_allocations.get_ptr(b)?;
                let eq = alloc_is_equal(cs.namespace(|| "equal tag"), a_num, b_num)?;
                let eq_num = boolean_to_elt::<F, CS>(&eq);
                let ptr = CircuitPtr::Ptr(Elt::Constant(Tag::Expr(Num).to_field()), eq_num.clone());
                bound_allocations.insert(tgt.clone(), ptr);
            }
            Op::EqVal(tgt, a, b) => {
                let (_, a_num) = bound_allocations.get_ptr(a)?;
                let (_, b_num) = bound_allocations.get_ptr(b)?;
                let eq = alloc_is_equal(cs.namespace(|| "equal val"), a_num, b_num)?;
                let eq_num = boolean_to_elt::<F, CS>(&eq);
                let ptr = CircuitPtr::Ptr(Elt::Constant(Tag::Expr(Num).to_field()), eq_num.clone());
                bound_allocations.insert(tgt.clone(), ptr);
            }
            Op::Add(tgt, a, b) => {
                let (_, a_num) = bound_allocations.get_ptr(a)?;
                let (_, b_num) = bound_allocations.get_ptr(b)?;
                let ptr = CircuitPtr::Ptr(
                    Elt::Constant(Tag::Expr(Num).to_field()),
                    a_num.add::<CS>(b_num),
                );
                bound_allocations.insert(tgt.clone(), ptr);
            }
            Op::Sub(tgt, a, b) => {
                let (_, a_num) = bound_allocations.get_ptr(a)?;
                let (_, b_num) = bound_allocations.get_ptr(b)?;
                let ptr = CircuitPtr::Ptr(
                    Elt::Constant(Tag::Expr(Num).to_field()),
                    a_num.sub::<CS>(b_num),
                );
                bound_allocations.insert(tgt.clone(), ptr);
            }
            Op::Mul(tgt, a, b) => {
                let (_, a_num) = bound_allocations.get_ptr(a)?;
                let (_, b_num) = bound_allocations.get_ptr(b)?;
                let ptr = CircuitPtr::Ptr(
                    Elt::Constant(Tag::Expr(Num).to_field()),
                    mul(cs.namespace(|| "mul"), a_num, b_num)?,
                );
                bound_allocations.insert(tgt.clone(), ptr);
            }
            Op::Div(tgt, a, b) => {
                let (_, a_num) = bound_allocations.get_ptr(a)?;
                let (_, b_num) = bound_allocations.get_ptr(b)?;
                let divisor = alloc_pick(
                    cs.namespace(|| "should divide"),
                    not_dummy,
                    b_num,
                    &Elt::Constant(F::ONE),
                )?;
                let ptr = CircuitPtr::Ptr(
                    Elt::Constant(Tag::Expr(Num).to_field()),
                    div(cs.namespace(|| "div"), a_num, &divisor)?,
                );
                bound_allocations.insert(tgt.clone(), ptr);
            }
            Op::Lt(tgt, a, b) => {
                let (_, a_num) = bound_allocations.get_ptr(a)?;
                let (_, b_num) = bound_allocations.get_ptr(b)?;
                let (preimg, lt) = &advices.less_than[slot_pos.consume_less_than()];
                implies_equal(
                    cs.namespace(|| "lt a"),
                    not_dummy,
                    a_num,
                    &Elt::from(preimg[0].clone()),
                );
                implies_equal(
                    cs.namespace(|| "lt b"),
                    not_dummy,
                    b_num,
                    &Elt::from(preimg[1].clone()),
                );
                // TODO Should return a Number instead of a Ptr
                let ptr = CircuitPtr::Ptr(
                    Elt::Constant(Tag::Expr(Num).to_field()),
                    Elt::from(lt.clone()),
                );
                bound_allocations.insert(tgt.clone(), ptr);
            }
            Op::Trunc(tgt, a, n) => {
                assert!(*n <= 64);
                let (_, a_num) = bound_allocations.get_ptr(a)?;
                let mut trunc_bits = elt_to_bits_le_strict(cs.namespace(|| "to bits le"), a_num)?;
                trunc_bits.truncate(*n as usize);
                let trunc = Elt::from(AllocatedNum::alloc(cs.namespace(|| "trunc"), || {
                    let b = if *n < 64 { (1 << *n) - 1 } else { u64::MAX };
                    a_num
                        .get_value()
                        .map(|a| F::from_u64(a.to_u64_unchecked() & b))
                        .ok_or(SynthesisError::AssignmentMissing)
                })?);
                enforce_pack(cs.namespace(|| "enforce trunc"), &trunc_bits, &trunc)?;
                let ptr = CircuitPtr::Ptr(Elt::Constant(Tag::Expr(Num).to_field()), trunc);
                bound_allocations.insert(tgt.clone(), ptr);
            }
            Op::DivRem64(tgt, a, b) => {
                let (_, a) = bound_allocations.get_ptr(a)?;
                let (_, b) = bound_allocations.get_ptr(b)?;
                let div_rem = a.get_value().and_then(|a| {
                    b.get_value().map(|b| {
                        if not_dummy.get_value().unwrap() {
                            let a = a.to_u64_unchecked();
                            let b = b.to_u64_unchecked();
                            (F::from_u64(a / b), F::from_u64(a % b))
                        } else {
                            (F::ZERO, *a)
                        }
                    })
                });
                let div = Elt::from(AllocatedNum::alloc(cs.namespace(|| "div"), || {
                    Ok(div_rem.unwrap().0)
                })?);
                let rem = Elt::from(AllocatedNum::alloc(cs.namespace(|| "rem"), || {
                    Ok(div_rem.unwrap().1)
                })?);
                let diff = b.sub::<CS>(&rem);
                implies_u64(cs.namespace(|| "div u64"), not_dummy, &div)?;
                implies_u64(cs.namespace(|| "rem u64"), not_dummy, &rem)?;
                implies_u64(cs.namespace(|| "diff u64"), not_dummy, &diff)?;
                cs.enforce(
                    || "euclid division",
                    |_| b.lc::<CS>(),
                    |_| div.lc::<CS>(),
                    // a - rem = b * div
                    |_| a.sub::<CS>(&rem).lc::<CS>(),
                );
                let num_tag = Elt::Constant(Tag::Expr(Num).to_field());
                let div_ptr = CircuitPtr::Ptr(num_tag.clone(), div);
                let rem_ptr = CircuitPtr::Ptr(num_tag, rem);
                bound_allocations.insert(tgt[0].clone(), div_ptr);
                bound_allocations.insert(tgt[1].clone(), rem_ptr);
            }
            Op::Emit(_) => (),
            Op::Hide(tgt, sec, pay) => {
                todo!()
            }
            Op::Open(sec, pay, comm) => {
                todo!()
            }
        }
    }

    match &block.ctrl {
        Ctrl::Return(return_vars) => {
            for (i, return_var) in return_vars.iter().enumerate() {
                let (tag, hash) = bound_allocations.get_ptr(return_var)?;
                let out_tag = Elt::from(outputs[2 * i].clone());
                let out_hash = Elt::from(outputs[2 * i + 1].clone());
                implies_equal(
                    cs.namespace(|| format!("return {i} tag")),
                    not_dummy,
                    tag,
                    &out_tag,
                );
                implies_equal(
                    cs.namespace(|| format!("return {i} hash")),
                    not_dummy,
                    hash,
                    &out_hash,
                );
            }
            Ok(())
        }
        Ctrl::IfEq(x, y, eq_block, else_block) => {
            let (_, x_hash) = bound_allocations.get_ptr(x)?;
            let (_, y_hash) = bound_allocations.get_ptr(y)?;
            let is_eq = alloc_is_equal(cs.namespace(|| "is equal"), x_hash, y_hash)?;
            let is_not_eq = is_eq.not();
            let not_dummy_eq = Boolean::and(cs.namespace(|| "not dummy equal"), &is_eq, not_dummy)?;
            let not_dummy_not_eq = Boolean::and(
                cs.namespace(|| "not dummy not equal"),
                &is_not_eq,
                not_dummy,
            )?;
            let mut branch_slot = *slot_pos;
            synthesize_func_aux(
                cs.namespace(|| "equal block"),
                eq_block,
                &not_dummy_eq,
                store,
                bound_allocations,
                outputs,
                &mut branch_slot,
                advices,
            )?;
            synthesize_func_aux(
                cs.namespace(|| "else block"),
                else_block,
                &not_dummy_not_eq,
                store,
                bound_allocations,
                outputs,
                slot_pos,
                advices,
            )?;
            *slot_pos = slot_pos.max(branch_slot);
            Ok(())
        }
        Ctrl::MatchTag(match_var, cases, def) => {
            let match_tag = bound_allocations.get_ptr(match_var)?.0.clone();
            let mut selector = Vec::with_capacity(cases.len() + usize::from(def.is_some()));
            let mut branch_slots = Vec::with_capacity(cases.len());
            for (tag, block) in cases {
                let matched = Boolean::Is(AllocatedBit::alloc(
                    cs.namespace(|| format!("{tag} allocated bit")),
                    not_dummy.get_value().and_then(|not_dummy| {
                        match_tag
                            .get_value()
                            .map(|val| not_dummy && *val == tag.to_field::<F>())
                    }),
                )?);
                implies_equal(
                    cs.namespace(|| format!("{tag} implies equal")),
                    &matched,
                    &match_tag,
                    &Elt::Constant(tag.to_field()),
                );
                selector.push(matched.clone());
                let mut branch_slot = *slot_pos;
                synthesize_func_aux(
                    cs.namespace(|| format!("{tag} block")),
                    block,
                    &matched,
                    store,
                    bound_allocations,
                    outputs,
                    &mut branch_slot,
                    advices,
                )?;
                branch_slots.push(branch_slot);
            }
            if let Some(def) = def {
                let matched = Boolean::Is(AllocatedBit::alloc(
                    cs.namespace(|| "_ allocated bit"),
                    selector.iter().fold(not_dummy.get_value(), |acc, b| {
                        acc.and_then(|acc| b.get_value().map(|b| acc && !b))
                    }),
                )?);
                for (tag, _) in cases {
                    implies_unequal(
                        cs.namespace(|| format!("{tag} implies unequal")),
                        &matched,
                        &match_tag,
                        &Elt::Constant(tag.to_field()),
                    )?;
                }
                selector.push(matched.clone());
                synthesize_func_aux(
                    cs.namespace(|| "_ block"),
                    def,
                    &matched,
                    store,
                    bound_allocations,
                    outputs,
                    slot_pos,
                    advices,
                )?;
            }
            // The number of slots the match used is the max number of slots of each branch
            *slot_pos = branch_slots
                .into_iter()
                .fold(*slot_pos, |acc, branch_slot| acc.max(branch_slot));
            implies_popcount(
                cs.namespace(|| "popcount"),
                not_dummy,
                &Elt::Constant(F::ONE),
                &selector,
            );
            Ok(())
        }
        Ctrl::MatchVal(match_var, cases, def) => {
            let match_lit = bound_allocations.get_ptr(match_var)?.1.clone();
            let mut selector = Vec::with_capacity(cases.len() + usize::from(def.is_some()));
            let mut branch_slots = Vec::with_capacity(cases.len());
            for (i, (lit, block)) in cases.iter().enumerate() {
                let lit_ptr = lit.to_ptr(store);
                let lit_hash = store.hash_ptr(&lit_ptr)?.hash;
                let matched = Boolean::Is(AllocatedBit::alloc(
                    cs.namespace(|| format!("{i} allocated bit")),
                    not_dummy.get_value().and_then(|not_dummy| {
                        match_lit
                            .get_value()
                            .map(|val| not_dummy && *val == lit_hash)
                    }),
                )?);
                implies_equal(
                    cs.namespace(|| format!("{i} implies equal")),
                    &matched,
                    &match_lit,
                    &Elt::Constant(lit_hash),
                );
                selector.push(matched.clone());
                let mut branch_slot = *slot_pos;
                synthesize_func_aux(
                    cs.namespace(|| format!("{i} block")),
                    block,
                    &matched,
                    store,
                    bound_allocations,
                    outputs,
                    &mut branch_slot,
                    advices,
                )?;
                branch_slots.push(branch_slot);
            }
            if let Some(def) = def {
                let matched = Boolean::Is(AllocatedBit::alloc(
                    cs.namespace(|| "_ allocated bit"),
                    selector.iter().fold(not_dummy.get_value(), |acc, b| {
                        acc.and_then(|acc| b.get_value().map(|b| acc && !b))
                    }),
                )?);
                for (i, (lit, _)) in cases.iter().enumerate() {
                    let lit_ptr = lit.to_ptr(store);
                    let lit_hash = store.hash_ptr(&lit_ptr)?.hash;
                    implies_unequal(
                        cs.namespace(|| format!("{i} implies unequal")),
                        &matched,
                        &match_lit,
                        &Elt::Constant(lit_hash),
                    )?;
                }
                selector.push(matched.clone());
                synthesize_func_aux(
                    cs.namespace(|| "_ block"),
                    def,
                    &matched,
                    store,
                    bound_allocations,
                    outputs,
                    slot_pos,
                    advices,
                )?;
            }
            // The number of slots the match used is the max number of slots of each branch
            *slot_pos = branch_slots
                .into_iter()
                .fold(*slot_pos, |acc, branch_slot| acc.max(branch_slot));

            implies_popcount(
                cs.namespace(|| "popcount"),
                not_dummy,
                &Elt::Constant(F::ONE),
                &selector,
            );
            Ok(())
        }
    }
}

#[derive(Default)]
pub(crate) struct Advices<F: LurkField> {
    hash2: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
    hash3: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
    hash4: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
    commitment: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
    less_than: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
    call_output: VecDeque<Vec<Ptr<F>>>,
}

fn build_func_advices<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    func: &Func,
    store: &mut Store<F>,
    frame: &Frame<F>,
) -> Result<Advices<F>> {
    // Slots are constrained by their usage inside the function body. The ones
    // not used in throughout the concrete path are effectively unconstrained,
    // that's why they are filled with dummies
    let hash2 = alloc_slots(
        cs.namespace(|| "hash2 slots"),
        &frame.preimages.hash2,
        SlotType::Hash2,
        func.slot.hash2,
        store,
    )?;

    let hash3 = alloc_slots(
        cs.namespace(|| "hash3 slots"),
        &frame.preimages.hash3,
        SlotType::Hash3,
        func.slot.hash3,
        store,
    )?;

    let hash4 = alloc_slots(
        cs.namespace(|| "hash4 slots"),
        &frame.preimages.hash4,
        SlotType::Hash4,
        func.slot.hash4,
        store,
    )?;

    let commitment = alloc_slots(
        cs.namespace(|| "commitment slots"),
        &frame.preimages.commitment,
        SlotType::Commitment,
        func.slot.commitment,
        store,
    )?;

    let less_than = alloc_slots(
        cs.namespace(|| "lt slots"),
        &frame.preimages.less_than,
        SlotType::LessThan,
        func.slot.less_than,
        store,
    )?;

    let call_output = frame.preimages.call_outputs.clone();

    Ok(Advices {
        hash2,
        hash3,
        hash4,
        commitment,
        less_than,
        call_output,
    })
}

/// Allocates unconstrained slots
fn alloc_slots<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    preimg_data: &[Option<PreimageData<F>>],
    slot_type: SlotType,
    num_slots: usize,
    store: &mut Store<F>,
) -> Result<Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>> {
    assert!(
        preimg_data.len() == num_slots,
        "collected preimages not equal to the number of available slots"
    );

    let mut preallocations = Vec::with_capacity(num_slots);

    // We must perform the allocations for the slots containing data collected
    // by the interpreter. The `None` cases must be filled with dummy values
    for (slot_idx, maybe_preimg_data) in preimg_data.iter().enumerate() {
        if let Some(preimg_data) = maybe_preimg_data {
            let slot = Slot {
                idx: slot_idx,
                typ: slot_type,
            };

            // Allocate the preimage because the image depends on it
            let mut preallocated_preimg = Vec::with_capacity(slot_type.preimg_size());

            match preimg_data {
                PreimageData::PtrVec(ptr_vec) => {
                    let mut component_idx = 0;
                    for ptr in ptr_vec {
                        let z_ptr = store.hash_ptr(ptr)?;

                        // allocate pointer tag
                        preallocated_preimg.push(AllocatedNum::alloc(
                            cs.namespace(|| format!("component {component_idx} for slot {slot}")),
                            || Ok(z_ptr.tag.to_field()),
                        )?);

                        component_idx += 1;

                        // allocate pointer hash
                        preallocated_preimg.push(AllocatedNum::alloc(
                            cs.namespace(|| format!("component {component_idx} for slot {slot}")),
                            || Ok(z_ptr.hash),
                        )?);

                        component_idx += 1;
                    }
                }
                PreimageData::FPtr(f, ptr) => {
                    let z_ptr = store.hash_ptr(ptr)?;
                    // allocate first component
                    preallocated_preimg.push(AllocatedNum::alloc(
                        cs.namespace(|| format!("component 0 for slot {slot}")),
                        || Ok(*f),
                    )?);
                    // allocate second component
                    preallocated_preimg.push(AllocatedNum::alloc(
                        cs.namespace(|| format!("component 1 for slot {slot}")),
                        || Ok(z_ptr.tag.to_field()),
                    )?);
                    // allocate third component
                    preallocated_preimg.push(AllocatedNum::alloc(
                        cs.namespace(|| format!("component 2 for slot {slot}")),
                        || Ok(z_ptr.hash),
                    )?);
                }
                PreimageData::FPair(a, b) => {
                    // allocate first component
                    preallocated_preimg.push(AllocatedNum::alloc(
                        cs.namespace(|| format!("component 0 for slot {slot}")),
                        || Ok(*a),
                    )?);

                    // allocate second component
                    preallocated_preimg.push(AllocatedNum::alloc(
                        cs.namespace(|| format!("component 1 for slot {slot}")),
                        || Ok(*b),
                    )?);
                }
            }

            // Allocate the image by calling the arithmetic function according
            // to the slot type
            let preallocated_img = alloc_img(
                cs.namespace(|| format!("image for slot {slot}")),
                &slot,
                preallocated_preimg.clone(),
                store,
            )?;

            preallocations.push((preallocated_preimg, preallocated_img));
        } else {
            let slot = Slot {
                idx: slot_idx,
                typ: slot_type,
            };
            let preallocated_preimg: Vec<_> = (0..slot_type.preimg_size())
                .map(|component_idx| {
                    AllocatedNum::alloc(
                        cs.namespace(|| format!("component {component_idx} for slot {slot}")),
                        || Ok(F::ZERO),
                    )
                })
                .collect::<Result<_, _>>()?;

            let preallocated_img = alloc_img(
                cs.namespace(|| format!("image for slot {slot}")),
                &slot,
                preallocated_preimg.clone(),
                store,
            )?;

            preallocations.push((preallocated_preimg, preallocated_img));
        }
    }

    Ok(preallocations)
}

fn alloc_img<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    slot: &Slot,
    preimg: Vec<AllocatedNum<F>>,
    store: &mut Store<F>,
) -> Result<AllocatedNum<F>> {
    let img = {
        match slot.typ {
            SlotType::Hash2 => hash_poseidon(cs, preimg, store.poseidon_cache.constants.c4())?,
            SlotType::Hash3 => hash_poseidon(cs, preimg, store.poseidon_cache.constants.c6())?,
            SlotType::Hash4 => hash_poseidon(cs, preimg, store.poseidon_cache.constants.c8())?,
            SlotType::Commitment => hash_poseidon(cs, preimg, store.poseidon_cache.constants.c3())?,
            SlotType::LessThan => {
                // TODO return `Elt` instead of `AllocatedNum`
                // Maybe `preimg` should also be `Elt`
                use crate::circuit::gadgets::constraints::boolean_to_num;
                let a_num = Elt::from(preimg[0].clone());
                let b_num = Elt::from(preimg[1].clone());
                let diff = a_num.sub::<CS>(&b_num);
                let diff_is_negative = alloc_is_negative(cs.namespace(|| "is negative"), &diff)?;
                boolean_to_num(cs.namespace(|| "boolean to num"), &diff_is_negative)?
            }
        }
    };
    Ok(img)
}
