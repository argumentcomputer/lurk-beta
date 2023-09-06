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
    synthesize_func_aux(
        cs,
        &func.body,
        &Boolean::Constant(true),
        store,
        bound_allocations,
        &outputs,
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
) -> Result<()> {
    for op in &block.ops {
        match op {
            Op::Call(out, func, inp) => {
                todo!()
            }
            Op::Hash2(img, tag, preimg) => {
                todo!()
            }
            Op::Hash3(img, tag, preimg) => {
                todo!()
            }
            Op::Hash4(img, tag, preimg) => {
                todo!()
            }
            Op::Unhash2(preimg, img) => {
                todo!()
            }
            Op::Unhash3(preimg, img) => {
                todo!()
            }
            Op::Unhash4(preimg, img) => {
                todo!()
            }
            Op::Null(tgt, tag) => {
                todo!()
            }
            Op::Lit(tgt, lit) => {
                todo!()
            }
            Op::Cast(tgt, tag, src) => {
                todo!()
            }
            Op::EqTag(tgt, a, b) => {
                todo!()
            }
            Op::EqVal(tgt, a, b) => {
                todo!()
            }
            Op::Add(tgt, a, b) => {
                todo!()
            }
            Op::Sub(tgt, a, b) => {
                todo!()
            }
            Op::Mul(tgt, a, b) => {
                todo!()
            }
            Op::Div(tgt, a, b) => {
                todo!()
            }
            Op::Lt(tgt, a, b) => {
                todo!()
            }
            Op::Trunc(tgt, a, n) => {
                todo!()
            }
            Op::DivRem64(tgt, a, b) => {
                todo!()
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
            let not_dummy_eq =
                Boolean::and(cs.namespace(|| "not dummy equal"), &is_eq, not_dummy)?;
            let not_dummy_not_eq = Boolean::and(
                cs.namespace(|| "not dummy not equal"),
                &is_not_eq,
                not_dummy,
            )?;
            synthesize_func_aux(
                cs.namespace(|| "equal block"),
                eq_block,
                &not_dummy_eq,
                store,
                bound_allocations,
                outputs,
            )?;
            synthesize_func_aux(
                cs.namespace(|| "else block"),
                else_block,
                &not_dummy_not_eq,
                store,
                bound_allocations,
                outputs,
            )?;
            Ok(())
        }
        Ctrl::MatchTag(match_var, cases, def) => {
            let match_tag = bound_allocations.get_ptr(match_var)?.0.clone();
            let mut selector = Vec::with_capacity(cases.len() + usize::from(def.is_some()));
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
                synthesize_func_aux(
                    cs.namespace(|| format!("{tag} block")),
                    block,
                    &matched,
                    store,
                    bound_allocations,
                    outputs,
                )?;
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
                )?;
            }
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
                synthesize_func_aux(
                    cs.namespace(|| format!("{i} block")),
                    block,
                    &matched,
                    store,
                    bound_allocations,
                    outputs,
                )?;
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
                )?;
            }
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
