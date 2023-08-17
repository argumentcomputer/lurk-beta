//! ## Constraint system for LEM
//!
//! This module implements the generation of bellperson constraints for LEM, such
//! that it can be used with Nova folding to prove evaluations of Lurk expressions.
//!
//! ### "Concrete" and "virtual" paths
//!
//! Control statements such as matches introduce branching, meaning execution can
//! follow different paths depending on a value. The real path of execution for
//! a particular instance we call the *concrete path*. The other paths which are
//! not followed we call *virtual paths*. A mechanism to "relax" the constraints
//! for the virtual paths while also properly enforcing the correctness for what
//! happens on the concrete path is thus needed.
//!
//! We do that by using implication gadgets. An implication of the form `A → B`
//! is trivially true if `A` is false. But if `A` is true, then the implication
//! is true iff `B` is true. In other words, `B` is irrelevant if `A` is false,
//! which is the behavior we want for the virtual paths.
//!
//! With that in mind, we can keep track of booleans that tell us whether we're
//! on a concrete or a virtual path and use such booleans as the premises to build
//! the constraints we care about with implication gadgets.

use std::collections::{HashMap, HashSet, VecDeque};

use anyhow::{Context, Result};
use bellpepper_core::{
    ConstraintSystem,
    {
        boolean::{AllocatedBit, Boolean},
        num::AllocatedNum,
    },
};

use crate::circuit::gadgets::{
    constraints::{
        add, alloc_equal, alloc_equal_const, and, enforce_selector_with_premise, implies_equal,
        mul, sub,
    },
    data::{allocate_constant, hash_poseidon},
    pointer::AllocatedPtr,
};

use crate::field::{FWrap, LurkField};
use crate::tag::ExprTag::*;

use super::{
    interpreter::Frame,
    pointers::{Ptr, ZPtr},
    slot::*,
    store::Store,
    var_map::VarMap,
    Block, Ctrl, Func, Op, Tag, Var,
};

/// Manages global allocations for constants in a constraint system
#[derive(Default)]
pub(crate) struct GlobalAllocator<F: LurkField>(HashMap<FWrap<F>, AllocatedNum<F>>);

#[inline]
fn allocate_num<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    namespace: &str,
    value: F,
) -> Result<AllocatedNum<F>> {
    AllocatedNum::alloc(cs.namespace(|| namespace), || Ok(value))
        .with_context(|| format!("allocation for '{namespace}' failed"))
}

#[inline]
fn allocate_const<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    namespace: &str,
    value: F,
) -> Result<AllocatedNum<F>> {
    allocate_constant(&mut cs.namespace(|| namespace), value)
        .with_context(|| format!("allocation for '{namespace}' failed"))
}

impl<F: LurkField> GlobalAllocator<F> {
    /// Checks if the allocation for a numeric variable has already been cached.
    /// If so, return the cached allocation variable. Allocate as a constant,
    /// cache and return otherwise.
    pub(crate) fn get_or_alloc_const<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        f: F,
    ) -> Result<AllocatedNum<F>> {
        let wrap = FWrap(f);
        match self.0.get(&wrap) {
            Some(allocated_num) => Ok(allocated_num.to_owned()),
            None => {
                let allocated_num =
                    allocate_const(cs, &format!("allocate constant {}", f.hex_digits()), f)?;
                self.0.insert(wrap, allocated_num.clone());
                Ok(allocated_num)
            }
        }
    }
}

type BoundAllocations<F> = VarMap<AllocatedPtr<F>>;

impl Func {
    /// Allocates an unconstrained pointer
    fn allocate_ptr<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        z_ptr: &ZPtr<F>,
        var: &Var,
        bound_allocations: &mut BoundAllocations<F>,
    ) -> Result<AllocatedPtr<F>> {
        let allocated_tag =
            allocate_num(cs, &format!("allocate {var}'s tag"), z_ptr.tag.to_field())?;
        let allocated_hash = allocate_num(cs, &format!("allocate {var}'s hash"), z_ptr.hash)?;
        let allocated_ptr = AllocatedPtr::from_parts(allocated_tag, allocated_hash);
        bound_allocations.insert(var.clone(), allocated_ptr.clone());
        Ok(allocated_ptr)
    }

    /// Allocates an unconstrained pointer for each input of the frame
    fn allocate_input<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &mut Store<F>,
        frame: &Frame<F>,
        bound_allocations: &mut BoundAllocations<F>,
    ) -> Result<()> {
        for (i, ptr) in frame.input.iter().enumerate() {
            let param = &self.input_params[i];
            Self::allocate_ptr(cs, &store.hash_ptr(ptr)?, param, bound_allocations)?;
        }
        Ok(())
    }

    /// Allocates an unconstrained pointer for each output of the frame
    fn allocate_output<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        store: &mut Store<F>,
        frame: &Frame<F>,
        bound_allocations: &mut BoundAllocations<F>,
    ) -> Result<Vec<AllocatedPtr<F>>> {
        frame
            .output
            .iter()
            .enumerate()
            .map(|(i, ptr)| {
                Self::allocate_ptr(
                    cs,
                    &store.hash_ptr(ptr)?,
                    &Var(format!("output[{}]", i).into()),
                    bound_allocations,
                )
            })
            .collect::<Result<_>>()
    }

    #[inline]
    fn allocate_preimg_component_for_slot<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        slot: &Slot,
        component_idx: usize,
        value: F,
    ) -> Result<AllocatedNum<F>> {
        allocate_num(
            cs,
            &format!("component {component_idx} for slot {slot}"),
            value,
        )
    }

    fn allocate_img_for_slot<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        slot: &Slot,
        preallocated_preimg: Vec<AllocatedNum<F>>,
        store: &mut Store<F>,
    ) -> Result<AllocatedNum<F>> {
        let cs = &mut cs.namespace(|| format!("poseidon for slot {slot}"));
        let preallocated_img = {
            match slot.typ {
                SlotType::Hash2 => {
                    hash_poseidon(cs, preallocated_preimg, store.poseidon_cache.constants.c4())?
                }
                SlotType::Hash3 => {
                    hash_poseidon(cs, preallocated_preimg, store.poseidon_cache.constants.c6())?
                }
                SlotType::Hash4 => {
                    hash_poseidon(cs, preallocated_preimg, store.poseidon_cache.constants.c8())?
                }
            }
        };
        Ok(preallocated_img)
    }

    /// Allocates unconstrained slots
    fn allocate_slots<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        preimgs: &[Option<Vec<Ptr<F>>>],
        slot_type: SlotType,
        num_slots: usize,
        store: &mut Store<F>,
    ) -> Result<Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>> {
        assert!(
            preimgs.len() == num_slots,
            "collected preimages not equal to the number of available slots"
        );

        let mut preallocations = Vec::with_capacity(num_slots);

        // We must perform the allocations for the slots containing data collected
        // by the interpreter. The `None` cases must be filled with dummy values
        for (slot_idx, maybe_preimg) in preimgs.iter().enumerate() {
            if let Some(preimg) = maybe_preimg {
                let slot = Slot {
                    idx: slot_idx,
                    typ: slot_type,
                };
                // Allocate the preimage because the image depends on it
                let mut preallocated_preimg = Vec::with_capacity(2 * preimg.len());

                let mut component_idx = 0;
                for ptr in preimg {
                    let z_ptr = store.hash_ptr(ptr)?;

                    // allocate pointer tag
                    preallocated_preimg.push(Self::allocate_preimg_component_for_slot(
                        cs,
                        &slot,
                        component_idx,
                        z_ptr.tag.to_field(),
                    )?);

                    component_idx += 1;

                    // allocate pointer hash
                    preallocated_preimg.push(Self::allocate_preimg_component_for_slot(
                        cs,
                        &slot,
                        component_idx,
                        z_ptr.hash,
                    )?);

                    component_idx += 1;
                }

                // Allocate the image by calling the arithmetic function according
                // to the slot type
                let preallocated_img =
                    Self::allocate_img_for_slot(cs, &slot, preallocated_preimg.clone(), store)?;

                preallocations.push((preallocated_preimg, preallocated_img));
            } else {
                let slot = Slot {
                    idx: slot_idx,
                    typ: slot_type,
                };
                let preallocated_preimg: Vec<_> = (0..slot_type.preimg_size())
                    .map(|component_idx| {
                        Self::allocate_preimg_component_for_slot(cs, &slot, component_idx, F::ZERO)
                    })
                    .collect::<Result<_, _>>()?;

                let preallocated_img =
                    Self::allocate_img_for_slot(cs, &slot, preallocated_preimg.clone(), store)?;

                preallocations.push((preallocated_preimg, preallocated_img));
            }
        }

        Ok(preallocations)
    }

    /// Create R1CS constraints for a LEM function given an evaluation frame. This
    /// function implements the STEP 3 mentioned above.
    ///
    /// Regarding the slot optimizations, STEP 3 uses information gathered during
    /// STEPs 1 and 2. So we proceed by first allocating preimages and images for
    /// each slot and then, as we traverse the function, we add constraints to make
    /// sure that the witness satisfies the arithmetic equations for the
    /// corresponding slots.
    pub fn synthesize<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &mut Store<F>,
        frame: &Frame<F>,
    ) -> Result<()> {
        let mut global_allocator = GlobalAllocator::default();
        let mut bound_allocations = BoundAllocations::new();

        // Inputs are constrained by their usage inside the function body
        self.allocate_input(cs, store, frame, &mut bound_allocations)?;
        // Outputs are constrained by the return statement. All functions return
        let preallocated_outputs = Func::allocate_output(cs, store, frame, &mut bound_allocations)?;

        // Slots are constrained by their usage inside the function body. The ones
        // not used in throughout the concrete path are effectively unconstrained,
        // that's why they are filled with dummies
        let preallocated_hash2_slots = Func::allocate_slots(
            cs,
            &frame.preimages.hash2_ptrs,
            SlotType::Hash2,
            self.slot.hash2,
            store,
        )?;

        let preallocated_hash3_slots = Func::allocate_slots(
            cs,
            &frame.preimages.hash3_ptrs,
            SlotType::Hash3,
            self.slot.hash3,
            store,
        )?;

        let preallocated_hash4_slots = Func::allocate_slots(
            cs,
            &frame.preimages.hash4_ptrs,
            SlotType::Hash4,
            self.slot.hash4,
            store,
        )?;

        struct Globals<'a, F: LurkField> {
            store: &'a mut Store<F>,
            global_allocator: &'a mut GlobalAllocator<F>,
            preallocated_hash2_slots: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
            preallocated_hash3_slots: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
            preallocated_hash4_slots: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
            call_outputs: VecDeque<Vec<Ptr<F>>>,
            call_count: usize,
        }

        fn recurse<F: LurkField, CS: ConstraintSystem<F>>(
            cs: &mut CS,
            block: &Block,
            not_dummy: &Boolean,
            next_slot: &mut SlotsCounter,
            bound_allocations: &mut BoundAllocations<F>,
            preallocated_outputs: &Vec<AllocatedPtr<F>>,
            g: &mut Globals<'_, F>,
        ) -> Result<()> {
            for op in &block.ops {
                macro_rules! hash_helper {
                    ( $img: expr, $tag: expr, $preimg: expr, $slot: expr ) => {
                        // Retrieve allocated preimage
                        let allocated_preimg = bound_allocations.get_many($preimg)?;

                        // Retrieve the preallocated preimage and image for this slot
                        let (preallocated_preimg, preallocated_img_hash) = match $slot {
                            SlotType::Hash2 => {
                                &g.preallocated_hash2_slots[next_slot.consume_hash2()]
                            }
                            SlotType::Hash3 => {
                                &g.preallocated_hash3_slots[next_slot.consume_hash3()]
                            }
                            SlotType::Hash4 => {
                                &g.preallocated_hash4_slots[next_slot.consume_hash4()]
                            }
                        };

                        // For each component of the preimage, add implication constraints
                        // for its tag and hash
                        for (i, allocated_ptr) in allocated_preimg.iter().enumerate() {
                            let var = &$preimg[i];
                            let ptr_idx = 2 * i;
                            implies_equal(
                                &mut cs.namespace(|| {
                                    format!(
                                        "implies equal for {var}'s tag (LEMOP {:?}, pos {i})",
                                        &op
                                    )
                                }),
                                not_dummy,
                                allocated_ptr.tag(),
                                &preallocated_preimg[ptr_idx], // tag index
                            )?;
                            implies_equal(
                                &mut cs.namespace(|| {
                                    format!(
                                        "implies equal for {var}'s hash (LEMOP {:?}, pos {i})",
                                        &op
                                    )
                                }),
                                not_dummy,
                                allocated_ptr.hash(),
                                &preallocated_preimg[ptr_idx + 1], // hash index
                            )?;
                        }

                        // Allocate the image tag if it hasn't been allocated before,
                        // create the full image pointer and add it to bound allocations
                        let img_tag = g.global_allocator.get_or_alloc_const(cs, $tag.to_field())?;
                        let img_hash = preallocated_img_hash.clone();
                        let img_ptr = AllocatedPtr::from_parts(img_tag, img_hash);
                        bound_allocations.insert($img, img_ptr);
                    };
                }

                macro_rules! unhash_helper {
                    ( $preimg: expr, $img: expr, $slot: expr ) => {
                        // Retrieve allocated image
                        let allocated_img = bound_allocations.get($img)?;

                        // Retrieve the preallocated preimage and image for this slot
                        let (preallocated_preimg, preallocated_img) = match $slot {
                            SlotType::Hash2 => {
                                &g.preallocated_hash2_slots[next_slot.consume_hash2()]
                            }
                            SlotType::Hash3 => {
                                &g.preallocated_hash3_slots[next_slot.consume_hash3()]
                            }
                            SlotType::Hash4 => {
                                &g.preallocated_hash4_slots[next_slot.consume_hash4()]
                            }
                        };

                        // Add the implication constraint for the image
                        implies_equal(
                            &mut cs.namespace(|| {
                                format!("implies equal for {}'s hash (LEMOP {:?})", $img, &op)
                            }),
                            not_dummy,
                            allocated_img.hash(),
                            &preallocated_img,
                        )?;

                        // Retrieve preimage hashes and tags create the full preimage pointers
                        // and add them to bound allocations
                        for i in 0..preallocated_preimg.len() / 2 {
                            let preimg_tag = &preallocated_preimg[2 * i];
                            let preimg_hash = &preallocated_preimg[2 * i + 1];
                            let preimg_ptr =
                                AllocatedPtr::from_parts(preimg_tag.clone(), preimg_hash.clone());
                            bound_allocations.insert($preimg[i].clone(), preimg_ptr);
                        }
                    };
                }

                match op {
                    Op::Call(out, func, inp) => {
                        // Allocate the output pointers that the `func` will return to.
                        // These should be unconstrained as of yet, and will be constrained
                        // by the return statements inside `func`.
                        // Note that, because there's currently no way of deferring giving
                        // a value to the allocated nums to be filled later, we must either
                        // add the results of the call to the witness, or recompute them.
                        let output_vals = if not_dummy.get_value().unwrap() {
                            g.call_outputs.pop_front().unwrap()
                        } else {
                            let dummy = Ptr::Leaf(Tag::Expr(Nil), F::ZERO);
                            (0..out.len()).map(|_| dummy).collect()
                        };
                        assert_eq!(output_vals.len(), out.len());
                        let mut output_ptrs = Vec::with_capacity(out.len());
                        for (ptr, var) in output_vals.iter().zip(out.iter()) {
                            let zptr = &g.store.hash_ptr(ptr)?;
                            output_ptrs.push(Func::allocate_ptr(cs, zptr, var, bound_allocations)?);
                        }
                        // Get the pointers for the input, i.e. the arguments
                        let args = bound_allocations.get_many_cloned(inp)?;
                        // These are the input parameters (formal variables)
                        let param_list = func.input_params.iter();
                        // Now we bind the `Func`'s input parameters to the arguments in the call.
                        param_list.zip(args.into_iter()).for_each(|(param, arg)| {
                            bound_allocations.insert(param.clone(), arg);
                        });
                        // Finally, we synthesize the circuit for the function body
                        g.call_count += 1;
                        recurse(
                            &mut cs.namespace(|| format!("Call {}", g.call_count)),
                            &func.body,
                            not_dummy,
                            next_slot,
                            bound_allocations,
                            &output_ptrs,
                            g,
                        )?;
                    }
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
                    Op::Null(tgt, tag) => {
                        let tag = g.global_allocator.get_or_alloc_const(cs, tag.to_field())?;
                        let zero = g.global_allocator.get_or_alloc_const(cs, F::ZERO)?;
                        let allocated_ptr = AllocatedPtr::from_parts(tag, zero);
                        bound_allocations.insert(tgt.clone(), allocated_ptr);
                    }
                    Op::Lit(tgt, lit) => {
                        let lit_ptr = lit.to_ptr(g.store);
                        let lit_tag = lit_ptr.tag().to_field();
                        let lit_hash = g.store.hash_ptr(&lit_ptr)?.hash;
                        let allocated_tag = g.global_allocator.get_or_alloc_const(cs, lit_tag)?;
                        let allocated_hash = g.global_allocator.get_or_alloc_const(cs, lit_hash)?;
                        let allocated_ptr = AllocatedPtr::from_parts(allocated_tag, allocated_hash);
                        bound_allocations.insert(tgt.clone(), allocated_ptr);
                    }
                    Op::Cast(tgt, tag, src) => {
                        let src = bound_allocations.get(src)?;
                        let tag = g.global_allocator.get_or_alloc_const(cs, tag.to_field())?;
                        let allocated_ptr = AllocatedPtr::from_parts(tag, src.hash().clone());
                        bound_allocations.insert(tgt.clone(), allocated_ptr);
                    }
                    Op::Add(tgt, a, b) => {
                        let a = bound_allocations.get(a)?;
                        let b = bound_allocations.get(b)?;
                        // TODO check that the tags are correct
                        let a_num = a.hash();
                        let b_num = b.hash();
                        let c_num = add(&mut cs.namespace(|| "add"), a_num, b_num)?;
                        let tag = g
                            .global_allocator
                            .get_or_alloc_const(cs, Tag::Expr(Num).to_field())?;
                        let c = AllocatedPtr::from_parts(tag, c_num);
                        bound_allocations.insert(tgt.clone(), c);
                    }
                    Op::Sub(tgt, a, b) => {
                        let a = bound_allocations.get(a)?;
                        let b = bound_allocations.get(b)?;
                        // TODO check that the tags are correct
                        let a_num = a.hash();
                        let b_num = b.hash();
                        let c_num = sub(&mut cs.namespace(|| "sub"), a_num, b_num)?;
                        let tag = g
                            .global_allocator
                            .get_or_alloc_const(cs, Tag::Expr(Num).to_field())?;
                        let c = AllocatedPtr::from_parts(tag, c_num);
                        bound_allocations.insert(tgt.clone(), c);
                    }
                    Op::Mul(tgt, a, b) => {
                        let a = bound_allocations.get(a)?;
                        let b = bound_allocations.get(b)?;
                        // TODO check that the tags are correct
                        let a_num = a.hash();
                        let b_num = b.hash();
                        let c_num = mul(&mut cs.namespace(|| "mul"), a_num, b_num)?;
                        let tag = g
                            .global_allocator
                            .get_or_alloc_const(cs, Tag::Expr(Num).to_field())?;
                        let c = AllocatedPtr::from_parts(tag, c_num);
                        bound_allocations.insert(tgt.clone(), c);
                    }
                    Op::Div(_tgt, _a, _b) => {
                        // TODO
                    }
                    Op::Emit(_) => (),
                    Op::Hide(tgt, _sec, _pay) => {
                        // TODO
                        let allocated_ptr = AllocatedPtr::from_parts(
                            g.global_allocator.get_or_alloc_const(cs, F::ZERO)?,
                            g.global_allocator.get_or_alloc_const(cs, F::ZERO)?,
                        );
                        bound_allocations.insert(tgt.clone(), allocated_ptr);
                    }
                    Op::Open(pay, sec, _comm_or_num) => {
                        // TODO
                        let allocated_ptr = AllocatedPtr::from_parts(
                            g.global_allocator.get_or_alloc_const(cs, F::ZERO)?,
                            g.global_allocator.get_or_alloc_const(cs, F::ZERO)?,
                        );
                        bound_allocations.insert(pay.clone(), allocated_ptr.clone());
                        bound_allocations.insert(sec.clone(), allocated_ptr);
                    }
                }
            }

            match &block.ctrl {
                Ctrl::Return(return_vars) => {
                    for (i, return_var) in return_vars.iter().enumerate() {
                        let allocated_ptr = bound_allocations.get(return_var)?;

                        allocated_ptr
                            .implies_ptr_equal(
                                &mut cs.namespace(|| {
                                    format!("implies_ptr_equal {return_var} (return_var {i})")
                                }),
                                not_dummy,
                                &preallocated_outputs[i],
                            )
                            .with_context(|| "couldn't constrain `implies_ptr_equal`")?;
                    }
                    Ok(())
                }
                Ctrl::IfEq(x, y, eq_block, else_block) => {
                    let x = bound_allocations.get(x)?.hash();
                    let y = bound_allocations.get(y)?.hash();
                    // TODO should we check whether the tags are equal too?
                    let eq = alloc_equal(&mut cs.namespace(|| "if_eq.alloc_equal"), x, y)?;
                    let not_eq = eq.not();
                    // TODO is this the most efficient way of doing if statements?
                    let not_dummy_and_eq = and(&mut cs.namespace(|| "if_eq.and"), not_dummy, &eq)?;
                    let not_dummy_and_not_eq =
                        and(&mut cs.namespace(|| "if_eq.and.2"), not_dummy, &not_eq)?;

                    let mut branch_slot = *next_slot;
                    recurse(
                        &mut cs.namespace(|| "if_eq.true"),
                        eq_block,
                        &not_dummy_and_eq,
                        &mut branch_slot,
                        bound_allocations,
                        preallocated_outputs,
                        g,
                    )?;
                    recurse(
                        &mut cs.namespace(|| "if_eq.false"),
                        else_block,
                        &not_dummy_and_not_eq,
                        next_slot,
                        bound_allocations,
                        preallocated_outputs,
                        g,
                    )?;
                    *next_slot = next_slot.max(branch_slot);
                    Ok(())
                }
                Ctrl::MatchTag(match_var, cases, def) => {
                    let allocated_match_tag = bound_allocations.get(match_var)?.tag().clone();
                    let mut selector = Vec::with_capacity(cases.len() + 1);
                    let mut branch_slots = Vec::with_capacity(cases.len());
                    for (tag, block) in cases {
                        let allocated_has_match = alloc_equal_const(
                            &mut cs.namespace(|| format!("{tag}.alloc_equal_const")),
                            &allocated_match_tag,
                            tag.to_field::<F>(),
                        )
                        .with_context(|| "couldn't allocate equal const")?;

                        let not_dummy_and_has_match = and(
                            &mut cs.namespace(|| format!("{tag}.and")),
                            not_dummy,
                            &allocated_has_match,
                        )
                        .with_context(|| "failed to constrain `and`")?;

                        selector.push(allocated_has_match);

                        let mut branch_slot = *next_slot;
                        recurse(
                            &mut cs.namespace(|| format!("{}", tag)),
                            block,
                            &not_dummy_and_has_match,
                            &mut branch_slot,
                            bound_allocations,
                            preallocated_outputs,
                            g,
                        )?;
                        branch_slots.push(branch_slot);
                    }

                    match def {
                        Some(def) => {
                            let default = selector.iter().all(|b| !b.get_value().unwrap());
                            let allocated_has_match = Boolean::Is(AllocatedBit::alloc(
                                &mut cs.namespace(|| "_.allocated_bit"),
                                Some(default),
                            )?);

                            let not_dummy_and_has_match = and(
                                &mut cs.namespace(|| "_.and"),
                                not_dummy,
                                &allocated_has_match,
                            )
                            .with_context(|| "failed to constrain `and`")?;

                            selector.push(allocated_has_match);

                            recurse(
                                &mut cs.namespace(|| "_"),
                                def,
                                &not_dummy_and_has_match,
                                next_slot,
                                bound_allocations,
                                preallocated_outputs,
                                g,
                            )?;
                        }
                        None => (),
                    }

                    // The number of slots the match used is the max number of slots of each branch
                    *next_slot = branch_slots
                        .into_iter()
                        .fold(*next_slot, |acc, branch_slot| acc.max(branch_slot));

                    // Now we need to enforce that at exactly one path was taken. We do that by enforcing
                    // that the sum of the previously collected `Boolean`s is one. But, of course, this
                    // irrelevant if we're on a virtual path and thus we use an implication gadget.
                    enforce_selector_with_premise(
                        &mut cs.namespace(|| "enforce_selector_with_premise"),
                        not_dummy,
                        &selector,
                    )
                    .with_context(|| " couldn't constrain `enforce_selector_with_premise`")
                }
                Ctrl::MatchVal(match_var, cases, def) => {
                    let allocated_lit = bound_allocations.get(match_var)?.hash().clone();
                    let mut selector = Vec::with_capacity(cases.len() + 1);
                    let mut branch_slots = Vec::with_capacity(cases.len());
                    for (lit, block) in cases {
                        let lit_ptr = lit.to_ptr(g.store);
                        let lit_hash = g.store.hash_ptr(&lit_ptr)?.hash;
                        let allocated_has_match = alloc_equal_const(
                            &mut cs.namespace(|| format!("{:?}.alloc_equal_const", lit)),
                            &allocated_lit,
                            lit_hash,
                        )
                        .with_context(|| "couldn't allocate equal const")?;

                        let not_dummy_and_has_match = and(
                            &mut cs.namespace(|| format!("{:?}.and", lit)),
                            not_dummy,
                            &allocated_has_match,
                        )
                        .with_context(|| "failed to constrain `and`")?;

                        selector.push(allocated_has_match);

                        let mut branch_slot = *next_slot;
                        recurse(
                            &mut cs.namespace(|| format!("{:?}", lit)),
                            block,
                            &not_dummy_and_has_match,
                            &mut branch_slot,
                            bound_allocations,
                            preallocated_outputs,
                            g,
                        )?;
                        branch_slots.push(branch_slot);
                    }

                    match def {
                        Some(def) => {
                            let default = selector.iter().all(|b| !b.get_value().unwrap());
                            let allocated_has_match = Boolean::Is(AllocatedBit::alloc(
                                &mut cs.namespace(|| "_.alloc_equal_const"),
                                Some(default),
                            )?);

                            let not_dummy_and_has_match = and(
                                &mut cs.namespace(|| "_.and"),
                                not_dummy,
                                &allocated_has_match,
                            )
                            .with_context(|| "failed to constrain `and`")?;

                            selector.push(allocated_has_match);

                            recurse(
                                &mut cs.namespace(|| "_"),
                                def,
                                &not_dummy_and_has_match,
                                next_slot,
                                bound_allocations,
                                preallocated_outputs,
                                g,
                            )?;
                        }
                        None => (),
                    }

                    // The number of slots the match used is the max number of slots of each branch
                    *next_slot = branch_slots
                        .into_iter()
                        .fold(*next_slot, |acc, branch_slot| acc.max(branch_slot));

                    // Now we need to enforce that at exactly one path was taken. We do that by enforcing
                    // that the sum of the previously collected `Boolean`s is one. But, of course, this
                    // irrelevant if we're on a virtual path and thus we use an implication gadget.
                    enforce_selector_with_premise(
                        &mut cs.namespace(|| "enforce_selector_with_premise"),
                        not_dummy,
                        &selector,
                    )
                    .with_context(|| " couldn't constrain `enforce_selector_with_premise`")
                }
            }
        }

        let call_outputs = frame.preimages.call_outputs.clone();
        recurse(
            cs,
            &self.body,
            &Boolean::Constant(true),
            &mut SlotsCounter::default(),
            &mut bound_allocations,
            &preallocated_outputs,
            &mut Globals {
                store,
                global_allocator: &mut global_allocator,
                preallocated_hash2_slots,
                preallocated_hash3_slots,
                preallocated_hash4_slots,
                call_outputs,
                call_count: 0,
            },
        )
    }

    /// Computes the number of constraints that `synthesize` should create. It's
    /// also an explicit way to document and attest how the number of constraints
    /// grow.
    pub fn num_constraints<F: LurkField>(&self, store: &mut Store<F>) -> usize {
        fn recurse<F: LurkField>(
            block: &Block,
            nested: bool,
            globals: &mut HashSet<FWrap<F>>,
            store: &mut Store<F>,
        ) -> usize {
            let mut num_constraints = 0;
            for op in &block.ops {
                match op {
                    Op::Call(_, func, _) => {
                        num_constraints += recurse(&func.body, nested, globals, store);
                    }
                    Op::Null(_, tag) => {
                        // constrain tag and hash
                        globals.insert(FWrap(tag.to_field()));
                        globals.insert(FWrap(F::ZERO));
                    }
                    Op::Lit(_, lit) => {
                        let lit_ptr = lit.to_ptr(store);
                        let lit_hash = store.hash_ptr(&lit_ptr).unwrap().hash;
                        globals.insert(FWrap(Tag::Expr(Sym).to_field()));
                        globals.insert(FWrap(lit_hash));
                    }
                    Op::Cast(_tgt, tag, _src) => {
                        globals.insert(FWrap(tag.to_field()));
                    }
                    Op::Add(_, _, _) | Op::Sub(_, _, _) | Op::Mul(_, _, _) => {
                        globals.insert(FWrap(Tag::Expr(Num).to_field()));
                        num_constraints += 1;
                    }
                    Op::Div(_, _, _) => {
                        // TODO
                    }
                    Op::Emit(_) => (),
                    Op::Hash2(_, tag, _) => {
                        // tag for the image
                        globals.insert(FWrap(tag.to_field()));
                        // tag and hash for 2 preimage pointers
                        num_constraints += 4;
                    }
                    Op::Hash3(_, tag, _) => {
                        // tag for the image
                        globals.insert(FWrap(tag.to_field()));
                        // tag and hash for 3 preimage pointers
                        num_constraints += 6;
                    }
                    Op::Hash4(_, tag, _) => {
                        // tag for the image
                        globals.insert(FWrap(tag.to_field()));
                        // tag and hash for 4 preimage pointers
                        num_constraints += 8;
                    }
                    Op::Unhash2(..) | Op::Unhash3(..) | Op::Unhash4(..) => {
                        // one constraint for the image's hash
                        num_constraints += 1;
                    }
                    Op::Hide(..) | Op::Open(..) => {
                        // TODO
                        globals.insert(FWrap(F::ZERO));
                    }
                }
            }
            match &block.ctrl {
                Ctrl::Return(vars) => num_constraints + 2 * vars.len(),
                Ctrl::IfEq(_, _, eq_block, else_block) => {
                    num_constraints
                        + if nested { 6 } else { 4 }
                        + recurse(eq_block, true, globals, store)
                        + recurse(else_block, true, globals, store)
                }
                Ctrl::MatchTag(_, cases, def) => {
                    // `alloc_equal_const` adds 3 constraints for each case and
                    // the `and` is free for non-nested `MatchTag`s, since we
                    // start `not_dummy` with a constant `true`
                    let multiplier = if nested { 4 } else { 3 };

                    // then we add 1 constraint from `enforce_selector_with_premise`
                    num_constraints += multiplier * cases.len() + 1;

                    // stacked ops are now nested
                    for block in cases.values() {
                        num_constraints += recurse(block, true, globals, store);
                    }
                    match def {
                        Some(def) => {
                            // constraints for the boolean and the default case
                            num_constraints += multiplier - 2;
                            num_constraints += recurse(def, true, globals, store);
                        }
                        None => (),
                    };
                    num_constraints
                }
                Ctrl::MatchVal(_, cases, def) => {
                    let multiplier = if nested { 4 } else { 3 };
                    num_constraints += multiplier * cases.len() + 1;
                    for block in cases.values() {
                        num_constraints += recurse(block, true, globals, store);
                    }
                    match def {
                        Some(def) => {
                            num_constraints += multiplier - 2;
                            num_constraints += recurse(def, true, globals, store);
                        }
                        None => (),
                    };
                    num_constraints
                }
            }
        }
        let globals = &mut HashSet::default();
        // fixed cost for each slot
        let slot_constraints =
            289 * self.slot.hash2 + 337 * self.slot.hash3 + 388 * self.slot.hash4;
        let num_constraints = recurse::<F>(&self.body, false, globals, store);
        slot_constraints + num_constraints + globals.len()
    }
}
