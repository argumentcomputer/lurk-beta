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

use anyhow::{anyhow, Result};
use bellpepper_core::{
    ConstraintSystem, SynthesisError,
    {
        boolean::{AllocatedBit, Boolean},
        num::AllocatedNum,
    },
};
use std::collections::{HashMap, HashSet, VecDeque};

use crate::circuit::gadgets::{
    constraints::{
        add, alloc_equal, alloc_is_zero, allocate_is_negative, boolean_to_num, div, enforce_pack,
        enforce_product_and_sum, enforce_selector_with_premise, implies_equal, implies_equal_const,
        implies_u64, implies_unequal, implies_unequal_const, mul, pick, sub,
    },
    data::{allocate_constant, hash_poseidon},
    pointer::AllocatedPtr,
};

use crate::{
    field::{FWrap, LurkField},
    tag::ExprTag::*,
};

use super::{
    interpreter::{Frame, PreimageData},
    pointers::{Ptr, ZPtr},
    slot::*,
    store::Store,
    var_map::VarMap,
    Block, Ctrl, Func, Op, Tag, Var,
};

/// Manages global allocations for constants in a constraint system
#[derive(Default)]
pub struct GlobalAllocator<F: LurkField>(HashMap<FWrap<F>, AllocatedNum<F>>);

#[inline]
fn allocate_num<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    namespace: &str,
    value: F,
) -> Result<AllocatedNum<F>, SynthesisError> {
    AllocatedNum::alloc(cs.namespace(|| namespace), || Ok(value))
}

impl<F: LurkField> GlobalAllocator<F> {
    /// Checks if the allocation for a numeric variable has already been cached.
    /// If so, don't do anything. Otherwise, allocate and cache it.
    fn alloc_const<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, f: F) {
        self.0.entry(FWrap(f)).or_insert_with(|| {
            allocate_constant(
                &mut cs.namespace(|| format!("allocate constant {}", f.hex_digits())),
                f,
            )
        });
    }

    #[inline]
    fn get_allocated_const(&self, f: F) -> Result<&AllocatedNum<F>> {
        self.0
            .get(&FWrap(f))
            .ok_or_else(|| anyhow!("Global allocation not found for {}", f.hex_digits()))
    }

    #[inline]
    fn get_allocated_const_cloned(&self, f: F) -> Result<AllocatedNum<F>> {
        self.get_allocated_const(f).cloned()
    }
}

pub(crate) type BoundAllocations<F> = VarMap<AllocatedPtr<F>>;

/// Allocates an unconstrained pointer
fn allocate_ptr<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    z_ptr: &ZPtr<F>,
    var: &Var,
    bound_allocations: &mut BoundAllocations<F>,
) -> Result<AllocatedPtr<F>> {
    let allocated_tag = allocate_num(cs, &format!("allocate {var}'s tag"), z_ptr.tag.to_field())?;
    let allocated_hash = allocate_num(cs, &format!("allocate {var}'s hash"), z_ptr.hash)?;
    let allocated_ptr = AllocatedPtr::from_parts(allocated_tag, allocated_hash);
    bound_allocations.insert(var.clone(), allocated_ptr.clone());
    Ok(allocated_ptr)
}

/// Allocates an unconstrained pointer for each output of the frame
fn allocate_output<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    store: &Store<F>,
    frame: &Frame<F>,
    bound_allocations: &mut BoundAllocations<F>,
) -> Result<Vec<AllocatedPtr<F>>> {
    frame
        .output
        .iter()
        .enumerate()
        .map(|(i, ptr)| {
            allocate_ptr(
                cs,
                &store.hash_ptr(ptr)?,
                &Var(format!("output[{}]", i).into()),
                bound_allocations,
            )
        })
        .collect()
}

#[inline]
fn allocate_preimg_component_for_slot<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    slot: &Slot,
    component_idx: usize,
    value: F,
) -> Result<AllocatedNum<F>, SynthesisError> {
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
    store: &Store<F>,
) -> Result<AllocatedNum<F>> {
    let cs = &mut cs.namespace(|| format!("image for slot {slot}"));
    let preallocated_img = {
        match slot.typ {
            SlotType::Hash4 => {
                hash_poseidon(cs, preallocated_preimg, store.poseidon_cache.constants.c4())?
            }
            SlotType::Hash6 => {
                hash_poseidon(cs, preallocated_preimg, store.poseidon_cache.constants.c6())?
            }
            SlotType::Hash8 => {
                hash_poseidon(cs, preallocated_preimg, store.poseidon_cache.constants.c8())?
            }
            SlotType::Commitment => {
                hash_poseidon(cs, preallocated_preimg, store.poseidon_cache.constants.c3())?
            }
            SlotType::LessThan => {
                // When a and b have the same sign, a < b iff a - b < 0
                // When a and b have different signs, a < b iff a is negative
                let a_num = &preallocated_preimg[0];
                let b_num = &preallocated_preimg[1];
                let slot_str = &slot.to_string();
                let a_is_negative = allocate_is_negative(
                    &mut cs.namespace(|| format!("a_is_negative for slot {slot_str}")),
                    a_num,
                )?;
                let a_is_negative_num = boolean_to_num(
                    &mut cs.namespace(|| format!("a_is_negative_num for slot {slot_str}")),
                    &a_is_negative,
                )?;
                let b_is_negative = allocate_is_negative(
                    &mut cs.namespace(|| format!("b_is_negative for slot {slot_str}")),
                    b_num,
                )?;
                let same_sign = Boolean::xor(
                    &mut cs.namespace(|| format!("same_sign for slot {slot_str}")),
                    &a_is_negative,
                    &b_is_negative,
                )?
                .not();
                let diff = sub(
                    &mut cs.namespace(|| format!("diff for slot {slot_str}")),
                    a_num,
                    b_num,
                )?;
                let diff_is_negative = allocate_is_negative(
                    &mut cs.namespace(|| format!("diff_is_negative for slot {slot_str}")),
                    &diff,
                )?;
                let diff_is_negative_num = boolean_to_num(
                    &mut cs.namespace(|| format!("diff_is_negative_num for slot {slot_str}")),
                    &diff_is_negative,
                )?;
                pick(
                    &mut cs.namespace(|| format!("pick for slot {slot}")),
                    &same_sign,
                    &diff_is_negative_num,
                    &a_is_negative_num,
                )?
            }
        }
    };
    Ok(preallocated_img)
}

/// Allocates unconstrained slots
fn allocate_slots<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    preimg_data: &[Option<PreimageData<F>>],
    slot_type: SlotType,
    num_slots: usize,
    store: &Store<F>,
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
                        preallocated_preimg.push(allocate_preimg_component_for_slot(
                            cs,
                            &slot,
                            component_idx,
                            z_ptr.tag.to_field(),
                        )?);

                        component_idx += 1;

                        // allocate pointer hash
                        preallocated_preimg.push(allocate_preimg_component_for_slot(
                            cs,
                            &slot,
                            component_idx,
                            z_ptr.hash,
                        )?);

                        component_idx += 1;
                    }
                }
                PreimageData::FPtr(f, ptr) => {
                    let z_ptr = store.hash_ptr(ptr)?;
                    // allocate first component
                    preallocated_preimg.push(allocate_preimg_component_for_slot(cs, &slot, 0, *f)?);
                    // allocate second component
                    preallocated_preimg.push(allocate_preimg_component_for_slot(
                        cs,
                        &slot,
                        1,
                        z_ptr.tag.to_field(),
                    )?);
                    // allocate third component
                    preallocated_preimg.push(allocate_preimg_component_for_slot(
                        cs, &slot, 2, z_ptr.hash,
                    )?);
                }
                PreimageData::FPair(a, b) => {
                    // allocate first component
                    preallocated_preimg.push(allocate_preimg_component_for_slot(cs, &slot, 0, *a)?);

                    // allocate second component
                    preallocated_preimg.push(allocate_preimg_component_for_slot(cs, &slot, 1, *b)?);
                }
            }

            // Allocate the image by calling the arithmetic function according
            // to the slot type
            let preallocated_img =
                allocate_img_for_slot(cs, &slot, preallocated_preimg.clone(), store)?;

            preallocations.push((preallocated_preimg, preallocated_img));
        } else {
            let slot = Slot {
                idx: slot_idx,
                typ: slot_type,
            };
            let preallocated_preimg: Vec<_> = (0..slot_type.preimg_size())
                .map(|component_idx| {
                    allocate_preimg_component_for_slot(cs, &slot, component_idx, F::ZERO)
                })
                .collect::<Result<_, _>>()?;

            let preallocated_img =
                allocate_img_for_slot(cs, &slot, preallocated_preimg.clone(), store)?;

            preallocations.push((preallocated_preimg, preallocated_img));
        }
    }

    Ok(preallocations)
}

impl Block {
    fn alloc_globals<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &Store<F>,
        g: &mut GlobalAllocator<F>,
    ) -> Result<(), SynthesisError> {
        for op in &self.ops {
            match op {
                Op::Call(_, func, _) => func.body.alloc_globals(cs, store, g)?,
                Op::Cons2(_, tag, _)
                | Op::Cons3(_, tag, _)
                | Op::Cons4(_, tag, _)
                | Op::Cast(_, tag, _) => {
                    g.alloc_const(cs, tag.to_field());
                }
                Op::Lit(_, lit) => {
                    let lit_ptr = lit.to_ptr_cached(store);
                    let lit_z_ptr = store.hash_ptr(&lit_ptr).unwrap();
                    g.alloc_const(cs, lit_z_ptr.tag.to_field());
                    g.alloc_const(cs, lit_z_ptr.hash);
                }
                Op::Null(_, tag) => {
                    g.alloc_const(cs, tag.to_field());
                    g.alloc_const(cs, F::ZERO);
                }
                Op::EqTag(..)
                | Op::EqVal(..)
                | Op::Add(..)
                | Op::Sub(..)
                | Op::Mul(..)
                | Op::Lt(..)
                | Op::Trunc(..)
                | Op::DivRem64(..) => {
                    g.alloc_const(cs, Tag::Expr(Num).to_field());
                }
                Op::Div(..) => {
                    g.alloc_const(cs, Tag::Expr(Num).to_field());
                    g.alloc_const(cs, F::ONE);
                }
                Op::Hide(..) | Op::Open(..) => {
                    g.alloc_const(cs, Tag::Expr(Num).to_field());
                    g.alloc_const(cs, Tag::Expr(Comm).to_field());
                }
                _ => (),
            }
        }
        match &self.ctrl {
            Ctrl::IfEq(.., a, b) => {
                a.alloc_globals(cs, store, g)?;
                b.alloc_globals(cs, store, g)?;
            }
            Ctrl::MatchTag(_, cases, def) => {
                for block in cases.values() {
                    block.alloc_globals(cs, store, g)?;
                }
                if let Some(def) = def {
                    def.alloc_globals(cs, store, g)?;
                }
            }
            Ctrl::MatchSymbol(_, cases, def) => {
                g.alloc_const(cs, Tag::Expr(Sym).to_field());
                for block in cases.values() {
                    block.alloc_globals(cs, store, g)?;
                }
                if let Some(def) = def {
                    def.alloc_globals(cs, store, g)?;
                }
            }
            Ctrl::Return(..) => (),
        }
        Ok(())
    }
}

impl Func {
    /// Allocates an unconstrained pointer for each input of the frame
    fn allocate_input<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &Store<F>,
        frame: &Frame<F>,
        bound_allocations: &mut BoundAllocations<F>,
    ) -> Result<()> {
        for (i, ptr) in frame.input.iter().enumerate() {
            let param = &self.input_params[i];
            allocate_ptr(cs, &store.hash_ptr(ptr)?, param, bound_allocations)?;
        }
        Ok(())
    }

    pub fn alloc_globals<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &Store<F>,
    ) -> Result<GlobalAllocator<F>, SynthesisError> {
        let mut g = GlobalAllocator::default();
        self.body.alloc_globals(cs, store, &mut g)?;
        Ok(g)
    }

    /// Create R1CS constraints for a LEM function given an evaluation frame. This
    /// function implements the STEP 3 mentioned above.
    ///
    /// Regarding the slot optimizations, STEP 3 uses information gathered during
    /// STEPs 1 and 2. So we proceed by first allocating preimages and images for
    /// each slot and then, as we traverse the function, we add constraints to make
    /// sure that the witness satisfies the arithmetic equations for the
    /// corresponding slots.
    pub fn synthesize_frame<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &Store<F>,
        frame: &Frame<F>,
        global_allocator: &GlobalAllocator<F>,
        bound_allocations: &mut BoundAllocations<F>,
    ) -> Result<Vec<AllocatedPtr<F>>> {
        // Outputs are constrained by the return statement. All functions return
        let preallocated_outputs = allocate_output(cs, store, frame, bound_allocations)?;

        // Slots are constrained by their usage inside the function body. The ones
        // not used in throughout the concrete path are effectively unconstrained,
        // that's why they are filled with dummies
        let preallocated_hash4_slots = allocate_slots(
            cs,
            &frame.preimages.hash4,
            SlotType::Hash4,
            self.slot.hash4,
            store,
        )?;

        let preallocated_hash6_slots = allocate_slots(
            cs,
            &frame.preimages.hash6,
            SlotType::Hash6,
            self.slot.hash6,
            store,
        )?;

        let preallocated_hash8_slots = allocate_slots(
            cs,
            &frame.preimages.hash8,
            SlotType::Hash8,
            self.slot.hash8,
            store,
        )?;

        let preallocated_commitment_slots = allocate_slots(
            cs,
            &frame.preimages.commitment,
            SlotType::Commitment,
            self.slot.commitment,
            store,
        )?;

        let preallocated_less_than_slots = allocate_slots(
            cs,
            &frame.preimages.less_than,
            SlotType::LessThan,
            self.slot.less_than,
            store,
        )?;

        struct Globals<'a, F: LurkField> {
            store: &'a Store<F>,
            global_allocator: &'a GlobalAllocator<F>,
            preallocated_hash4_slots: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
            preallocated_hash6_slots: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
            preallocated_hash8_slots: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
            preallocated_commitment_slots: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
            preallocated_less_than_slots: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
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
                macro_rules! cons_helper {
                    ( $img: expr, $tag: expr, $preimg: expr, $slot: expr ) => {
                        // Retrieve allocated preimage
                        let allocated_preimg = bound_allocations.get_many($preimg)?;

                        // Retrieve the preallocated preimage and image for this slot
                        let (preallocated_preimg, preallocated_img_hash) = match $slot {
                            SlotType::Hash4 => {
                                &g.preallocated_hash4_slots[next_slot.consume_hash4()]
                            }
                            SlotType::Hash6 => {
                                &g.preallocated_hash6_slots[next_slot.consume_hash6()]
                            }
                            SlotType::Hash8 => {
                                &g.preallocated_hash8_slots[next_slot.consume_hash8()]
                            }
                            _ => panic!("Invalid slot type for cons_helper macro"),
                        };

                        // For each component of the preimage, add implication constraints
                        // for its tag and hash
                        for (i, allocated_ptr) in allocated_preimg.iter().enumerate() {
                            let var = &$preimg[i];
                            let ptr_idx = 2 * i;
                            implies_equal(
                                &mut cs.namespace(|| {
                                    format!("implies equal for {var}'s tag (OP {:?}, pos {i})", &op)
                                }),
                                not_dummy,
                                allocated_ptr.tag(),
                                &preallocated_preimg[ptr_idx], // tag index
                            );
                            implies_equal(
                                &mut cs.namespace(|| {
                                    format!(
                                        "implies equal for {var}'s hash (OP {:?}, pos {i})",
                                        &op
                                    )
                                }),
                                not_dummy,
                                allocated_ptr.hash(),
                                &preallocated_preimg[ptr_idx + 1], // hash index
                            );
                        }

                        // Allocate the image tag if it hasn't been allocated before,
                        // create the full image pointer and add it to bound allocations
                        let img_tag = g
                            .global_allocator
                            .get_allocated_const_cloned($tag.to_field())?;
                        let img_hash = preallocated_img_hash.clone();
                        let img_ptr = AllocatedPtr::from_parts(img_tag, img_hash);
                        bound_allocations.insert($img, img_ptr);
                    };
                }

                macro_rules! decons_helper {
                    ( $preimg: expr, $img: expr, $slot: expr ) => {
                        // Retrieve allocated image
                        let allocated_img = bound_allocations.get($img)?;

                        // Retrieve the preallocated preimage and image for this slot
                        let (preallocated_preimg, preallocated_img) = match $slot {
                            SlotType::Hash4 => {
                                &g.preallocated_hash4_slots[next_slot.consume_hash4()]
                            }
                            SlotType::Hash6 => {
                                &g.preallocated_hash6_slots[next_slot.consume_hash6()]
                            }
                            SlotType::Hash8 => {
                                &g.preallocated_hash8_slots[next_slot.consume_hash8()]
                            }
                            _ => panic!("Invalid slot type for decons_helper macro"),
                        };

                        // Add the implication constraint for the image
                        implies_equal(
                            &mut cs.namespace(|| {
                                format!("implies equal for {}'s hash (OP {:?})", $img, &op)
                            }),
                            not_dummy,
                            allocated_img.hash(),
                            &preallocated_img,
                        );

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
                        let dummy = Ptr::null(Tag::Expr(Nil));
                        let output_vals = if let Some(true) = not_dummy.get_value() {
                            g.call_outputs
                                .pop_front()
                                .unwrap_or_else(|| (0..out.len()).map(|_| dummy).collect())
                        } else {
                            (0..out.len()).map(|_| dummy).collect()
                        };
                        assert_eq!(output_vals.len(), out.len());
                        let mut output_ptrs = Vec::with_capacity(out.len());
                        for (ptr, var) in output_vals.iter().zip(out.iter()) {
                            let zptr = &g.store.hash_ptr(ptr)?;
                            output_ptrs.push(allocate_ptr(cs, zptr, var, bound_allocations)?);
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
                    Op::Cons2(img, tag, preimg) => {
                        cons_helper!(img.clone(), tag, preimg, SlotType::Hash4);
                    }
                    Op::Cons3(img, tag, preimg) => {
                        cons_helper!(img.clone(), tag, preimg, SlotType::Hash6);
                    }
                    Op::Cons4(img, tag, preimg) => {
                        cons_helper!(img.clone(), tag, preimg, SlotType::Hash8);
                    }
                    Op::Decons2(preimg, img) => {
                        decons_helper!(preimg, img, SlotType::Hash4);
                    }
                    Op::Decons3(preimg, img) => {
                        decons_helper!(preimg, img, SlotType::Hash6);
                    }
                    Op::Decons4(preimg, img) => {
                        decons_helper!(preimg, img, SlotType::Hash8);
                    }
                    Op::Null(tgt, tag) => {
                        let tag = g
                            .global_allocator
                            .get_allocated_const_cloned(tag.to_field())?;
                        let zero = g.global_allocator.get_allocated_const_cloned(F::ZERO)?;
                        let allocated_ptr = AllocatedPtr::from_parts(tag, zero);
                        bound_allocations.insert(tgt.clone(), allocated_ptr);
                    }
                    Op::Lit(tgt, lit) => {
                        let lit_ptr = lit.to_ptr_cached(g.store);
                        let lit_tag = lit_ptr.tag().to_field();
                        let lit_hash = g.store.hash_ptr(&lit_ptr)?.hash;
                        let allocated_tag =
                            g.global_allocator.get_allocated_const_cloned(lit_tag)?;
                        let allocated_hash =
                            g.global_allocator.get_allocated_const_cloned(lit_hash)?;
                        let allocated_ptr = AllocatedPtr::from_parts(allocated_tag, allocated_hash);
                        bound_allocations.insert(tgt.clone(), allocated_ptr);
                    }
                    Op::Cast(tgt, tag, src) => {
                        let src = bound_allocations.get(src)?;
                        let tag = g
                            .global_allocator
                            .get_allocated_const_cloned(tag.to_field())?;
                        let allocated_ptr = AllocatedPtr::from_parts(tag, src.hash().clone());
                        bound_allocations.insert(tgt.clone(), allocated_ptr);
                    }
                    Op::EqTag(tgt, a, b) => {
                        let a = bound_allocations.get(a)?;
                        let b = bound_allocations.get(b)?;
                        let a_num = a.tag();
                        let b_num = b.tag();
                        let eq = alloc_equal(&mut cs.namespace(|| "equal_tag"), a_num, b_num)?;
                        let c_num = boolean_to_num(&mut cs.namespace(|| "equal_tag.to_num"), &eq)?;
                        let tag = g
                            .global_allocator
                            .get_allocated_const_cloned(Tag::Expr(Num).to_field())?;
                        let c = AllocatedPtr::from_parts(tag, c_num);
                        bound_allocations.insert(tgt.clone(), c);
                    }
                    Op::EqVal(tgt, a, b) => {
                        let a = bound_allocations.get(a)?;
                        let b = bound_allocations.get(b)?;
                        let a_num = a.hash();
                        let b_num = b.hash();
                        let eq = alloc_equal(&mut cs.namespace(|| "equal_val"), a_num, b_num)?;
                        let c_num = boolean_to_num(&mut cs.namespace(|| "equal_val.to_num"), &eq)?;
                        let tag = g
                            .global_allocator
                            .get_allocated_const_cloned(Tag::Expr(Num).to_field())?;
                        let c = AllocatedPtr::from_parts(tag, c_num);
                        bound_allocations.insert(tgt.clone(), c);
                    }
                    Op::Add(tgt, a, b) => {
                        let a = bound_allocations.get(a)?;
                        let b = bound_allocations.get(b)?;
                        let a_num = a.hash();
                        let b_num = b.hash();
                        let c_num = add(&mut cs.namespace(|| "add"), a_num, b_num)?;
                        let tag = g
                            .global_allocator
                            .get_allocated_const_cloned(Tag::Expr(Num).to_field())?;
                        let c = AllocatedPtr::from_parts(tag, c_num);
                        bound_allocations.insert(tgt.clone(), c);
                    }
                    Op::Sub(tgt, a, b) => {
                        let a = bound_allocations.get(a)?;
                        let b = bound_allocations.get(b)?;
                        let a_num = a.hash();
                        let b_num = b.hash();
                        let c_num = sub(&mut cs.namespace(|| "sub"), a_num, b_num)?;
                        let tag = g
                            .global_allocator
                            .get_allocated_const_cloned(Tag::Expr(Num).to_field())?;
                        let c = AllocatedPtr::from_parts(tag, c_num);
                        bound_allocations.insert(tgt.clone(), c);
                    }
                    Op::Mul(tgt, a, b) => {
                        let a = bound_allocations.get(a)?;
                        let b = bound_allocations.get(b)?;
                        let a_num = a.hash();
                        let b_num = b.hash();
                        let c_num = mul(&mut cs.namespace(|| "mul"), a_num, b_num)?;
                        let tag = g
                            .global_allocator
                            .get_allocated_const_cloned(Tag::Expr(Num).to_field())?;
                        let c = AllocatedPtr::from_parts(tag, c_num);
                        bound_allocations.insert(tgt.clone(), c);
                    }
                    Op::Div(tgt, a, b) => {
                        let a = bound_allocations.get(a)?;
                        let b = bound_allocations.get(b)?;
                        let a_num = a.hash();
                        let b_num = b.hash();

                        let b_is_zero = &alloc_is_zero(&mut cs.namespace(|| "b_is_zero"), b_num)?;
                        let one = g.global_allocator.get_allocated_const(F::ONE)?;

                        let divisor = pick(
                            &mut cs.namespace(|| "maybe-dummy divisor"),
                            b_is_zero,
                            one,
                            b_num,
                        )?;

                        let quotient = div(&mut cs.namespace(|| "quotient"), a_num, &divisor)?;

                        let tag = g
                            .global_allocator
                            .get_allocated_const_cloned(Tag::Expr(Num).to_field())?;
                        let c = AllocatedPtr::from_parts(tag, quotient);
                        bound_allocations.insert(tgt.clone(), c);
                    }
                    Op::Lt(tgt, a, b) => {
                        let a = bound_allocations.get(a)?;
                        let b = bound_allocations.get(b)?;
                        let tag = g
                            .global_allocator
                            .get_allocated_const_cloned(Tag::Expr(Num).to_field())?;
                        let (preallocated_preimg, lt) =
                            &g.preallocated_less_than_slots[next_slot.consume_less_than()];
                        for (i, n) in [a.hash(), b.hash()].into_iter().enumerate() {
                            implies_equal(
                                &mut cs.namespace(|| {
                                    format!("implies equal for component {i} (OP {:?})", &op)
                                }),
                                not_dummy,
                                n,
                                &preallocated_preimg[i],
                            );
                        }
                        let c = AllocatedPtr::from_parts(tag, lt.clone());
                        bound_allocations.insert(tgt.clone(), c);
                    }
                    Op::Trunc(tgt, a, n) => {
                        assert!(*n <= 64);
                        let a = bound_allocations.get(a)?;
                        let mut trunc_bits = a
                            .hash()
                            .to_bits_le_strict(&mut cs.namespace(|| "to_bits_le"))?;
                        trunc_bits.truncate(*n as usize);
                        let trunc = AllocatedNum::alloc(cs.namespace(|| "trunc"), || {
                            let b = if *n < 64 { (1 << *n) - 1 } else { u64::MAX };
                            a.hash()
                                .get_value()
                                .map(|a| F::from_u64(a.to_u64_unchecked() & b))
                                .ok_or(SynthesisError::AssignmentMissing)
                        })?;
                        enforce_pack(&mut cs.namespace(|| "enforce_trunc"), &trunc_bits, &trunc);
                        let tag = g
                            .global_allocator
                            .get_allocated_const_cloned(Tag::Expr(Num).to_field())?;
                        let c = AllocatedPtr::from_parts(tag, trunc);
                        bound_allocations.insert(tgt.clone(), c);
                    }
                    Op::DivRem64(tgt, a, b) => {
                        let a = bound_allocations.get(a)?.hash();
                        let b = bound_allocations.get(b)?.hash();
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
                            AllocatedNum::alloc(cs.namespace(|| "div"), || Ok(div_rem.unwrap().0))?;
                        let rem =
                            AllocatedNum::alloc(cs.namespace(|| "rem"), || Ok(div_rem.unwrap().1))?;

                        let diff = sub(cs.namespace(|| "diff for slot {slot}"), b, &rem)?;
                        implies_u64(cs.namespace(|| "div_u64"), not_dummy, &div)?;
                        implies_u64(cs.namespace(|| "rem_u64"), not_dummy, &rem)?;
                        implies_u64(cs.namespace(|| "diff_u64"), not_dummy, &diff)?;

                        enforce_product_and_sum(
                            cs,
                            || "enforce a = b * div + rem",
                            b,
                            &div,
                            &rem,
                            a,
                        );
                        let tag = g
                            .global_allocator
                            .get_allocated_const_cloned(Tag::Expr(Num).to_field())?;
                        let div_ptr = AllocatedPtr::from_parts(tag.clone(), div);
                        let rem_ptr = AllocatedPtr::from_parts(tag, rem);
                        bound_allocations.insert(tgt[0].clone(), div_ptr);
                        bound_allocations.insert(tgt[1].clone(), rem_ptr);
                    }
                    Op::Emit(_) => (),
                    Op::Hide(tgt, sec, pay) => {
                        let sec = bound_allocations.get(sec)?;
                        let pay = bound_allocations.get(pay)?;
                        let sec_tag = g
                            .global_allocator
                            .get_allocated_const(Tag::Expr(Num).to_field())?;
                        let (preallocated_preimg, hash) =
                            &g.preallocated_commitment_slots[next_slot.consume_commitment()];
                        implies_equal(
                            &mut cs.namespace(|| {
                                format!("implies equal for the secret's tag (OP {:?})", &op)
                            }),
                            not_dummy,
                            sec.tag(),
                            sec_tag,
                        );
                        implies_equal(
                            &mut cs.namespace(|| {
                                format!("implies equal for the secret's hash (OP {:?})", &op)
                            }),
                            not_dummy,
                            sec.hash(),
                            &preallocated_preimg[0],
                        );
                        implies_equal(
                            &mut cs.namespace(|| {
                                format!("implies equal for the payload's tag (OP {:?})", &op)
                            }),
                            not_dummy,
                            pay.tag(),
                            &preallocated_preimg[1],
                        );
                        implies_equal(
                            &mut cs.namespace(|| {
                                format!("implies equal for the payload's hash (OP {:?})", &op)
                            }),
                            not_dummy,
                            pay.hash(),
                            &preallocated_preimg[2],
                        );
                        let tag = g
                            .global_allocator
                            .get_allocated_const_cloned(Tag::Expr(Comm).to_field())?;
                        let allocated_ptr = AllocatedPtr::from_parts(tag, hash.clone());
                        bound_allocations.insert(tgt.clone(), allocated_ptr);
                    }
                    Op::Open(sec, pay, comm) => {
                        let comm = bound_allocations.get(comm)?;
                        let (preallocated_preimg, com_hash) =
                            &g.preallocated_commitment_slots[next_slot.consume_commitment()];
                        let comm_tag = g
                            .global_allocator
                            .get_allocated_const(Tag::Expr(Comm).to_field())?;
                        implies_equal(
                            &mut cs.namespace(|| {
                                format!("implies equal for comm's tag (OP {:?})", &op)
                            }),
                            not_dummy,
                            comm.tag(),
                            comm_tag,
                        );
                        implies_equal(
                            &mut cs.namespace(|| {
                                format!("implies equal for comm's hash (OP {:?})", &op)
                            }),
                            not_dummy,
                            comm.hash(),
                            com_hash,
                        );
                        let sec_tag = g
                            .global_allocator
                            .get_allocated_const_cloned(Tag::Expr(Num).to_field())?;
                        let allocated_sec_ptr =
                            AllocatedPtr::from_parts(sec_tag, preallocated_preimg[0].clone());
                        let allocated_pay_ptr = AllocatedPtr::from_parts(
                            preallocated_preimg[1].clone(),
                            preallocated_preimg[2].clone(),
                        );
                        bound_allocations.insert(sec.clone(), allocated_sec_ptr);
                        bound_allocations.insert(pay.clone(), allocated_pay_ptr);
                    }
                }
            }

            let mut synthesize_match = |matched: &AllocatedNum<F>,
                                        cases: &[(F, &Block)],
                                        def: &Option<Box<Block>>,
                                        bound_allocations: &mut VarMap<AllocatedPtr<F>>,
                                        g: &mut Globals<'_, F>|
             -> Result<Vec<SlotsCounter>> {
                // * One `Boolean` for each case
                // * Maybe one `Boolean` for the default case
                // * One `Boolean` for the negation of `not_dummy`
                let selector_size = cases.len() + usize::from(def.is_some()) + 1;
                let mut selector = Vec::with_capacity(selector_size);
                let mut branch_slots = Vec::with_capacity(cases.len());
                for (i, (f, block)) in cases.iter().enumerate() {
                    // For each case, we compute `not_dummy_and_has_match: Boolean`
                    // and accumulate them on a `selector` vector
                    let not_dummy_and_has_match_bool =
                        not_dummy.get_value().and_then(|not_dummy| {
                            matched
                                .get_value()
                                .map(|matched_f| not_dummy && &matched_f == f)
                        });
                    let not_dummy_and_has_match = Boolean::Is(AllocatedBit::alloc(
                        &mut cs.namespace(|| format!("{i}.allocated_bit")),
                        not_dummy_and_has_match_bool,
                    )?);

                    // If `not_dummy_and_has_match` is true, then we enforce a match
                    implies_equal_const(
                        &mut cs.namespace(|| format!("{i}.implies_equal_const")),
                        &not_dummy_and_has_match,
                        matched,
                        *f,
                    );

                    selector.push(not_dummy_and_has_match.clone());

                    let mut branch_slot = *next_slot;
                    recurse(
                        &mut cs.namespace(|| format!("{i}")),
                        block,
                        &not_dummy_and_has_match,
                        &mut branch_slot,
                        bound_allocations,
                        preallocated_outputs,
                        g,
                    )?;
                    branch_slots.push(branch_slot);
                }

                if let Some(def) = def {
                    // Compute `default: Boolean`, which tells whether the default case was chosen or not
                    let is_default_bool = selector.iter().fold(not_dummy.get_value(), |acc, b| {
                        // all the booleans in `selector` have to be false up to this point
                        // in order for the default case to be selected
                        acc.and_then(|acc| b.get_value().map(|b| acc && !b))
                    });
                    let is_default = Boolean::Is(AllocatedBit::alloc(
                        &mut cs.namespace(|| "_.allocated_bit"),
                        is_default_bool,
                    )?);

                    for (i, (f, _)) in cases.iter().enumerate() {
                        // if the default path was taken, then there can be no tag in `cases`
                        // that equals the tag of the pointer being matched on
                        implies_unequal_const(
                            &mut cs.namespace(|| format!("{i}.implies_unequal_const")),
                            &is_default,
                            matched,
                            *f,
                        )?;
                    }

                    recurse(
                        &mut cs.namespace(|| "_"),
                        def,
                        &is_default,
                        next_slot,
                        bound_allocations,
                        preallocated_outputs,
                        g,
                    )?;

                    // Pushing `is_default` to `selector` to enforce summation = 1
                    selector.push(is_default);
                }

                // Now we need to enforce that exactly one path was taken. We do that by enforcing
                // that the sum of the previously collected `Boolean`s is one. But, of course, this
                // is irrelevant if we're on a virtual path and thus we use an implication gadget.

                // If `not_dummy` is false, then all booleans in `selector` are false up to this point.
                // Thus we need to add a negation of `not_dummy` to make it satisfiable. If it's true,
                // it will count as a 0 and will not influence the sum.
                selector.push(not_dummy.not());

                enforce_selector_with_premise(
                    &mut cs.namespace(|| "enforce_selector_with_premise"),
                    not_dummy,
                    &selector,
                );

                Ok(branch_slots)
            };

            match &block.ctrl {
                Ctrl::Return(return_vars) => {
                    for (i, return_var) in return_vars.iter().enumerate() {
                        let allocated_ptr = bound_allocations.get(return_var)?;

                        allocated_ptr.implies_ptr_equal(
                            &mut cs.namespace(|| {
                                format!("implies_ptr_equal {return_var} (return_var {i})")
                            }),
                            not_dummy,
                            &preallocated_outputs[i],
                        );
                    }
                    Ok(())
                }
                Ctrl::IfEq(x, y, eq_block, else_block) => {
                    let x_ptr = bound_allocations.get(x)?.hash();
                    let y_ptr = bound_allocations.get(y)?.hash();
                    let mut selector = Vec::with_capacity(3);

                    let eq_val = not_dummy.get_value().and_then(|not_dummy| {
                        x_ptr
                            .get_value()
                            .and_then(|x| y_ptr.get_value().map(|y| not_dummy && x == y))
                    });
                    let neq_val = not_dummy.get_value().and_then(|not_dummy| {
                        x_ptr
                            .get_value()
                            .and_then(|x| y_ptr.get_value().map(|y| not_dummy && x != y))
                    });
                    let is_eq =
                        Boolean::Is(AllocatedBit::alloc(&mut cs.namespace(|| "if_eq"), eq_val)?);
                    let is_neq = Boolean::Is(AllocatedBit::alloc(
                        &mut cs.namespace(|| "if_neq"),
                        neq_val,
                    )?);
                    implies_equal(
                        &mut cs.namespace(|| format!("{x} = {y}")),
                        &is_eq,
                        x_ptr,
                        y_ptr,
                    );
                    implies_unequal(
                        &mut cs.namespace(|| format!("{x} != {y}")),
                        &is_neq,
                        x_ptr,
                        y_ptr,
                    )?;

                    selector.push(not_dummy.not());
                    selector.push(is_eq.clone());
                    selector.push(is_neq.clone());
                    enforce_selector_with_premise(
                        &mut cs.namespace(|| "if_enforce_selector_with_premise"),
                        not_dummy,
                        &selector,
                    );

                    let mut branch_slot = *next_slot;
                    recurse(
                        &mut cs.namespace(|| "if_eq.true"),
                        eq_block,
                        &is_eq,
                        &mut branch_slot,
                        bound_allocations,
                        preallocated_outputs,
                        g,
                    )?;
                    recurse(
                        &mut cs.namespace(|| "if_eq.false"),
                        else_block,
                        &is_neq,
                        next_slot,
                        bound_allocations,
                        preallocated_outputs,
                        g,
                    )?;
                    *next_slot = next_slot.max(branch_slot);
                    Ok(())
                }
                Ctrl::MatchTag(match_var, cases, def) => {
                    let matched = bound_allocations.get(match_var)?.tag().clone();
                    let cases_vec = cases
                        .iter()
                        .map(|(tag, block)| (tag.to_field::<F>(), block))
                        .collect::<Vec<_>>();
                    let branch_slots =
                        synthesize_match(&matched, &cases_vec, def, bound_allocations, g)?;

                    // The number of slots the match used is the max number of slots of each branch
                    *next_slot = next_slot.fold_max(branch_slots);
                    Ok(())
                }
                Ctrl::MatchSymbol(match_var, cases, def) => {
                    let match_var_ptr = bound_allocations.get(match_var)?.clone();

                    let mut cases_vec = Vec::with_capacity(cases.len());
                    for (sym, block) in cases {
                        let sym_ptr = g
                            .store
                            .interned_symbol(sym)
                            .expect("symbol must have been interned");
                        let sym_hash = g.store.hash_ptr(sym_ptr)?.hash;
                        cases_vec.push((sym_hash, block));
                    }

                    let branch_slots = synthesize_match(
                        match_var_ptr.hash(),
                        &cases_vec,
                        def,
                        bound_allocations,
                        g,
                    )?;

                    // Now we enforce `match_var`'s tag

                    let sym_tag = g
                        .global_allocator
                        .get_allocated_const(Tag::Expr(Sym).to_field())?;

                    implies_equal(
                        &mut cs.namespace(|| format!("implies equal for {match_var}'s tag (Sym)")),
                        not_dummy,
                        match_var_ptr.tag(),
                        sym_tag,
                    );

                    // The number of slots the match used is the max number of slots of each branch
                    *next_slot = next_slot.fold_max(branch_slots);
                    Ok(())
                }
            }
        }

        let call_outputs = frame.preimages.call_outputs.clone();
        recurse(
            cs,
            &self.body,
            &Boolean::Constant(true),
            &mut SlotsCounter::default(),
            bound_allocations,
            &preallocated_outputs,
            &mut Globals {
                store,
                global_allocator,
                preallocated_hash4_slots,
                preallocated_hash6_slots,
                preallocated_hash8_slots,
                preallocated_commitment_slots,
                preallocated_less_than_slots,
                call_outputs,
                call_count: 0,
            },
        )?;
        Ok(preallocated_outputs)
    }

    /// Helper API for tests
    pub fn synthesize_frame_aux<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &Store<F>,
        frame: &Frame<F>,
    ) -> Result<()> {
        let bound_allocations = &mut BoundAllocations::new();
        let global_allocator = self.alloc_globals(cs, store)?;
        self.allocate_input(cs, store, frame, bound_allocations)?;
        self.synthesize_frame(cs, store, frame, &global_allocator, bound_allocations)?;
        Ok(())
    }

    /// Computes the number of constraints that `synthesize` should create. It's
    /// also an explicit way to document and attest how the number of constraints
    /// grow.
    pub fn num_constraints<F: LurkField>(&self, store: &Store<F>) -> usize {
        fn recurse<F: LurkField>(
            block: &Block,
            globals: &mut HashSet<FWrap<F>>,
            store: &Store<F>,
        ) -> usize {
            let mut num_constraints = 0;
            for op in &block.ops {
                match op {
                    Op::Call(_, func, _) => {
                        num_constraints += recurse(&func.body, globals, store);
                    }
                    Op::Null(_, tag) => {
                        // constrain tag and hash
                        globals.insert(FWrap(tag.to_field()));
                        globals.insert(FWrap(F::ZERO));
                    }
                    Op::Lit(_, lit) => {
                        let lit_ptr = lit.to_ptr_cached(store);
                        let lit_z_ptr = store.hash_ptr(&lit_ptr).unwrap();
                        globals.insert(FWrap(lit_z_ptr.tag.to_field()));
                        globals.insert(FWrap(lit_z_ptr.hash));
                    }
                    Op::Cast(_, tag, _) => {
                        globals.insert(FWrap(tag.to_field()));
                    }
                    Op::EqTag(..) | Op::EqVal(..) => {
                        globals.insert(FWrap(Tag::Expr(Num).to_field()));
                        num_constraints += 5;
                    }
                    Op::Add(..) | Op::Sub(..) | Op::Mul(..) => {
                        globals.insert(FWrap(Tag::Expr(Num).to_field()));
                        num_constraints += 1;
                    }
                    Op::Div(..) => {
                        globals.insert(FWrap(Tag::Expr(Num).to_field()));
                        globals.insert(FWrap(F::ONE));
                        num_constraints += 5;
                    }
                    Op::Lt(..) => {
                        globals.insert(FWrap(Tag::Expr(Num).to_field()));
                        num_constraints += 2;
                    }
                    Op::Trunc(..) => {
                        globals.insert(FWrap(Tag::Expr(Num).to_field()));
                        // bit decomposition + enforce_pack
                        num_constraints += 389;
                    }
                    Op::DivRem64(..) => {
                        globals.insert(FWrap(Tag::Expr(Num).to_field()));
                        // three implies_u64, one sub and one linear
                        num_constraints += 197;
                    }
                    Op::Emit(_) => (),
                    Op::Cons2(_, tag, _) => {
                        // tag for the image
                        globals.insert(FWrap(tag.to_field()));
                        // tag and hash for 2 preimage pointers
                        num_constraints += 4;
                    }
                    Op::Cons3(_, tag, _) => {
                        // tag for the image
                        globals.insert(FWrap(tag.to_field()));
                        // tag and hash for 3 preimage pointers
                        num_constraints += 6;
                    }
                    Op::Cons4(_, tag, _) => {
                        // tag for the image
                        globals.insert(FWrap(tag.to_field()));
                        // tag and hash for 4 preimage pointers
                        num_constraints += 8;
                    }
                    Op::Decons2(..) | Op::Decons3(..) | Op::Decons4(..) => {
                        // one constraint for the image's hash
                        num_constraints += 1;
                    }
                    Op::Hide(..) => {
                        num_constraints += 4;
                        globals.insert(FWrap(Tag::Expr(Num).to_field()));
                        globals.insert(FWrap(Tag::Expr(Comm).to_field()));
                    }
                    Op::Open(..) => {
                        num_constraints += 2;
                        globals.insert(FWrap(Tag::Expr(Num).to_field()));
                        globals.insert(FWrap(Tag::Expr(Comm).to_field()));
                    }
                }
            }
            match &block.ctrl {
                Ctrl::Return(vars) => num_constraints + 2 * vars.len(),
                Ctrl::IfEq(_, _, eq_block, else_block) => {
                    num_constraints
                        + 5
                        + recurse(eq_block, globals, store)
                        + recurse(else_block, globals, store)
                }
                Ctrl::MatchTag(_, cases, def) => {
                    // We allocate one boolean per case and constrain it once
                    // per case. Then we add 1 constraint to enforce only one
                    // case was selected
                    num_constraints += 2 * cases.len() + 1;

                    for block in cases.values() {
                        num_constraints += recurse(block, globals, store);
                    }
                    if let Some(def) = def {
                        // constraints for the boolean, the unequalities and the default case
                        num_constraints += 1 + cases.len();
                        num_constraints += recurse(def, globals, store);
                    }
                    num_constraints
                }
                Ctrl::MatchSymbol(_, cases, def) => {
                    // First we enforce that the tag of the pointer being matched on
                    // is Sym
                    num_constraints += 1;
                    globals.insert(FWrap(Tag::Expr(Sym).to_field()));
                    // We allocate one boolean per case and constrain it once
                    // per case. Then we add 1 constraint to enforce only one
                    // case was selected
                    num_constraints += 2 * cases.len() + 1;

                    for block in cases.values() {
                        num_constraints += recurse(block, globals, store);
                    }
                    if let Some(def) = def {
                        // constraints for the boolean, the unequalities and the default case
                        num_constraints += 1 + cases.len();
                        num_constraints += recurse(def, globals, store);
                    }
                    num_constraints
                }
            }
        }
        let globals = &mut HashSet::default();
        // fixed cost for each slot
        let slot_constraints = 289 * self.slot.hash4
            + 337 * self.slot.hash6
            + 388 * self.slot.hash8
            + 265 * self.slot.commitment
            + 1172 * self.slot.less_than;
        let num_constraints = recurse(&self.body, globals, store);
        slot_constraints + num_constraints + globals.len()
    }
}
