//! ## Constraint system for LEM
//!
//! This module implements the generation of bellpepper constraints for LEM, such
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

use anyhow::{anyhow, bail, Result};
use bellpepper::util_cs::witness_cs::WitnessCS;
use bellpepper_core::{
    ConstraintSystem, SynthesisError,
    {
        boolean::{AllocatedBit, Boolean},
        num::AllocatedNum,
    },
};
use std::{
    collections::{HashMap, HashSet, VecDeque},
    sync::Arc,
};

use crate::{
    circuit::gadgets::{
        constraints::{
            alloc_equal, alloc_is_zero, and, div, enforce_product_and_sum,
            enforce_selector_with_premise, implies_equal, implies_equal_const, implies_pack,
            implies_u64, implies_unequal_const, mul, or, pick, sub,
        },
        data::{allocate_constant, hash_poseidon},
        pointer::AllocatedPtr,
    },
    coprocessor::Coprocessor,
    eval::lang::Lang,
    field::{FWrap, LanguageField, LurkField},
    tag::{
        ExprTag::{Comm, Num, Sym},
        Tag,
    },
};

use super::{
    interpreter::Frame,
    pointers::{Ptr, ZPtr},
    slot::*,
    store::Store,
    var_map::VarMap,
    Block, Ctrl, Func, Op, Var,
};

#[derive(Clone)]
pub enum AllocatedVal<F: LurkField> {
    Pointer(AllocatedPtr<F>),
    Number(AllocatedNum<F>),
    Boolean(Boolean),
    Bits(Vec<Boolean>),
}

pub struct SlotsAllocations<F: LurkField> {
    hash4: Vec<(Vec<AllocatedNum<F>>, AllocatedVal<F>)>,
    hash6: Vec<(Vec<AllocatedNum<F>>, AllocatedVal<F>)>,
    hash8: Vec<(Vec<AllocatedNum<F>>, AllocatedVal<F>)>,
    commitment: Vec<(Vec<AllocatedNum<F>>, AllocatedVal<F>)>,
    bit_decomp: Vec<(Vec<AllocatedNum<F>>, AllocatedVal<F>)>,
}

pub struct SlotWitness<F: LurkField> {
    pub witness: WitnessCS<F>,
    pub allocations: (Vec<AllocatedNum<F>>, AllocatedVal<F>),
}

/// Manages global allocations for constants in a constraint system
#[derive(Default)]
pub struct GlobalAllocator<F: LurkField>(HashMap<FWrap<F>, AllocatedNum<F>>);

impl<F: LurkField> GlobalAllocator<F> {
    /// Checks if the allocation for a numeric variable has already been cached.
    /// If so, don't do anything. Otherwise, allocate and cache it.
    pub fn new_const<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, f: F) {
        self.0
            .entry(FWrap(f))
            .or_insert_with(|| allocate_constant(&mut cs.namespace(|| f.hex_digits()), f));
    }

    #[inline]
    pub fn get_const(&self, f: F) -> Result<&AllocatedNum<F>> {
        self.0
            .get(&FWrap(f))
            .ok_or_else(|| anyhow!("Global allocation not found for {}", f.hex_digits()))
    }

    #[inline]
    fn get_const_cloned(&self, f: F) -> Result<AllocatedNum<F>> {
        self.get_const(f).cloned()
    }

    #[inline]
    pub fn get_tag<T: Tag>(&self, tag: &T) -> Result<&AllocatedNum<F>> {
        self.get_const(tag.to_field())
    }

    #[inline]
    pub fn get_tag_cloned<T: Tag>(&self, tag: &T) -> Result<AllocatedNum<F>> {
        self.get_tag(tag).cloned()
    }

    #[inline]
    pub fn get_allocated_ptr<T: Tag>(&self, tag: &T, hash: F) -> Result<AllocatedPtr<F>> {
        Ok(AllocatedPtr::from_parts(
            self.get_tag_cloned(tag)?,
            self.get_const_cloned(hash)?,
        ))
    }

    pub fn get_allocated_ptr_from_ptr(
        &self,
        ptr: &Ptr<F>,
        store: &Store<F>,
    ) -> Result<AllocatedPtr<F>> {
        let crate::z_ptr::ZPtr(tag, hash) = store.hash_ptr(ptr);
        self.get_allocated_ptr(&tag, hash)
    }
}

pub(crate) type BoundAllocations<F> = VarMap<AllocatedVal<F>>;

impl<F: LurkField> BoundAllocations<F> {
    fn get_many_ptr(&self, args: &[Var]) -> Result<Vec<AllocatedPtr<F>>> {
        args.iter().map(|arg| self.get_ptr(arg).cloned()).collect()
    }

    fn get_ptr(&self, var: &Var) -> Result<&AllocatedPtr<F>> {
        if let AllocatedVal::Pointer(ptr) = self.get(var)? {
            return Ok(ptr);
        }
        bail!("Expected {var} to be a pointer")
    }

    fn insert_ptr(&mut self, var: Var, ptr: AllocatedPtr<F>) -> Option<AllocatedVal<F>> {
        self.insert(var, AllocatedVal::Pointer(ptr))
    }

    fn get_bool(&self, var: &Var) -> Result<&Boolean> {
        if let AllocatedVal::Boolean(b) = self.get(var)? {
            return Ok(b);
        }
        bail!("Expected {var} to be a boolean")
    }

    fn insert_bool(&mut self, var: Var, b: Boolean) -> Option<AllocatedVal<F>> {
        self.insert(var, AllocatedVal::Boolean(b))
    }
}

fn allocate_img_for_slot<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    slot: &Slot,
    preallocated_preimg: Vec<AllocatedNum<F>>,
    store: &Store<F>,
) -> Result<AllocatedVal<F>> {
    let cs = cs.namespace(|| format!("image for slot {slot}"));
    let preallocated_img = {
        match slot.typ {
            SlotType::Hash4 => AllocatedVal::Number(hash_poseidon(
                cs,
                preallocated_preimg,
                store.poseidon_cache.constants.c4(),
            )?),
            SlotType::Hash6 => AllocatedVal::Number(hash_poseidon(
                cs,
                preallocated_preimg,
                store.poseidon_cache.constants.c6(),
            )?),
            SlotType::Hash8 => AllocatedVal::Number(hash_poseidon(
                cs,
                preallocated_preimg,
                store.poseidon_cache.constants.c8(),
            )?),
            SlotType::Commitment => AllocatedVal::Number(hash_poseidon(
                cs,
                preallocated_preimg,
                store.poseidon_cache.constants.c3(),
            )?),
            SlotType::BitDecomp => {
                AllocatedVal::Bits(preallocated_preimg[0].to_bits_le_strict(cs)?)
            }
        }
    };
    Ok(preallocated_img)
}

pub(crate) fn allocate_slot<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    slot_data: &Option<SlotData<F>>,
    slot_idx: usize,
    slot_type: SlotType,
    store: &Store<F>,
) -> Result<(Vec<AllocatedNum<F>>, AllocatedVal<F>)> {
    let slot = Slot {
        idx: slot_idx,
        typ: slot_type,
    };
    if let Some(slot_data) = slot_data {
        assert!(slot_type.is_compatible(slot_data));

        // Allocate the preimage because the image depends on it
        let mut preallocated_preimg = Vec::with_capacity(slot_type.preimg_size());

        match slot_data {
            SlotData::PtrVec(ptr_vec) => {
                let mut component_idx = 0;
                for ptr in ptr_vec {
                    let z_ptr = store.hash_ptr(ptr);

                    // allocate pointer tag
                    preallocated_preimg.push(AllocatedNum::alloc_infallible(
                        cs.namespace(|| format!("component {component_idx} slot {slot}")),
                        || z_ptr.tag_field(),
                    ));

                    component_idx += 1;

                    // allocate pointer hash
                    preallocated_preimg.push(AllocatedNum::alloc_infallible(
                        cs.namespace(|| format!("component {component_idx} slot {slot}")),
                        || *z_ptr.value(),
                    ));

                    component_idx += 1;
                }
            }
            SlotData::FPtr(f, ptr) => {
                let z_ptr = store.hash_ptr(ptr);
                // allocate first component
                preallocated_preimg.push(AllocatedNum::alloc_infallible(
                    cs.namespace(|| format!("component 0 slot {slot}")),
                    || *f,
                ));
                // allocate second component
                preallocated_preimg.push(AllocatedNum::alloc_infallible(
                    cs.namespace(|| format!("component 1 slot {slot}")),
                    || z_ptr.tag_field(),
                ));
                // allocate third component
                preallocated_preimg.push(AllocatedNum::alloc_infallible(
                    cs.namespace(|| format!("component 2 slot {slot}")),
                    || *z_ptr.value(),
                ));
            }
            SlotData::F(a) => {
                preallocated_preimg.push(AllocatedNum::alloc_infallible(
                    cs.namespace(|| format!("component 0 slot {slot}")),
                    || *a,
                ));
            }
        }

        // Allocate the image by calling the arithmetic function according
        // to the slot type
        let preallocated_img =
            allocate_img_for_slot(cs, &slot, preallocated_preimg.clone(), store)?;

        Ok((preallocated_preimg, preallocated_img))
    } else {
        let preallocated_preimg: Vec<_> = (0..slot_type.preimg_size())
            .map(|component_idx| {
                AllocatedNum::alloc_infallible(
                    cs.namespace(|| format!("component {component_idx} slot {slot}")),
                    || F::ZERO,
                )
            })
            .collect();

        let preallocated_img =
            allocate_img_for_slot(cs, &slot, preallocated_preimg.clone(), store)?;

        Ok((preallocated_preimg, preallocated_img))
    }
}

/// Allocates unconstrained slots
pub(crate) fn allocate_slots<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    slots_data: &[Option<SlotData<F>>],
    slot_type: SlotType,
    num_slots: usize,
    store: &Store<F>,
) -> Result<Vec<(Vec<AllocatedNum<F>>, AllocatedVal<F>)>> {
    assert!(
        slots_data.len() == num_slots,
        "collected preimages not equal to the number of available slots"
    );

    let mut preallocations = Vec::with_capacity(num_slots);

    // We must perform the allocations for the slots containing data collected
    // by the interpreter. The `None` cases must be filled with dummy values
    for (slot_idx, slot_data) in slots_data.iter().enumerate() {
        preallocations.push(allocate_slot(cs, slot_data, slot_idx, slot_type, store)?);
    }

    Ok(preallocations)
}

pub fn build_slots_allocations<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    store: &Store<F>,
    frame: &Frame<F>,
    slot_counter: &SlotsCounter,
) -> Result<SlotsAllocations<F>> {
    let hash4 = allocate_slots(
        cs,
        &frame.hints.hash4,
        SlotType::Hash4,
        slot_counter.hash4,
        store,
    )?;

    let hash6 = allocate_slots(
        cs,
        &frame.hints.hash6,
        SlotType::Hash6,
        slot_counter.hash6,
        store,
    )?;

    let hash8 = allocate_slots(
        cs,
        &frame.hints.hash8,
        SlotType::Hash8,
        slot_counter.hash8,
        store,
    )?;

    let commitment = allocate_slots(
        cs,
        &frame.hints.commitment,
        SlotType::Commitment,
        slot_counter.commitment,
        store,
    )?;

    let bit_decomp = allocate_slots(
        cs,
        &frame.hints.bit_decomp,
        SlotType::BitDecomp,
        slot_counter.bit_decomp,
        store,
    )?;

    Ok(SlotsAllocations {
        hash4,
        hash6,
        hash8,
        commitment,
        bit_decomp,
    })
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
                    g.new_const(cs, tag.to_field());
                }
                Op::Lit(_, lit) => {
                    let lit_ptr = lit.to_ptr(store);
                    let lit_z_ptr = store.hash_ptr(&lit_ptr);
                    g.new_const(cs, lit_z_ptr.tag_field());
                    g.new_const(cs, *lit_z_ptr.value());
                }
                Op::Zero(_, tag) => {
                    g.new_const(cs, tag.to_field());
                    g.new_const(cs, F::ZERO);
                }
                Op::Hash3Zeros(_, tag) => {
                    g.new_const(cs, tag.to_field());
                    g.new_const(cs, store.hash3zeros);
                }
                Op::Hash4Zeros(_, tag) => {
                    g.new_const(cs, tag.to_field());
                    g.new_const(cs, store.hash4zeros);
                }
                Op::Hash6Zeros(_, tag) => {
                    g.new_const(cs, tag.to_field());
                    g.new_const(cs, store.hash6zeros);
                }
                Op::Hash8Zeros(_, tag) => {
                    g.new_const(cs, tag.to_field());
                    g.new_const(cs, store.hash8zeros);
                }
                Op::Not(..)
                | Op::And(..)
                | Op::Or(..)
                | Op::Add(..)
                | Op::Sub(..)
                | Op::Mul(..)
                | Op::Lt(..)
                | Op::Trunc(..)
                | Op::DivRem64(..) => {
                    g.new_const(cs, Num.to_field());
                }
                Op::Div(..) => {
                    g.new_const(cs, Num.to_field());
                    g.new_const(cs, F::ONE);
                }
                Op::Hide(..) | Op::Open(..) => {
                    g.new_const(cs, Num.to_field());
                    g.new_const(cs, Comm.to_field());
                }
                _ => (),
            }
        }
        match &self.ctrl {
            Ctrl::If(.., a, b) => {
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
                g.new_const(cs, Sym.to_field());
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

struct RecursiveContext<'a, F: LurkField, C: Coprocessor<F>> {
    lang: &'a Lang<F, C>,
    store: &'a Store<F>,
    global_allocator: &'a GlobalAllocator<F>,
    hash4_slots: &'a [&'a (Vec<AllocatedNum<F>>, AllocatedVal<F>)],
    hash6_slots: &'a [&'a (Vec<AllocatedNum<F>>, AllocatedVal<F>)],
    hash8_slots: &'a [&'a (Vec<AllocatedNum<F>>, AllocatedVal<F>)],
    commitment_slots: &'a [&'a (Vec<AllocatedNum<F>>, AllocatedVal<F>)],
    bit_decomp_slots: &'a [&'a (Vec<AllocatedNum<F>>, AllocatedVal<F>)],
    blank: bool,
    call_outputs: &'a VecDeque<Vec<Ptr<F>>>,
    call_idx: usize,
    cproc_outputs: &'a [Vec<Ptr<F>>],
}

fn synthesize_block<F: LurkField, CS: ConstraintSystem<F>, C: Coprocessor<F>>(
    cs: &mut CS,
    block: &Block,
    not_dummy: &Boolean,
    next_slot: &mut SlotsCounter,
    bound_allocations: &mut BoundAllocations<F>,
    preallocated_outputs: &Vec<AllocatedPtr<F>>,
    ctx: &mut RecursiveContext<'_, F, C>,
    mut cproc_idx: usize,
) -> Result<()> {
    for (op_idx, op) in block.ops.iter().enumerate() {
        let mut cs = cs.namespace(|| format!("op {op_idx}"));

        macro_rules! cons_helper {
            ( $img: expr, $tag: expr, $preimg: expr, $slot: expr ) => {
                // Retrieve allocated preimage
                let allocated_preimg = bound_allocations.get_many_ptr($preimg)?;

                // Retrieve the preallocated preimage and image for this slot
                let (preallocated_preimg, preallocated_img_hash) = match $slot {
                    SlotType::Hash4 => &ctx.hash4_slots[next_slot.consume_hash4()],
                    SlotType::Hash6 => &ctx.hash6_slots[next_slot.consume_hash6()],
                    SlotType::Hash8 => &ctx.hash8_slots[next_slot.consume_hash8()],
                    _ => panic!("Invalid slot type for cons_helper macro"),
                };

                // For each component of the preimage, add implication constraints
                // for its tag and hash
                for (i, allocated_ptr) in allocated_preimg.iter().enumerate() {
                    let var = &$preimg[i];
                    let ptr_idx = 2 * i;
                    implies_equal(
                        &mut cs.namespace(|| format!("implies equal {var}.tag pos {i}")),
                        not_dummy,
                        allocated_ptr.tag(),
                        &preallocated_preimg[ptr_idx], // tag index
                    );
                    implies_equal(
                        &mut cs.namespace(|| format!("implies equal {var}.hash pos {i}")),
                        not_dummy,
                        allocated_ptr.hash(),
                        &preallocated_preimg[ptr_idx + 1], // hash index
                    );
                }

                // Allocate the image tag if it hasn't been allocated before,
                // create the full image pointer and add it to bound allocations
                let img_tag = ctx.global_allocator.get_tag_cloned($tag)?;
                let AllocatedVal::Number(img_hash) = preallocated_img_hash else {
                    bail!("Expected number")
                };
                let img_ptr = AllocatedPtr::from_parts(img_tag, img_hash.clone());
                bound_allocations.insert_ptr($img, img_ptr);
            };
        }

        macro_rules! decons_helper {
            ( $preimg: expr, $img: expr, $slot: expr ) => {
                // Retrieve allocated image
                let allocated_img = bound_allocations.get_ptr($img)?;

                // Retrieve the preallocated preimage and image for this slot
                let (preallocated_preimg, preallocated_img_hash) = match $slot {
                    SlotType::Hash4 => &ctx.hash4_slots[next_slot.consume_hash4()],
                    SlotType::Hash6 => &ctx.hash6_slots[next_slot.consume_hash6()],
                    SlotType::Hash8 => &ctx.hash8_slots[next_slot.consume_hash8()],
                    _ => panic!("Invalid slot type for decons_helper macro"),
                };

                // Add the implication constraint for the image
                let AllocatedVal::Number(img_hash) = preallocated_img_hash else {
                    bail!("Expected number")
                };
                implies_equal(
                    &mut cs.namespace(|| format!("implies equal {}.hash", $img)),
                    not_dummy,
                    allocated_img.hash(),
                    img_hash,
                );

                // Retrieve preimage hashes and tags create the full preimage pointers
                // and add them to bound allocations
                for i in 0..preallocated_preimg.len() / 2 {
                    let preimg_tag = &preallocated_preimg[2 * i];
                    let preimg_hash = &preallocated_preimg[2 * i + 1];
                    let preimg_ptr =
                        AllocatedPtr::from_parts(preimg_tag.clone(), preimg_hash.clone());
                    bound_allocations.insert_ptr($preimg[i].clone(), preimg_ptr);
                }
            };
        }

        match op {
            Op::Cproc(out, sym, inp) => {
                let cproc = ctx
                    .lang
                    .lookup_by_sym(sym)
                    .ok_or_else(|| anyhow!("Coprocessor for {sym} not found"))?;
                let not_dummy_and_not_blank = not_dummy.get_value() == Some(true) && !ctx.blank;
                let collected_z_ptrs = if not_dummy_and_not_blank {
                    let collected_ptrs = &ctx.cproc_outputs[cproc_idx];
                    if out.len() != collected_ptrs.len() {
                        bail!("Incompatible output length for coprocessor {sym}")
                    }
                    collected_ptrs
                        .iter()
                        .map(|ptr| ctx.store.hash_ptr(ptr))
                        .collect::<Vec<_>>()
                } else {
                    vec![ZPtr::dummy(); out.len()]
                };
                if cproc.has_circuit() {
                    // call the coprocessor's synthesize and then make sure that
                    // the output matches the data collected during interpretation
                    let inp_ptrs = bound_allocations.get_many_ptr(inp)?;
                    let synthesize_output = cproc.synthesize_internal(
                        &mut cs.namespace(|| format!("Coprocessor {sym}")),
                        ctx.global_allocator,
                        ctx.store,
                        not_dummy,
                        &inp_ptrs,
                    )?;
                    if out.len() != synthesize_output.len() {
                        bail!("Incompatible output length for coprocessor {sym}")
                    }
                    for ((i, var), ptr) in out.iter().enumerate().zip(synthesize_output) {
                        if not_dummy_and_not_blank {
                            let z_ptr = &collected_z_ptrs[i];
                            if ptr.tag().get_value() != Some(z_ptr.tag_field())
                                || ptr.hash().get_value() != Some(*z_ptr.value())
                            {
                                bail!("Mismatch between evaluate and synthesize outputs for coprocessor {sym} (pointer {i})")
                            }
                        }
                        bound_allocations.insert(var.clone(), AllocatedVal::Pointer(ptr));
                    }
                } else {
                    // just move on with the data that was collected from interpretation
                    for ((i, var), z_ptr) in out.iter().enumerate().zip(collected_z_ptrs) {
                        let allocated_tag = AllocatedNum::alloc_infallible(
                            &mut cs.namespace(|| format!("tag for pointer {i} from cproc {sym}")),
                            || z_ptr.tag_field(),
                        );
                        let allocated_hash = AllocatedNum::alloc_infallible(
                            &mut cs.namespace(|| format!("hash for pointer {i} from cproc {sym}")),
                            || *z_ptr.value(),
                        );
                        bound_allocations.insert(
                            var.clone(),
                            AllocatedVal::Pointer(AllocatedPtr::from_parts(
                                allocated_tag,
                                allocated_hash,
                            )),
                        );
                    }
                }
                cproc_idx += 1;
            }
            Op::Call(out, func, inp) => {
                // Allocate the output pointers that the `func` will return to.
                // These should be unconstrained as of yet, and will be constrained
                // by the return statements inside `func`.
                // Note that, because there's currently no way of deferring giving
                // a value to the allocated nums to be filled later, we must either
                // add the results of the call to the witness, or recompute them.
                let not_dummy_and_not_blank = not_dummy.get_value() == Some(true) && !ctx.blank;
                let output_z_ptrs = if not_dummy_and_not_blank {
                    let z_ptrs = ctx.call_outputs[ctx.call_idx]
                        .iter()
                        .map(|ptr| ctx.store.hash_ptr(ptr))
                        .collect::<Vec<_>>();
                    ctx.call_idx += 1;
                    assert_eq!(z_ptrs.len(), out.len());
                    z_ptrs
                } else {
                    vec![ZPtr::dummy(); out.len()]
                };
                let mut output_ptrs = Vec::with_capacity(out.len());
                for (z_ptr, var) in output_z_ptrs.into_iter().zip(out.iter()) {
                    let ptr =
                        AllocatedPtr::alloc(&mut cs.namespace(|| format!("var: {var}")), || {
                            Ok(z_ptr)
                        })?;
                    bound_allocations.insert_ptr(var.clone(), ptr.clone());
                    output_ptrs.push(ptr);
                }
                // Get the pointers for the input, i.e. the arguments
                let args = bound_allocations.get_many_ptr(inp)?;
                // These are the input parameters (formal variables)
                let param_list = func.input_params.iter();
                // Now we bind the `Func`'s input parameters to the arguments in the call.
                param_list.zip(args.into_iter()).for_each(|(param, arg)| {
                    bound_allocations.insert_ptr(param.clone(), arg);
                });
                // Finally, we synthesize the circuit for the function body
                synthesize_block(
                    &mut cs.namespace(|| "call"),
                    &func.body,
                    not_dummy,
                    next_slot,
                    bound_allocations,
                    &output_ptrs,
                    ctx,
                    cproc_idx,
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
            Op::Copy(tgt, src) => {
                bound_allocations.insert(tgt.clone(), bound_allocations.get_cloned(src)?);
            }
            Op::Zero(tgt, tag) => {
                bound_allocations.insert_ptr(
                    tgt.clone(),
                    ctx.global_allocator.get_allocated_ptr(tag, F::ZERO)?,
                );
            }
            Op::Hash3Zeros(tgt, tag) => {
                bound_allocations.insert_ptr(
                    tgt.clone(),
                    ctx.global_allocator
                        .get_allocated_ptr(tag, ctx.store.hash3zeros)?,
                );
            }
            Op::Hash4Zeros(tgt, tag) => {
                bound_allocations.insert_ptr(
                    tgt.clone(),
                    ctx.global_allocator
                        .get_allocated_ptr(tag, ctx.store.hash4zeros)?,
                );
            }
            Op::Hash6Zeros(tgt, tag) => {
                bound_allocations.insert_ptr(
                    tgt.clone(),
                    ctx.global_allocator
                        .get_allocated_ptr(tag, ctx.store.hash6zeros)?,
                );
            }
            Op::Hash8Zeros(tgt, tag) => {
                bound_allocations.insert_ptr(
                    tgt.clone(),
                    ctx.global_allocator
                        .get_allocated_ptr(tag, ctx.store.hash8zeros)?,
                );
            }
            Op::Lit(tgt, lit) => {
                let allocated_ptr = ctx
                    .global_allocator
                    .get_allocated_ptr_from_ptr(&lit.to_ptr(ctx.store), ctx.store)?;
                bound_allocations.insert_ptr(tgt.clone(), allocated_ptr);
            }
            Op::Cast(tgt, tag, src) => {
                let src = bound_allocations.get_ptr(src)?;
                let tag = ctx.global_allocator.get_tag_cloned(tag)?;
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
                let c = and(&mut cs.namespace(|| "and"), a, b)?;
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
                let tag = ctx.global_allocator.get_tag_cloned(&Num)?;
                let c = AllocatedPtr::from_parts(tag, c_num);
                bound_allocations.insert_ptr(tgt.clone(), c);
            }
            Op::Sub(tgt, a, b) => {
                let a = bound_allocations.get_ptr(a)?;
                let b = bound_allocations.get_ptr(b)?;
                let a_num = a.hash();
                let b_num = b.hash();
                let c_num = sub(cs.namespace(|| "sub"), a_num, b_num)?;
                let tag = ctx.global_allocator.get_tag_cloned(&Num)?;
                let c = AllocatedPtr::from_parts(tag, c_num);
                bound_allocations.insert_ptr(tgt.clone(), c);
            }
            Op::Mul(tgt, a, b) => {
                let a = bound_allocations.get_ptr(a)?;
                let b = bound_allocations.get_ptr(b)?;
                let a_num = a.hash();
                let b_num = b.hash();
                let c_num = mul(cs.namespace(|| "mul"), a_num, b_num)?;
                let tag = ctx.global_allocator.get_tag_cloned(&Num)?;
                let c = AllocatedPtr::from_parts(tag, c_num);
                bound_allocations.insert_ptr(tgt.clone(), c);
            }
            Op::Div(tgt, a, b) => {
                let a = bound_allocations.get_ptr(a)?;
                let b = bound_allocations.get_ptr(b)?;
                let a_num = a.hash();
                let b_num = b.hash();

                let b_is_zero = &alloc_is_zero(cs.namespace(|| "b_is_zero"), b_num)?;
                let one = ctx.global_allocator.get_const(F::ONE)?;

                let divisor = pick(
                    cs.namespace(|| "maybe-dummy divisor"),
                    b_is_zero,
                    one,
                    b_num,
                )?;

                let quotient = div(cs.namespace(|| "quotient"), a_num, &divisor)?;

                let tag = ctx.global_allocator.get_tag_cloned(&Num)?;
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
                // Get slot allocated preimages/bits for the double of a, b, a-b
                let (double_a_preimg, double_a_bits) =
                    &ctx.bit_decomp_slots[next_slot.consume_bit_decomp()];
                let AllocatedVal::Bits(double_a_bits) = double_a_bits else {
                    panic!("Expected bits")
                };
                let (double_b_preimg, double_b_bits) =
                    &ctx.bit_decomp_slots[next_slot.consume_bit_decomp()];
                let AllocatedVal::Bits(double_b_bits) = double_b_bits else {
                    panic!("Expected bits")
                };
                let (double_diff_preimg, double_diff_bits) =
                    &ctx.bit_decomp_slots[next_slot.consume_bit_decomp()];
                let AllocatedVal::Bits(double_diff_bits) = double_diff_bits else {
                    panic!("Expected bits")
                };
                // Check that the slot allocated preimages are the double of a, b, a-b
                implies_equal(
                    &mut cs.namespace(|| "implies equal for a_preimg"),
                    not_dummy,
                    &double_a,
                    &double_a_preimg[0],
                );
                implies_equal(
                    &mut cs.namespace(|| "implies equal for b_preimg"),
                    not_dummy,
                    &double_b,
                    &double_b_preimg[0],
                );
                implies_equal(
                    &mut cs.namespace(|| "implies equal for diff_preimg"),
                    not_dummy,
                    &double_diff,
                    &double_diff_preimg[0],
                );

                // The number is negative if the least significant bit of its double is 1
                let a_is_negative = double_a_bits.get(0).unwrap();
                let b_is_negative = double_b_bits.get(0).unwrap();
                let diff_is_negative = double_diff_bits.get(0).unwrap();

                // Two numbers have the same sign if both are negative or both are positive, i.e.
                let same_sign =
                    Boolean::xor(cs.namespace(|| "same_sign"), a_is_negative, b_is_negative)?.not();

                // Finally, a < b iff (same_sign && diff < 0) || (!same_sign && a < 0)
                let and1 = and(&mut cs.namespace(|| "and1"), &same_sign, diff_is_negative)?;
                let and2 = and(
                    &mut cs.namespace(|| "and2"),
                    &same_sign.not(),
                    a_is_negative,
                )?;
                let lt = or(&mut cs.namespace(|| "or"), &and1, &and2)?;
                bound_allocations.insert_bool(tgt.clone(), lt.clone());
            }
            Op::Trunc(tgt, a, n) => {
                assert!(*n <= 64);
                let a = bound_allocations.get_ptr(a)?;
                let (preallocated_preimg, trunc_bits) =
                    &ctx.bit_decomp_slots[next_slot.consume_bit_decomp()];
                implies_equal(
                    &mut cs.namespace(|| "implies equal component trunc"),
                    not_dummy,
                    a.hash(),
                    &preallocated_preimg[0],
                );
                let AllocatedVal::Bits(trunc_bits) = trunc_bits else {
                    panic!("Expected bits")
                };
                let trunc_bits = &trunc_bits[0..*n as usize];
                let trunc = AllocatedNum::alloc(cs.namespace(|| "trunc"), || {
                    let b = if *n < 64 { (1 << *n) - 1 } else { u64::MAX };
                    a.hash()
                        .get_value()
                        .map(|a| F::from_u64(a.to_u64_unchecked() & b))
                        .ok_or(SynthesisError::AssignmentMissing)
                })?;
                implies_pack(
                    cs.namespace(|| "implies_trunc"),
                    not_dummy,
                    trunc_bits,
                    &trunc,
                );
                let tag = ctx.global_allocator.get_tag_cloned(&Num)?;
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
                let tag = ctx.global_allocator.get_tag_cloned(&Num)?;
                let div_ptr = AllocatedPtr::from_parts(tag.clone(), div);
                let rem_ptr = AllocatedPtr::from_parts(tag, rem);
                bound_allocations.insert_ptr(tgt[0].clone(), div_ptr);
                bound_allocations.insert_ptr(tgt[1].clone(), rem_ptr);
            }
            Op::Emit(_) => (),
            Op::Hide(tgt, sec, pay) => {
                let sec = bound_allocations.get_ptr(sec)?;
                let pay = bound_allocations.get_ptr(pay)?;
                let sec_tag = ctx.global_allocator.get_const(Num.to_field())?;
                let (preallocated_preimg, hash) =
                    &ctx.commitment_slots[next_slot.consume_commitment()];
                let AllocatedVal::Number(hash) = hash else {
                    panic!("Excepted number")
                };
                implies_equal(
                    &mut cs.namespace(|| "implies equal secret.tag"),
                    not_dummy,
                    sec.tag(),
                    sec_tag,
                );
                implies_equal(
                    &mut cs.namespace(|| "implies equal secret.hash"),
                    not_dummy,
                    sec.hash(),
                    &preallocated_preimg[0],
                );
                implies_equal(
                    &mut cs.namespace(|| "implies equal payload.tag"),
                    not_dummy,
                    pay.tag(),
                    &preallocated_preimg[1],
                );
                implies_equal(
                    &mut cs.namespace(|| "implies equal payload.hash"),
                    not_dummy,
                    pay.hash(),
                    &preallocated_preimg[2],
                );
                let tag = ctx.global_allocator.get_tag_cloned(&Comm)?;
                let allocated_ptr = AllocatedPtr::from_parts(tag, hash.clone());
                bound_allocations.insert_ptr(tgt.clone(), allocated_ptr);
            }
            Op::Open(sec, pay, comm) => {
                let comm = bound_allocations.get_ptr(comm)?;
                let (preallocated_preimg, com_hash) =
                    &ctx.commitment_slots[next_slot.consume_commitment()];
                let comm_tag = ctx.global_allocator.get_const(Comm.to_field())?;
                let AllocatedVal::Number(com_hash) = com_hash else {
                    panic!("Excepted number")
                };
                implies_equal(
                    &mut cs.namespace(|| "implies equal comm.tag"),
                    not_dummy,
                    comm.tag(),
                    comm_tag,
                );
                implies_equal(
                    &mut cs.namespace(|| "implies equal comm.hash "),
                    not_dummy,
                    comm.hash(),
                    com_hash,
                );
                let sec_tag = ctx.global_allocator.get_tag_cloned(&Num)?;
                let allocated_sec_ptr =
                    AllocatedPtr::from_parts(sec_tag, preallocated_preimg[0].clone());
                let allocated_pay_ptr = AllocatedPtr::from_parts(
                    preallocated_preimg[1].clone(),
                    preallocated_preimg[2].clone(),
                );
                bound_allocations.insert_ptr(sec.clone(), allocated_sec_ptr);
                bound_allocations.insert_ptr(pay.clone(), allocated_pay_ptr);
            }
        }
    }

    let mut synthesize_match = |matched: &AllocatedNum<F>,
                                cases: &[(F, &Block)],
                                def: &Option<Box<Block>>,
                                bound_allocations: &mut VarMap<AllocatedVal<F>>,
                                ctx: &mut RecursiveContext<'_, F, C>|
     -> Result<Vec<SlotsCounter>> {
        // * One `Boolean` for each case
        // * Maybe one `Boolean` for the default case
        let selector_size = cases.len() + usize::from(def.is_some());
        let mut selector = Vec::with_capacity(selector_size);
        let mut branch_slots = Vec::with_capacity(cases.len());
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
                &mut cs.namespace(|| format!("{i}.implies_equal_const")),
                &not_dummy_and_has_match,
                matched,
                *f,
            );

            selector.push(not_dummy_and_has_match.clone());

            let mut branch_slot = *next_slot;
            synthesize_block(
                &mut cs.namespace(|| format!("{i}")),
                block,
                &not_dummy_and_has_match,
                &mut branch_slot,
                bound_allocations,
                preallocated_outputs,
                ctx,
                cproc_idx,
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
                cs.namespace(|| "_.allocated_bit"),
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

            synthesize_block(
                &mut cs.namespace(|| "_"),
                def,
                &is_default,
                next_slot,
                bound_allocations,
                preallocated_outputs,
                ctx,
                cproc_idx,
            )?;

            // Pushing `is_default` to `selector` to enforce summation = 1
            selector.push(is_default);
        }

        // Now we need to enforce that exactly one path was taken. We do that by enforcing
        // that the sum of the previously collected `Boolean`s is one. But, of course, this
        // is irrelevant if we're on a virtual path and thus we use an implication gadget.
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
                let allocated_ptr = bound_allocations.get_ptr(return_var)?;

                allocated_ptr.implies_ptr_equal(
                    &mut cs.namespace(|| format!("implies_ptr_equal {return_var} pos {i}")),
                    not_dummy,
                    &preallocated_outputs[i],
                );
            }
            Ok(())
        }
        Ctrl::If(b, true_block, false_block) => {
            let b = bound_allocations.get_bool(b)?;
            let b_not_dummy = and(&mut cs.namespace(|| "b and not_dummy"), b, not_dummy)?;
            let not_b_not_dummy = and(
                &mut cs.namespace(|| "not_b and not_dummy"),
                &b.not(),
                not_dummy,
            )?;
            let mut branch_slot = *next_slot;
            synthesize_block(
                &mut cs.namespace(|| "if_eq.true"),
                true_block,
                &b_not_dummy,
                &mut branch_slot,
                bound_allocations,
                preallocated_outputs,
                ctx,
                cproc_idx,
            )?;
            synthesize_block(
                &mut cs.namespace(|| "if_eq.false"),
                false_block,
                &not_b_not_dummy,
                next_slot,
                bound_allocations,
                preallocated_outputs,
                ctx,
                cproc_idx,
            )?;
            *next_slot = next_slot.cmp_max(branch_slot);
            Ok(())
        }
        Ctrl::MatchTag(match_var, cases, def) => {
            let matched = bound_allocations.get_ptr(match_var)?.tag().clone();
            let cases_vec = cases
                .iter()
                .map(|(tag, block)| (tag.to_field::<F>(), block))
                .collect::<Vec<_>>();
            let branch_slots = synthesize_match(&matched, &cases_vec, def, bound_allocations, ctx)?;

            // The number of slots the match used is the max number of slots of each branch
            *next_slot = next_slot.fold_max(branch_slots);
            Ok(())
        }
        Ctrl::MatchSymbol(match_var, cases, def) => {
            let match_var_ptr = bound_allocations.get_ptr(match_var)?.clone();

            let mut cases_vec = Vec::with_capacity(cases.len());
            for (sym, block) in cases {
                let sym_ptr = ctx.store.intern_symbol(sym);
                let sym_hash = *ctx.store.hash_ptr(&sym_ptr).value();
                cases_vec.push((sym_hash, block));
            }

            let branch_slots = synthesize_match(
                match_var_ptr.hash(),
                &cases_vec,
                def,
                bound_allocations,
                ctx,
            )?;

            // Now we enforce `MatchSymbol`'s tag
            let sym_tag = ctx.global_allocator.get_const(Sym.to_field())?;
            implies_equal(
                &mut cs.namespace(|| format!("implies equal {match_var}.tag")),
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

impl Func {
    /// Add input to bound_allocations
    pub(crate) fn bind_input<F: LurkField>(
        &self,
        input: &[AllocatedPtr<F>],
        bound_allocations: &mut BoundAllocations<F>,
    ) {
        assert_eq!(input.len(), self.input_params.len());
        for (var, ptr) in self.input_params.iter().zip(input) {
            bound_allocations.insert_ptr(var.clone(), ptr.clone());
        }
    }

    /// Allocates an unconstrained pointer for each output of the frame
    fn allocate_output<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &Store<F>,
        frame: &Frame<F>,
    ) -> Result<Vec<AllocatedPtr<F>>> {
        assert_eq!(self.output_size, frame.output.len());
        let mut output = Vec::with_capacity(frame.output.len());
        for (i, ptr) in frame.output.iter().enumerate() {
            let zptr = store.hash_ptr(ptr);
            output.push(AllocatedPtr::alloc(
                &mut cs.namespace(|| format!("var: output[{}]", i)),
                || Ok(zptr),
            )?);
        }
        Ok(output)
    }

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
            let zptr = store.hash_ptr(ptr);
            let ptr =
                AllocatedPtr::alloc(&mut cs.namespace(|| format!("var: {param}")), || Ok(zptr))?;
            bound_allocations.insert_ptr(param.clone(), ptr);
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
    pub fn synthesize_frame<F: LurkField, CS: ConstraintSystem<F>, C: Coprocessor<F>>(
        &self,
        cs: &mut CS,
        store: &Store<F>,
        frame: &Frame<F>,
        global_allocator: &GlobalAllocator<F>,
        bound_allocations: &mut BoundAllocations<F>,
        lang: &Lang<F, C>,
        slots_witness: Option<&[Arc<SlotWitness<F>>]>,
    ) -> Result<Vec<AllocatedPtr<F>>> {
        // Outputs are constrained by the return statement. All functions return
        let preallocated_outputs = self.allocate_output(cs, store, frame)?;

        if let Some(slots_witness) = slots_witness {
            assert!(cs.is_witness_generator());
            slots_witness
                .iter()
                .for_each(|sw| cs.extend_aux(sw.witness.aux_slice()));
            let hash4_upper = frame.hints.hash4.len();
            let hash6_upper = hash4_upper + frame.hints.hash6.len();
            let hash8_upper = hash6_upper + frame.hints.hash8.len();
            let commitment_upper = hash8_upper + frame.hints.commitment.len();
            let bit_decomp_upper = commitment_upper + frame.hints.bit_decomp.len();

            let collect = |lower, upper| {
                slots_witness[lower..upper]
                    .iter()
                    .map(|sw| &sw.allocations)
                    .collect::<Vec<_>>()
            };

            let hash4_slots = &collect(0, hash4_upper);
            let hash6_slots = &collect(hash4_upper, hash6_upper);
            let hash8_slots = &collect(hash6_upper, hash8_upper);
            let commitment_slots = &collect(hash8_upper, commitment_upper);
            let bit_decomp_slots = &collect(commitment_upper, bit_decomp_upper);
            synthesize_block(
                cs,
                &self.body,
                &Boolean::Constant(true),
                &mut SlotsCounter::default(),
                bound_allocations,
                &preallocated_outputs,
                &mut RecursiveContext {
                    lang,
                    store,
                    global_allocator,
                    hash4_slots,
                    hash6_slots,
                    hash8_slots,
                    commitment_slots,
                    bit_decomp_slots,
                    blank: frame.blank,
                    call_outputs: &frame.hints.call_outputs,
                    call_idx: 0,
                    cproc_outputs: &frame.hints.cproc_outputs,
                },
                0,
            )?;
        } else {
            assert!(!cs.is_witness_generator());
            let slots_allocations = build_slots_allocations(cs, store, frame, &self.slots_count)?;
            let hash4_slots = &slots_allocations.hash4.iter().collect::<Vec<_>>();
            let hash6_slots = &slots_allocations.hash6.iter().collect::<Vec<_>>();
            let hash8_slots = &slots_allocations.hash8.iter().collect::<Vec<_>>();
            let commitment_slots = &slots_allocations.commitment.iter().collect::<Vec<_>>();
            let bit_decomp_slots = &slots_allocations.bit_decomp.iter().collect::<Vec<_>>();
            synthesize_block(
                cs,
                &self.body,
                &Boolean::Constant(true),
                &mut SlotsCounter::default(),
                bound_allocations,
                &preallocated_outputs,
                &mut RecursiveContext {
                    lang,
                    store,
                    global_allocator,
                    hash4_slots,
                    hash6_slots,
                    hash8_slots,
                    commitment_slots,
                    bit_decomp_slots,
                    blank: frame.blank,
                    call_outputs: &frame.hints.call_outputs,
                    call_idx: 0,
                    cproc_outputs: &frame.hints.cproc_outputs,
                },
                0,
            )?;
        }

        Ok(preallocated_outputs)
    }

    /// Helper API for tests
    pub fn synthesize_frame_aux<F: LurkField, CS: ConstraintSystem<F>, C: Coprocessor<F>>(
        &self,
        cs: &mut CS,
        store: &Store<F>,
        frame: &Frame<F>,
        lang: &Lang<F, C>,
    ) -> Result<()> {
        let bound_allocations = &mut BoundAllocations::new();
        let global_allocator = self.alloc_globals(cs, store)?;
        self.allocate_input(cs, store, frame, bound_allocations)?;
        self.synthesize_frame(
            cs,
            store,
            frame,
            &global_allocator,
            bound_allocations,
            lang,
            None,
        )?;
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
            is_nested: bool,
        ) -> usize {
            let mut num_constraints = 0;
            for op in &block.ops {
                match op {
                    Op::Call(_, func, _) => {
                        num_constraints += recurse(&func.body, globals, store, is_nested);
                    }
                    Op::Zero(_, tag) => {
                        // constrain tag and hash
                        globals.insert(FWrap(tag.to_field()));
                        globals.insert(FWrap(F::ZERO));
                    }
                    Op::Hash3Zeros(_, tag) => {
                        // constrain tag and hash
                        globals.insert(FWrap(tag.to_field()));
                        globals.insert(FWrap(store.hash3zeros));
                    }
                    Op::Hash4Zeros(_, tag) => {
                        // constrain tag and hash
                        globals.insert(FWrap(tag.to_field()));
                        globals.insert(FWrap(store.hash4zeros));
                    }
                    Op::Hash6Zeros(_, tag) => {
                        // constrain tag and hash
                        globals.insert(FWrap(tag.to_field()));
                        globals.insert(FWrap(store.hash6zeros));
                    }
                    Op::Hash8Zeros(_, tag) => {
                        // constrain tag and hash
                        globals.insert(FWrap(tag.to_field()));
                        globals.insert(FWrap(store.hash8zeros));
                    }
                    Op::Lit(_, lit) => {
                        let lit_ptr = lit.to_ptr(store);
                        let lit_z_ptr = store.hash_ptr(&lit_ptr);
                        globals.insert(FWrap(lit_z_ptr.tag_field()));
                        globals.insert(FWrap(*lit_z_ptr.value()));
                    }
                    Op::Cast(_, tag, _) => {
                        globals.insert(FWrap(tag.to_field()));
                    }
                    Op::EqTag(..) | Op::EqVal(..) => {
                        num_constraints += 3;
                    }
                    Op::Add(..) | Op::Sub(..) | Op::Mul(..) => {
                        globals.insert(FWrap(Num.to_field()));
                        num_constraints += 1;
                    }
                    Op::Div(..) => {
                        globals.insert(FWrap(Num.to_field()));
                        globals.insert(FWrap(F::ONE));
                        num_constraints += 5;
                    }
                    Op::Lt(..) => {
                        globals.insert(FWrap(Num.to_field()));
                        num_constraints += 11;
                    }
                    Op::Trunc(..) => {
                        globals.insert(FWrap(Num.to_field()));
                        // 1 implies_equal, 1 implies_pack
                        num_constraints += 2;
                    }
                    Op::DivRem64(..) => {
                        globals.insert(FWrap(Num.to_field()));
                        // three implies_u64, one sub and one linear
                        num_constraints += 197;
                    }
                    Op::Not(..) | Op::Emit(_) | Op::Cproc(..) | Op::Copy(..) => (),
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
                    Op::And(..)
                    | Op::Or(..)
                    | Op::Decons2(..)
                    | Op::Decons3(..)
                    | Op::Decons4(..) => {
                        // one constraint for the image's hash
                        num_constraints += 1;
                    }
                    Op::Hide(..) => {
                        num_constraints += 4;
                        globals.insert(FWrap(Num.to_field()));
                        globals.insert(FWrap(Comm.to_field()));
                    }
                    Op::Open(..) => {
                        num_constraints += 2;
                        globals.insert(FWrap(Num.to_field()));
                        globals.insert(FWrap(Comm.to_field()));
                    }
                }
            }
            match &block.ctrl {
                Ctrl::Return(vars) => num_constraints + 2 * vars.len(),
                Ctrl::If(_, true_block, false_block) => {
                    num_constraints
                        + if is_nested { 2 } else { 0 }
                        + recurse(true_block, globals, store, true)
                        + recurse(false_block, globals, store, true)
                }
                Ctrl::MatchTag(_, cases, def) => {
                    // We allocate one boolean per case and constrain it once
                    // per case. Then we add 1 constraint to enforce only one
                    // case was selected
                    num_constraints += 2 * cases.len() + 1;

                    for block in cases.values() {
                        num_constraints += recurse(block, globals, store, true);
                    }
                    if let Some(def) = def {
                        // constraints for the boolean, the unequalities and the default case
                        num_constraints += 1 + cases.len();
                        num_constraints += recurse(def, globals, store, true);
                    }
                    num_constraints
                }
                Ctrl::MatchSymbol(_, cases, def) => {
                    // First we enforce that the tag of the pointer being matched on
                    // is Sym
                    num_constraints += 1;
                    globals.insert(FWrap(Sym.to_field()));
                    // We allocate one boolean per case and constrain it once
                    // per case. Then we add 1 constraint to enforce only one
                    // case was selected
                    num_constraints += 2 * cases.len() + 1;

                    for block in cases.values() {
                        num_constraints += recurse(block, globals, store, true);
                    }
                    if let Some(def) = def {
                        // constraints for the boolean, the unequalities and the default case
                        num_constraints += 1 + cases.len();
                        num_constraints += recurse(def, globals, store, true);
                    }
                    num_constraints
                }
            }
        }
        let globals = &mut HashSet::default();
        let bit_decomp_cost = match F::FIELD {
            LanguageField::Pallas => 298,
            LanguageField::Vesta => 301,
            _ => todo!(),
        };

        // fixed cost for each slot
        let slot_constraints = 289 * self.slots_count.hash4
            + 337 * self.slots_count.hash6
            + 388 * self.slots_count.hash8
            + 265 * self.slots_count.commitment
            + bit_decomp_cost * self.slots_count.bit_decomp;
        let num_constraints = recurse(&self.body, globals, store, false);
        slot_constraints + num_constraints + globals.len()
    }
}
