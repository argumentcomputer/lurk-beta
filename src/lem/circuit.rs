//! ## Constraint system for LEM
//!
//! This is a high level description of how we generate bellperson constraints for
//! LEM, such that it can be used with Nova folding to implement the Lurk
//! evaluation.
//!
//! Some LEMOPs require expensive gadgets, such as Poseidon hashing. So we use
//! the concept of "slots" to avoid wasting constraints.
//!
//! We've separated the process in three steps:
//!
//! 1. Perform a static analysis to compute the slots that are needed as well as
//! the mapping from LEMOPs to their respective slots. This piece of information
//! will live on a `SlotsInfo` structure, which is populated by the function
//! `LEMOP::slots_info`;
//!
//! 2. Interpret the LEM and collect the data that was generated on each visited
//! slot, along with all bindings from `MetaPtr`s to `Ptr`s. This piece of
//! information will live on a `Frame` structure;
//!
//! 3. Finally build the circuit with `SlotsInfo` and `Frame` at hand. This step
//! is explained in more details in the `LEMOP::synthesize` function.
//!
//! The 3 steps above will be further referred to as *STEP 1*, *STEP 2* and
//! *STEP 3* respectively. STEP 1 should be performed once per slot. Then STEP 2
//! will need as many iterations as it takes to evaluate the Lurk expression and
//! so will STEP 3.

use std::collections::HashMap;

use anyhow::{anyhow, bail, Context, Result};
use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    ConstraintSystem,
};

use crate::circuit::gadgets::{
    constraints::{
        alloc_equal_const, and, enforce_selector_with_premise, implies_equal, implies_equal_zero,
    },
    data::hash_poseidon,
    pointer::AllocatedPtr,
};

use crate::field::{FWrap, LurkField};

use super::{
    interpreter::Frame,
    path::Path,
    pointers::{Ptr, ZPtr},
    store::Store,
    AString, MetaPtr, LEM, LEMCTL, LEMOP,
};

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct SlotsCounter {
    pub hash2: usize,
    pub hash3: usize,
    pub hash4: usize,
}

impl SlotsCounter {
    /// This interface is mostly for testing
    #[inline]
    pub(crate) fn new(num_slots: (usize, usize, usize)) -> Self {
        Self {
            hash2: num_slots.0,
            hash3: num_slots.1,
            hash4: num_slots.2,
        }
    }

    // #[inline]
    // pub(crate) fn next_hash2(&self) -> Self {
    //     Self {
    //         hash2: self.hash2 + 1,
    //         hash3: self.hash3,
    //         hash4: self.hash4,
    //     }
    // }

    // #[inline]
    // pub(crate) fn next_hash3(&self) -> Self {
    //     Self {
    //         hash2: self.hash2,
    //         hash3: self.hash3 + 1,
    //         hash4: self.hash4,
    //     }
    // }

    // #[inline]
    // pub(crate) fn next_hash4(&self) -> Self {
    //     Self {
    //         hash2: self.hash2,
    //         hash3: self.hash3,
    //         hash4: self.hash4 + 1,
    //     }
    // }

    #[inline]
    pub(crate) fn max(&self, other: Self) -> Self {
        use std::cmp::max;
        Self {
            hash2: max(self.hash2, other.hash2),
            hash3: max(self.hash3, other.hash3),
            hash4: max(self.hash4, other.hash4),
        }
    }

    #[inline]
    pub(crate) fn add(&self, other: Self) -> Self {
        Self {
            hash2: self.hash2 + other.hash2,
            hash3: self.hash3 + other.hash3,
            hash4: self.hash4 + other.hash4,
        }
    }
}

impl LEMCTL {
    pub fn count_slots(&self) -> SlotsCounter {
        match self {
            LEMCTL::MatchTag(_, cases) => {
                cases.values().fold(SlotsCounter::default(), |acc, code| {
                    acc.max(code.count_slots())
                })
            }
            LEMCTL::MatchSymbol(_, cases, def) => cases
                .values()
                .fold(def.count_slots(), |acc, code| acc.max(code.count_slots())),
            LEMCTL::Return(..) => SlotsCounter::default(),
            LEMCTL::Seq(ops, rest) => {
                let ops_slots = ops.iter().fold(SlotsCounter::default(), |acc, op| {
                    let val = match op {
                        LEMOP::Hash2(..) | LEMOP::Unhash2(..) => SlotsCounter::new((1, 0, 0)),
                        LEMOP::Hash3(..) | LEMOP::Unhash3(..) => SlotsCounter::new((0, 1, 0)),
                        LEMOP::Hash4(..) | LEMOP::Unhash4(..) => SlotsCounter::new((0, 0, 1)),
                        _ => SlotsCounter::default(),
                    };
                    acc.add(val)
                });
                ops_slots.add(rest.count_slots())
            }
        }
    }
}

/// Manages global allocations for constants in a constraint system
#[derive(Default)]
pub struct AllocationManager<F: LurkField>(HashMap<FWrap<F>, AllocatedNum<F>>);

impl<F: LurkField> AllocationManager<F> {
    /// Checks if the allocation for a numeric variable has already been cached.
    /// If so, return the cached allocation variable. Allocate, cache and return
    /// otherwise.
    pub(crate) fn get_or_alloc_num<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        f: F,
    ) -> Result<AllocatedNum<F>> {
        let wrap = FWrap(f);
        match self.0.get(&wrap) {
            Some(allocated_num) => Ok(allocated_num.to_owned()),
            None => {
                let digits = f.hex_digits();
                let allocated_num =
                    AllocatedNum::alloc(cs.namespace(|| format!("allocate {digits}")), || Ok(f))
                        .with_context(|| format!("couldn't allocate {digits}"))?;
                self.0.insert(wrap, allocated_num.clone());
                Ok(allocated_num)
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum SlotType {
    Hash2,
    Hash3,
    Hash4,
}

impl SlotType {
    pub(crate) fn preimg_size(&self) -> usize {
        match self {
            Self::Hash2 => 4,
            Self::Hash3 => 6,
            Self::Hash4 => 8,
        }
    }
}

impl std::fmt::Display for SlotType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Hash2 => write!(f, "Hash2"),
            Self::Hash3 => write!(f, "Hash3"),
            Self::Hash4 => write!(f, "Hash4"),
        }
    }
}

/// A `Slot` is characterized by an index and a type
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Slot {
    idx: usize,
    typ: SlotType,
}

impl std::fmt::Display for Slot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Slot({}, {})", self.idx, self.typ)
    }
}

impl LEM {
    fn allocate_ptr<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        z_ptr: &ZPtr<F>,
        name: &AString,
        allocated_ptrs: &HashMap<&AString, AllocatedPtr<F>>,
    ) -> Result<AllocatedPtr<F>> {
        if allocated_ptrs.contains_key(name) {
            bail!("{} already allocated", name);
        };
        let allocated_tag =
            AllocatedNum::alloc(cs.namespace(|| format!("allocate {name}'s tag")), || {
                Ok(z_ptr.tag.to_field())
            })
            .with_context(|| format!("couldn't allocate {name}'s tag"))?;
        let allocated_hash =
            AllocatedNum::alloc(cs.namespace(|| format!("allocate {name}'s hash")), || {
                Ok(z_ptr.hash)
            })
            .with_context(|| format!("couldn't allocate {name}'s hash"))?;
        Ok(AllocatedPtr::from_parts(&allocated_tag, &allocated_hash))
    }

    fn allocate_input<'a, F: LurkField, CS: ConstraintSystem<F>>(
        &'a self,
        cs: &mut CS,
        store: &mut Store<F>,
        frame: &Frame<F>,
        allocated_ptrs: &mut HashMap<&'a AString, AllocatedPtr<F>>,
    ) -> Result<()> {
        for (i, ptr) in frame.input.iter().enumerate() {
            let name = &self.input_vars[i];
            let allocated_ptr =
                Self::allocate_ptr(cs, &store.hash_ptr(ptr)?, name, allocated_ptrs)?;
            allocated_ptrs.insert(name, allocated_ptr);
        }
        Ok(())
    }

    fn allocate_output<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        store: &mut Store<F>,
        frame: &Frame<F>,
        allocated_ptrs: &HashMap<&AString, AllocatedPtr<F>>,
    ) -> Result<[AllocatedPtr<F>; 3]> {
        let mut allocated_output_ptrs = vec![];
        for (i, ptr) in frame.output.iter().enumerate() {
            let allocated_ptr = Self::allocate_ptr(
                cs,
                &store.hash_ptr(ptr)?,
                &format!("output[{}]", i).into(),
                allocated_ptrs,
            )?;
            allocated_output_ptrs.push(allocated_ptr)
        }
        Ok(allocated_output_ptrs.try_into().unwrap())
    }

    fn zptr_from_mptr<F: LurkField>(
        mptr: &MetaPtr,
        frame: &Frame<F>,
        store: &mut Store<F>,
    ) -> Result<ZPtr<F>> {
        match frame.binds.get(mptr) {
            Some(ptr) => store.hash_ptr(ptr),
            None => Ok(ZPtr::dummy()),
        }
    }

    fn alloc_preimg<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        preimg: &[MetaPtr],
        frame: &Frame<F>,
        store: &mut Store<F>,
        allocated_ptrs: &HashMap<&AString, AllocatedPtr<F>>,
    ) -> Result<Vec<AllocatedPtr<F>>> {
        preimg
            .iter()
            .map(|x| {
                Self::zptr_from_mptr(x, frame, store)
                    .and_then(|ref ptr| Self::allocate_ptr(cs, ptr, x.name(), allocated_ptrs))
            })
            .collect::<Result<Vec<_>>>()
    }

    fn get_allocated_preimg<'a, F: LurkField>(
        preimg: &[MetaPtr],
        allocated_ptrs: &'a HashMap<&AString, AllocatedPtr<F>>,
    ) -> Result<Vec<&'a AllocatedPtr<F>>> {
        preimg
            .iter()
            .map(|x| {
                allocated_ptrs
                    .get(x.name())
                    .ok_or_else(|| anyhow!("{x} not allocated"))
            })
            .collect::<Result<Vec<_>>>()
    }

    fn allocate_preimg_component_for_slot<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        slot: &Slot,
        component_idx: usize,
        value: F,
    ) -> Result<AllocatedNum<F>> {
        let namespace = &format!("component {component_idx} for slot {slot}");
        AllocatedNum::alloc(cs.namespace(|| namespace), || Ok(value))
            .with_context(|| format!("allocation for {namespace} failed"))
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

    fn allocate_slots<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        preimgs: &[Vec<Ptr<F>>],
        slot_type: SlotType,
        num_slots: usize,
        store: &mut Store<F>,
    ) -> Result<Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>> {
        let mut preallocations = vec![];

        for (slot_idx, preimg) in preimgs.iter().enumerate() {
            let slot = Slot {
                idx: slot_idx,
                typ: slot_type,
            };
            // We need to allocate the preimage and the image for the slots. We
            // start by the preimage because the image depends on it
            let mut preallocated_preimg = vec![];

            let mut component_idx = 0;
            for ptr in preimg.iter() {
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

            // Then we allocate the image by calling the arithmetic function
            // according to the slot type
            let preallocated_img =
                Self::allocate_img_for_slot(cs, &slot, preallocated_preimg.clone(), store)?;

            preallocations.push((preallocated_preimg, preallocated_img));
        }
        for slot_idx in preallocations.len()..num_slots {
            let slot = Slot {
                idx: slot_idx,
                typ: slot_type,
            };
            let mut preallocated_preimg = vec![];
            for component_idx in 0..slot_type.preimg_size() {
                preallocated_preimg.push(Self::allocate_preimg_component_for_slot(
                    cs,
                    &slot,
                    component_idx,
                    F::ZERO,
                )?);
            }
        }
        Ok(preallocations)
    }

    /// Create R1CS constraints for LEM given an evaluation frame. This function
    /// implements the STEP 3 mentioned above.
    ///
    /// We use a stack to keep track of the LEMOPs that need to be constrained
    /// and a hashmap to map meta pointers to their respective allocated pointers.
    ///
    /// Notably, one of the variables that we push to the stack is a
    /// `concrete_path: Boolean`, which encodes whether we are on a *concrete* or
    /// *virtual* path. A virtual path is one that wasn't taken during
    /// interpretation and thus its frame pointers weren't bound. A concrete path
    /// means that interpretation went down that road and the frame data should
    /// be complete for the variables and the slots on that path. For virtual
    /// paths we need to create dummy bindings for the meta pointers and relax the
    /// implications with false premises. The premise is precicely `concrete_path`.
    ///
    /// Regarding the slot optimizations, STEP 3 uses information gathered during
    /// STEPs 1 and 2. So at this point we know:
    ///
    /// 1. Which LEMOPs map to which slots;
    /// 2. The slots (and their respective preimages) that were visited during
    /// interpretation.
    ///
    /// So we proceed by first allocating preimages and images for each slot and
    /// then, as we traverse the LEMOP, we add constraints to make sure that the
    /// witness satisfies the arithmetic equations for the corresponding slots.
    pub fn synthesize<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        alloc_manager: &mut AllocationManager<F>,
        store: &mut Store<F>,
        frame: &Frame<F>,
        slots_count: &SlotsCounter,
    ) -> Result<()> {
        let mut allocated_ptrs: HashMap<&AString, AllocatedPtr<F>> = HashMap::default();

        self.allocate_input(cs, store, frame, &mut allocated_ptrs)?;
        let preallocated_outputs = Self::allocate_output(cs, store, frame, &allocated_ptrs)?;

        let preallocated_hash2_slots = Self::allocate_slots(
            cs,
            &frame.preimages.hash2,
            SlotType::Hash2,
            slots_count.hash2,
            store,
        )?;

        let preallocated_hash3_slots = Self::allocate_slots(
            cs,
            &frame.preimages.hash3,
            SlotType::Hash3,
            slots_count.hash3,
            store,
        )?;

        let preallocated_hash4_slots = Self::allocate_slots(
            cs,
            &frame.preimages.hash4,
            SlotType::Hash4,
            slots_count.hash4,
            store,
        )?;

        let get_preallocations_fn = |slot: Slot| match slot.typ {
            SlotType::Hash2 => &preallocated_hash2_slots[slot.idx],
            SlotType::Hash3 => &preallocated_hash3_slots[slot.idx],
            SlotType::Hash4 => &preallocated_hash4_slots[slot.idx],
        };

        let mut stack = vec![(&self.lem, Boolean::Constant(true), Path::default())];

        while let Some((code, concrete_path, path)) = stack.pop() {
            match code {
                LEMCTL::MatchTag(match_ptr, cases) => {
                    let Some(allocated_match_ptr) = allocated_ptrs.get(match_ptr.name()) else {
                        bail!("{match_ptr} not allocated");
                    };
                    let mut concrete_path_vec = Vec::new();
                    for (tag, op) in cases {
                        let allocated_has_match = alloc_equal_const(
                            &mut cs.namespace(|| format!("{path}.{tag}.alloc_equal_const")),
                            allocated_match_ptr.tag(),
                            tag.to_field::<F>(),
                        )
                        .with_context(|| "couldn't allocate equal const")?;
                        concrete_path_vec.push(allocated_has_match.clone());

                        let concrete_path_and_has_match = and(
                            &mut cs.namespace(|| format!("{path}.{tag}.and")),
                            &concrete_path,
                            &allocated_has_match,
                        )
                        .with_context(|| "failed to constrain `and`")?;

                        let new_path = path.push_tag(tag);
                        stack.push((op, concrete_path_and_has_match, new_path));
                    }

                    // Now we need to enforce that at least one path was taken. We do that by constraining
                    // that the sum of the previously collected `Boolean`s is one

                    enforce_selector_with_premise(
                        &mut cs.namespace(|| format!("{path}.enforce_selector_with_premise")),
                        &concrete_path,
                        &concrete_path_vec,
                    )
                    .with_context(|| " couldn't constrain `enforce_selector_with_premise`")?;
                }
                LEMCTL::Seq(ops, rest) => {
                    for op in ops {
                        macro_rules! constrain_slot {
                            ( $preimg: expr, $img: expr, $allocated_preimg: expr, $allocated_img: expr, $slot: expr ) => {
                                // Retrieve the preallocated preimage and image for this slot
                                let (preallocated_preimg, preallocated_img) =
                                    &get_preallocations_fn($slot);

                                // Add the implication constraint for the image
                                implies_equal(
                                    &mut cs.namespace(|| {
                                        format!("implies equal for {}'s hash (LEMOP {:?})", $img, &op)
                                    }),
                                    &concrete_path,
                                    $allocated_img.hash(),
                                    &preallocated_img,
                                )?;

                                // For each component of the preimage, add implication constraints
                                // for its tag and hash
                                for (i, allocated_ptr) in $allocated_preimg.iter().enumerate() {
                                    let name = $preimg[i].name();
                                    let ptr_idx = 2 * i;
                                    implies_equal(
                                        &mut cs.namespace(|| {
                                            format!("implies equal for {name}'s tag (LEMOP {:?}, pos {i})", &op)
                                        }),
                                        &concrete_path,
                                        allocated_ptr.tag(),
                                        &preallocated_preimg[ptr_idx], // tag index
                                    )?;
                                    implies_equal(
                                        &mut cs.namespace(|| {
                                            format!(
                                                "implies equal for {name}'s hash (LEMOP {:?}, pos {i})",
                                                &op
                                            )
                                        }),
                                        &concrete_path,
                                        allocated_ptr.hash(),
                                        &preallocated_preimg[ptr_idx + 1], // hash index
                                    )?;
                                }
                            };
                        }
                        macro_rules! hash_helper {
                            ( $img: expr, $tag: expr, $preimg: expr, $slot: expr ) => {
                                // Allocate image
                                let allocated_img = Self::allocate_ptr(
                                    cs,
                                    &Self::zptr_from_mptr($img, frame, store)?,
                                    $img.name(),
                                    &allocated_ptrs,
                                )?;

                                // Retrieve allocated preimage
                                let allocated_preimg =
                                    Self::get_allocated_preimg($preimg, &allocated_ptrs)?;

                                // Create constraint for the tag
                                let allocated_tag =
                                    alloc_manager.get_or_alloc_num(cs, $tag.to_field())?;
                                implies_equal(
                                    &mut cs
                                        .namespace(|| format!("implies equal for {}'s tag", $img)),
                                    &concrete_path,
                                    allocated_img.tag(),
                                    &allocated_tag,
                                )?;

                                // Add the hash constraints
                                constrain_slot!(
                                    $preimg,
                                    $img,
                                    allocated_preimg,
                                    allocated_img,
                                    $slot
                                );

                                // Insert allocated image into `allocated_ptrs`
                                allocated_ptrs.insert($img.name(), allocated_img.clone());
                            };
                        }
                        macro_rules! unhash_helper {
                            ( $preimg: expr, $img: expr, $slot: expr ) => {
                                // Retrieve allocated image
                                let Some(allocated_img) = allocated_ptrs.get($img.name()) else {
                                                                    bail!("{} not allocated", $img)
                                                                };

                                // Allocate preimage
                                let allocated_preimg =
                                    Self::alloc_preimg(cs, $preimg, frame, store, &allocated_ptrs)?;

                                // Add the hash constraints
                                constrain_slot!($preimg, $img, allocated_preimg, allocated_img, $slot);

                                // Insert allocated preimage into `allocated_ptrs`
                                for (mptr, allocated_ptr) in $preimg.iter().zip(allocated_preimg) {
                                    allocated_ptrs.insert(mptr.name(), allocated_ptr);
                                }
                            };
                        }

                        match op {
                            LEMOP::Hash2(img, tag, preimg) => {
                                hash_helper!(
                                    img,
                                    tag,
                                    preimg,
                                    Slot {
                                        idx: 0, // FIXME
                                        typ: SlotType::Hash2
                                    }
                                );
                            }
                            LEMOP::Hash3(img, tag, preimg) => {
                                hash_helper!(
                                    img,
                                    tag,
                                    preimg,
                                    Slot {
                                        idx: 0, // FIXME
                                        typ: SlotType::Hash3
                                    }
                                );
                            }
                            LEMOP::Hash4(img, tag, preimg) => {
                                hash_helper!(
                                    img,
                                    tag,
                                    preimg,
                                    Slot {
                                        idx: 0, // FIXME
                                        typ: SlotType::Hash4
                                    }
                                );
                            }
                            LEMOP::Unhash2(preimg, img) => {
                                unhash_helper!(
                                    preimg,
                                    img,
                                    Slot {
                                        idx: 0, // FIXME
                                        typ: SlotType::Hash2
                                    }
                                );
                            }
                            LEMOP::Unhash3(preimg, img) => {
                                unhash_helper!(
                                    preimg,
                                    img,
                                    Slot {
                                        idx: 0, // FIXME
                                        typ: SlotType::Hash3
                                    }
                                );
                            }
                            LEMOP::Unhash4(preimg, img) => {
                                unhash_helper!(
                                    preimg,
                                    img,
                                    Slot {
                                        idx: 0, // FIXME
                                        typ: SlotType::Hash4
                                    }
                                );
                            }
                            LEMOP::Null(tgt, tag) => {
                                let allocated_tgt = Self::allocate_ptr(
                                    cs,
                                    &Self::zptr_from_mptr(tgt, frame, store)?,
                                    tgt.name(),
                                    &allocated_ptrs,
                                )?;
                                allocated_ptrs.insert(tgt.name(), allocated_tgt.clone());
                                let allocated_tag =
                                    alloc_manager.get_or_alloc_num(cs, tag.to_field())?;

                                // Constrain tag
                                implies_equal(
                                    &mut cs.namespace(|| format!("implies equal for {tgt}'s tag")),
                                    &concrete_path,
                                    allocated_tgt.tag(),
                                    &allocated_tag,
                                )
                                .with_context(|| {
                                    format!("couldn't enforce implies equal for {tgt}'s tag")
                                })?;

                                // Constrain hash
                                implies_equal_zero(
                                    &mut cs.namespace(|| {
                                        format!("implies equal zero for {tgt}'s hash")
                                    }),
                                    &concrete_path,
                                    allocated_tgt.hash(),
                                )
                                .with_context(|| {
                                    format!("couldn't enforce implies equal zero for {tgt}'s hash")
                                })?;
                            }
                            _ => todo!(),
                        }
                    }
                    stack.push((rest, concrete_path, path));
                }
                LEMCTL::Return(outputs) => {
                    for (i, output) in outputs.iter().enumerate() {
                        let Some(allocated_ptr) = allocated_ptrs.get(output.name()) else {
                            bail!("{output} not allocated")
                        };

                        allocated_ptr
                            .implies_ptr_equal(
                                &mut cs.namespace(|| {
                                    format!("{path}.implies_ptr_equal {output} (output {i})")
                                }),
                                &concrete_path,
                                &preallocated_outputs[i],
                            )
                            .with_context(|| "couldn't constrain `implies_ptr_equal`")?;
                    }
                }
                _ => todo!(),
            }
        }
        Ok(())
    }

    /// Computes the number of constraints that `synthesize` should create. It's
    /// also an explicit way to document and attest how the number of constraints
    /// grow.
    pub fn num_constraints(&self, slots_count: &SlotsCounter) -> usize {
        // fixed cost for each slot
        let mut num_constraints =
            289 * slots_count.hash2 + 337 * slots_count.hash3 + 388 * slots_count.hash4;

        let mut stack = vec![(&self.lem, false)];
        while let Some((code, nested)) = stack.pop() {
            match code {
                LEMCTL::Return(..) => {
                    // tag and hash for 3 pointers
                    num_constraints += 6;
                }
                LEMCTL::MatchTag(_, cases) => {
                    // `alloc_equal_const` adds 3 constraints for each case and
                    // the `and` is free for non-nested `MatchTag`s, since we
                    // start `concrete_path` with a constant `true`
                    let multiplier = if nested { 4 } else { 3 };

                    // then we add 1 constraint from `enforce_selector_with_premise`
                    num_constraints += multiplier * cases.len() + 1;

                    // stacked ops are now nested
                    for code in cases.values() {
                        stack.push((code, true));
                    }
                }
                LEMCTL::MatchSymbol(..) => todo!(),
                LEMCTL::Seq(ops, rest) => {
                    for op in ops {
                        match op {
                            LEMOP::Null(..) => {
                                // constrain tag and hash
                                num_constraints += 2;
                            }
                            LEMOP::Hash2(..) => {
                                // tag and hash for 3 pointers: 1 image + 2 from preimage
                                num_constraints += 6;
                            }
                            LEMOP::Hash3(..) => {
                                // tag and hash for 4 pointers: 1 image + 3 from preimage
                                num_constraints += 8;
                            }
                            LEMOP::Hash4(..) => {
                                // tag and hash for 5 pointers: 1 image + 4 from preimage
                                num_constraints += 10;
                            }
                            LEMOP::Unhash2(..) => {
                                // one constraint for the image's hash
                                // tag and hash for 2 pointers from preimage
                                num_constraints += 5;
                            }
                            LEMOP::Unhash3(..) => {
                                // one constraint for the image's hash
                                // tag and hash for 3 pointers from preimage
                                num_constraints += 7;
                            }
                            LEMOP::Unhash4(..) => {
                                // one constraint for the image's hash
                                // tag and hash for 4 pointers from preimage
                                num_constraints += 9;
                            }
                            _ => todo!(),
                        }
                    }
                    // no constraints added here
                    stack.push((rest, nested))
                }
            }
        }

        num_constraints
    }
}
