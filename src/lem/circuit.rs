//! # Constraint system for LEM
//!
//! Here we describe how we generate bellperson constraints for LEM, such that
//! it can be used with Nova folding to implement the Lurk evaluation.
//!
//! ## Pattern matching and the implication system:
//!
//! LEM implements branching using, for example, `MatchTag` and `MatchSymbol`.
//! By nesting `MatchTag`s and `MatchSymbol`s we create a set of paths that
//! interpretation can follow. We call them **virtual** and **concrete** paths.
//! In particular, the followed path is the concrete one. We use a Boolean
//! variable to indicate whether a path is concrete or not. This allows us to
//! construct an **implication system**, which is responsible for ensuring that
//! allocated variables in the concrete path are equal to their expected values
//! but such equalities on virtual paths are irrelevant.
//!
//! ## Slot optimization:
//!
//! Some operations like Poseidon hash can be relatively expensive in the circuit,
//! therefore we want to avoid wasting constraints with them as much as possible.
//! In order to achieve this goal, we only add constraints to a limited number of
//! *slots* that correspond to a maximum number of such expensive operations that
//! may occurr in a single interpretation round. This optimization avoids
//! constraining every expensive operation on every possible path.
//!
//! Shortly, we construct the hash slot system using the next steps:
//!
//! * STEP 1: Static analysis, when we traverse LEM for the first time and allocate
//! slots for hashes in all virtual paths. We only add hashes that where not yet
//! previously added, therefore ensuring deduplication of hashes in different
//! branches.
//!
//! * STEP 2: During interpretation (second traversal) we gather information
//! related to each visited slot.
//!
//! * STEP 3: During construction of constraints, we first preallocate the preimage
//! and image for each slot; then we synthesize all slots; and finally we traverse
//! LEM (for the third time), adding implication constraints, glueing together all the
//! information. This step is better explained in the `synthesize` function.

use std::collections::{HashMap, HashSet};

use anyhow::{anyhow, bail, Context, Result};
use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    ConstraintSystem,
};
use indexmap::{IndexMap, IndexSet};

use crate::circuit::gadgets::{
    constraints::{
        alloc_equal_const, and, enforce_selector_with_premise, implies_equal, implies_equal_zero,
    },
    data::hash_poseidon,
    pointer::AllocatedPtr,
};

use crate::field::{FWrap, LurkField};

use super::{
    interpreter::{Frame, SlotType},
    path::Path,
    pointers::ZPtr,
    store::Store,
    MetaPtr, LEMCTL, LEMOP,
};

/// Holds a counter per path
#[derive(Default)]
struct PathTicker(HashMap<Path, usize>);

impl PathTicker {
    /// Increments the counter of a path. If the path wasn't tracked, returns
    /// `0` and starts tracking it
    pub(crate) fn tick(&mut self, path: Path) -> usize {
        let next = self.0.get(&path).unwrap_or(&0).to_owned();
        self.0.insert(path, next + 1);
        next
    }

    /// Starts tracking a new path with a counter from another. If the reference
    /// path wasn't being tracked, the new one won't be either, such that calling
    /// `next` will return `0`.
    pub(crate) fn cont(&mut self, new: Path, from: &Path) {
        match self.0.get(from) {
            Some(i) => {
                self.0.insert(new, *i);
            }
            None => (),
        }
    }
}

/// Keeps track of previously used slots indices for each possible LEM path,
/// being capable of informing the next slot index to be used
#[derive(Default)]
struct SlotsCounter {
    hash2: PathTicker,
    hash3: PathTicker,
    hash4: PathTicker,
}

impl SlotsCounter {
    #[inline]
    pub(crate) fn next_hash2(&mut self, path: Path) -> usize {
        self.hash2.tick(path)
    }

    #[inline]
    pub(crate) fn next_hash3(&mut self, path: Path) -> usize {
        self.hash3.tick(path)
    }

    #[inline]
    pub(crate) fn next_hash4(&mut self, path: Path) -> usize {
        self.hash4.tick(path)
    }

    pub(crate) fn cont(&mut self, new: Path, from: &Path) {
        self.hash2.cont(new.clone(), from);
        self.hash3.cont(new.clone(), from);
        self.hash4.cont(new, from);
    }
}

/// Contains a `slots_map` that maps `LEMOP`s to their slots. This map is not
/// expected to be injective, as two or more `LEMOP`s can be mapped to the same
/// slot.
///
/// The `slots` attribute is derived from `slots_map` by iterating on its values.
#[derive(Clone, Eq, PartialEq, Default)]
pub struct SlotsInfo {
    slots_map: IndexMap<LEMOP, (usize, SlotType)>,
    slots: IndexSet<(usize, SlotType)>,
}

impl SlotsInfo {
    #[inline]
    pub fn get_slot(&self, op: &LEMOP) -> Result<&(usize, SlotType)> {
        self.slots_map
            .get(op)
            .ok_or_else(|| anyhow!("Slot not found for LEMOP {:?}", op))
    }
}

#[derive(Clone, Eq, PartialEq, Default)]
struct ImgMap<'a>{
    // these hashmaps keep track of slots that were allocated for images
    img2: HashMap<&'a MetaPtr, (usize, SlotType)>,
    img3: HashMap<&'a MetaPtr, (usize, SlotType)>,
    img4: HashMap<&'a MetaPtr, (usize, SlotType)>,
    // these hashmaps keep track of slots that were allocated for preimages
    pre2: HashMap<&'a [MetaPtr; 2], (usize, SlotType)>,
    pre3: HashMap<&'a [MetaPtr; 3], (usize, SlotType)>,
    pre4: HashMap<&'a [MetaPtr; 4], (usize, SlotType)>,
}

impl LEMCTL {
    /// STEP 1: compute the slot mapping on a first (and unique) traversal
    ///
    /// While traversing parallel paths, we need to reuse compatible slots. For
    /// example, on a `MatchTag` with two arms, such that each arm is a `Hash2`,
    /// we want those hashes to occupy the same slot. We do this by using a
    /// `SlotsCounter`, which can return the next index for a slot category
    /// (`Hash2`, `Hash3` etc).
    ///
    /// Further, when we:
    /// * Construct the same pointer twice
    /// * Destruct the same pointer twice
    /// * Construct a pointer that was previously destructed
    /// * Destruct a pointer that was previously constructed
    ///
    /// We want to reuse the same slot as before. To accomplish this, we use
    /// hashmaps that can recover the slots that were previously allocated.
    pub fn slots_info(&self) -> Result<SlotsInfo> {
        let mut slots_info = SlotsInfo::default();
        let mut img_map = ImgMap::default();
        let mut slots_counter = SlotsCounter::default();

        fn populate_with_op<'a>(
            op: &'a LEMOP, path: Path, img_map: &mut ImgMap<'a>, slots_counter: &mut SlotsCounter, slots_info: &mut SlotsInfo
        ) -> Result<()> {
            /// Designates a slot for a pair of preimage/image. If a slot has
            /// already been allocated for either the preimage or the image,
            /// reuses it. Otherwise, allocates a new one.
            macro_rules! populate_slots_map {
                ( $preimg: expr, $img: expr, $preimgs_map: expr, $imgs_map: expr, $counter_fn: expr ) => {
                    match ($preimgs_map.get($preimg), $imgs_map.get($img)) {
                        (Some(slot), _) | (_, Some(slot)) => {
                            // reusing a slot
                            if slots_info.slots_map.insert(op.clone(), *slot).is_some() {
                                bail!("Duplicated LEMOP: {:?}", op)
                            }
                        }
                        (None, None) => {
                            // allocating a new slot
                            let slot_idx = $counter_fn(path);
                            let slot_type = SlotType::from_lemop(op);
                            let slot = (slot_idx, slot_type);
                            if slots_info.slots_map.insert(op.clone(), slot).is_some() {
                                bail!("Duplicated LEMOP: {:?}", op)
                            }
                            slots_info.slots.insert(slot);

                            // memoize
                            $preimgs_map.insert($preimg, slot);
                            $imgs_map.insert($img, slot);
                        }
                    };
                };
            }
            match op {
                LEMOP::Hash2(img, _, preimg) | LEMOP::Unhash2(preimg, img) => {
                    populate_slots_map!(preimg, img, img_map.pre2, img_map.img2, |path| {
                        slots_counter.next_hash2(path)
                    });
                    Ok(())
                }
                LEMOP::Hash3(img, _, preimg) | LEMOP::Unhash3(preimg, img) => {
                    populate_slots_map!(preimg, img, img_map.pre3, img_map.img3, |path| {
                        slots_counter.next_hash3(path)
                    });
                    Ok(())
                }
                LEMOP::Hash4(img, _, preimg) | LEMOP::Unhash4(preimg, img) => {
                    populate_slots_map!(preimg, img, img_map.pre4, img_map.img4, |path| {
                        slots_counter.next_hash4(path)
                    });
                    Ok(())
                }
                _ => Ok(())
            }
        }
        fn recurse<'a>(
            code: &'a LEMCTL, path: Path, img_map: &mut ImgMap<'a>, slots_counter: &mut SlotsCounter, slots_info: &mut SlotsInfo
        ) -> Result<()> {
            match code {
                LEMCTL::MatchTag(_, cases) => {
                    for (tag, code) in cases {
                        let new_path = path.push_tag(tag);
                        slots_counter.cont(new_path.clone(), &path);
                        recurse(code, new_path, img_map, slots_counter, slots_info)?;
                    }
                    Ok(())
                }
                LEMCTL::MatchSymbol(_, cases, def) => {
                    for (symbol, code) in cases {
                        let new_path = path.push_symbol(symbol);
                        slots_counter.cont(new_path.clone(), &path);
                        recurse(code, new_path, img_map, slots_counter, slots_info)?;
                    }
                    let new_path = path.push_default();
                    slots_counter.cont(new_path.clone(), &path);
                    recurse(def, new_path, img_map, slots_counter, slots_info)
                }
                LEMCTL::Seq(op, rest) => {
                    populate_with_op(op, path.clone(), img_map, slots_counter, slots_info)?;
                    recurse(rest, path, img_map, slots_counter, slots_info)
                },
                LEMCTL::Return(..) => Ok(()),
            }
        }
        recurse(&self, Path::default(), &mut img_map, &mut slots_counter, &mut slots_info)?;
        Ok(slots_info)
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

impl SlotType {
    pub(crate) fn from_lemop(op: &LEMOP) -> Self {
        match op {
            LEMOP::Hash2(..) | LEMOP::Unhash2(..) => SlotType::Hash2,
            LEMOP::Hash3(..) | LEMOP::Unhash3(..) => SlotType::Hash3,
            LEMOP::Hash4(..) | LEMOP::Unhash4(..) => SlotType::Hash4,
            _ => panic!("Invalid LEMOP"),
        }
    }
}

/*
impl LEM {
    fn allocate_ptr<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        z_ptr: &ZPtr<F>,
        name: &String,
        allocated_ptrs: &HashMap<&String, AllocatedPtr<F>>,
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
        allocated_ptrs: &mut HashMap<&'a String, AllocatedPtr<F>>,
    ) -> Result<()> {
        for (i, ptr) in frame.input.iter().enumerate() {
            let name = &self.input[i];
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
        allocated_ptrs: &HashMap<&String, AllocatedPtr<F>>,
    ) -> Result<[AllocatedPtr<F>; 3]> {
        let mut allocated_output_ptrs = vec![];
        for (i, ptr) in frame.output.iter().enumerate() {
            let allocated_ptr = Self::allocate_ptr(
                cs,
                &store.hash_ptr(ptr)?,
                &format!("output[{}]", i),
                allocated_ptrs,
            )?;
            allocated_output_ptrs.push(allocated_ptr)
        }
        Ok(allocated_output_ptrs.try_into().unwrap())
    }

    fn on_concrete_path(concrete_path: &Boolean) -> Result<bool> {
        concrete_path
            .get_value()
            .ok_or_else(|| anyhow!("Couldn't check whether we're on a concrete path"))
    }

    fn z_ptr_from_frame<F: LurkField>(
        concrete_path: &Boolean,
        frame: &Frame<F>,
        mptr: &MetaPtr,
        store: &mut Store<F>,
    ) -> Result<ZPtr<F>> {
        if Self::on_concrete_path(concrete_path)? {
            store.hash_ptr(mptr.get_ptr(&frame.binds)?)
        } else {
            Ok(ZPtr::dummy())
        }
    }

    fn alloc_preimg<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        preimg: &[MetaPtr],
        concrete_path: &Boolean,
        frame: &Frame<F>,
        store: &mut Store<F>,
        allocated_ptrs: &HashMap<&String, AllocatedPtr<F>>,
    ) -> Result<Vec<AllocatedPtr<F>>> {
        preimg
            .iter()
            .map(|x| {
                Self::z_ptr_from_frame(concrete_path, frame, x, store)
                    .and_then(|ref ptr| Self::allocate_ptr(cs, ptr, x.name(), allocated_ptrs))
            })
            .collect::<Result<Vec<_>>>()
    }

    fn get_allocated_preimg<'a, F: LurkField>(
        preimg: &[MetaPtr],
        allocated_ptrs: &'a HashMap<&String, AllocatedPtr<F>>,
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

    fn allocate_preimg_for_slot<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        frame: &Frame<F>,
        slot: &(usize, SlotType),
        store: &mut Store<F>,
    ) -> Result<Vec<AllocatedNum<F>>> {
        // TODO: avoid this destruction and implement proper display for slot blueprints
        let (slot_idx, slot_type) = slot;

        let mut preallocated_preimg = vec![];

        // We need to know whether we have data for that slot, which might have
        // been collected during interpretation.
        match frame.visits.get(slot) {
            None => {
                // No data was collected for this slot. We can allocate zeros
                for i in 0..slot_type.preimg_size() {
                    let allocated_zero = AllocatedNum::alloc(
                        cs.namespace(|| {
                            format!("preimage {i} for slot {slot_idx} (type {slot_type})")
                        }),
                        || Ok(F::ZERO),
                    )
                    .with_context(|| {
                        format!("preimage {i} for slot {slot_idx} (type {slot_type}) failed")
                    })?;

                    preallocated_preimg.push(allocated_zero);
                }
            }
            Some(ptrs) => {
                // In this case, interpretation visited the slot. We need to
                // allocate the tag and hash for each pointer in the preimage
                for (j, ptr) in ptrs.iter().enumerate() {
                    let z_ptr = store.hash_ptr(ptr)?;

                    // `i = 2 * j` to mimic the namespaces from the `None` case
                    let i = 2 * j;

                    // allocate tag
                    let allocated_tag = AllocatedNum::alloc(
                        cs.namespace(|| {
                            format!("preimage {i} for slot {slot_idx} (type {slot_type})")
                        }),
                        || Ok(z_ptr.tag.to_field()),
                    )
                    .with_context(|| {
                        format!("preimage {i} for slot {slot_idx} (type {slot_type}) failed")
                    })?;

                    preallocated_preimg.push(allocated_tag);

                    // now we refer to the hash of the pointer
                    let i = i + 1;

                    // allocate hash
                    let allocated_hash = AllocatedNum::alloc(
                        cs.namespace(|| {
                            format!("preimage {i} for slot {slot_idx} (type {slot_type})")
                        }),
                        || Ok(z_ptr.hash),
                    )
                    .with_context(|| {
                        format!("preimage {i} for slot {slot_idx} (type {slot_type}) failed")
                    })?;

                    preallocated_preimg.push(allocated_hash);
                }
            }
        }
        Ok(preallocated_preimg)
    }

    fn allocate_img_for_slot<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        slot: &(usize, SlotType),
        preallocated_preimg: Vec<AllocatedNum<F>>,
        store: &mut Store<F>,
    ) -> Result<AllocatedNum<F>> {
        // TODO: avoid this destruction and implement proper display for slot blueprints
        let (slot_idx, slot_type) = slot;

        let cs = &mut cs.namespace(|| format!("poseidon for slot {slot_idx} (type {slot_type})"));
        let preallocated_img = {
            match slot_type {
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

    /// Create R1CS constraints for LEM given an evaluation frame.
    ///
    /// As we find recursive (non-leaf) LEM operations, we stack them to be
    /// constrained later, using hash maps to manage viariables and pointers in
    /// a way we can reference allocated variables that were previously created.
    ///
    /// Notably, we use a variable `concrete_path: Boolean` to encode whether we
    /// are on a *concrete* or *virtual* path. A virtual path is one that wasn't
    /// taken during evaluation and thus its frame pointers weren't bound. A
    /// concrete path means that evaluation took that path and the frame data
    /// should be complete. For virtual paths we need to create dummy bindings
    /// and relax the implications with false premises. The premise is precicely
    /// `concrete_path`.
    ///
    /// Regarding the slot optimizations, STEP 3 uses information gathered during
    /// STEPs 1 and 2. So at this point we know:
    ///
    /// 1. Which LEMOPs map to which slots. Since LEMOPs can be deduplicated, it
    /// is possible a LEMOP has no slot at all;
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
        slots_info: &SlotsInfo,
    ) -> Result<()> {
        let mut allocated_ptrs: HashMap<&String, AllocatedPtr<F>> = HashMap::default();

        self.allocate_input(cs, store, frame, &mut allocated_ptrs)?;
        let preallocated_outputs = Self::allocate_output(cs, store, frame, &allocated_ptrs)?;

        // We need to populate this hashmap with preimages and images for each slot
        let mut preallocations: HashMap<
            (usize, SlotType),
            (Vec<AllocatedNum<F>>, AllocatedNum<F>),
        > = HashMap::default();

        // This loop is guaranteed to always visit slots in a fixed order for a
        // particular LEM because it iterates on an `IndexSet`, which preserves
        // the order in which data was added to it. That is the order in which
        // `LEMOP::slots_info` traverses the LEMOP.
        for slot in &slots_info.slots {
            // We need to allocate the preimage and the image for the slots. We
            // start by the preimage because the image depends on it
            let preallocated_preimg = Self::allocate_preimg_for_slot(cs, frame, slot, store)?;

            // Then we allocate the image by calling the arithmetic function
            // according to the slot type
            let preallocated_img =
                Self::allocate_img_for_slot(cs, slot, preallocated_preimg.clone(), store)?;

            preallocations.insert(*slot, (preallocated_preimg, preallocated_img));
        }

        let mut stack = vec![(&self.lem_op, Boolean::Constant(true), Path::default())];

        while let Some((op, concrete_path, path)) = stack.pop() {
            macro_rules! constrain_slot {
                ( $preimg: expr, $img: expr, $allocated_preimg: expr, $allocated_img: expr) => {
                    // Retrieve the preallocated preimage and image for this slot
                    let slot = slots_info.get_slot(op)?;
                    let (preallocated_preimg, preallocated_img) = preallocations.get(slot).unwrap();

                    // Add the implication constraint for the image
                    implies_equal(
                        &mut cs.namespace(|| {
                            format!("implies equal for {}'s hash (LEMOP {:?})", $img, &op)
                        }),
                        &concrete_path,
                        $allocated_img.hash(),
                        preallocated_img,
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
                ( $img: expr, $tag: expr, $preimg: expr ) => {
                    // Allocate image
                    let allocated_img = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_frame(&concrete_path, frame, $img, store)?,
                        $img.name(),
                        &allocated_ptrs,
                    )?;

                    // Retrieve allocated preimage
                    let allocated_preimg = Self::get_allocated_preimg($preimg, &allocated_ptrs)?;

                    // Create constraint for the tag
                    let allocated_tag = alloc_manager.get_or_alloc_num(cs, $tag.to_field())?;
                    implies_equal(
                        &mut cs.namespace(|| format!("implies equal for {}'s tag", $img)),
                        &concrete_path,
                        allocated_img.tag(),
                        &allocated_tag,
                    )?;

                    // Add the hash constraints
                    constrain_slot!($preimg, $img, allocated_preimg, allocated_img);

                    // Insert allocated image into `allocated_ptrs`
                    allocated_ptrs.insert($img.name(), allocated_img.clone());
                };
            }
            macro_rules! unhash_helper {
                ( $preimg: expr, $img: expr ) => {
                    // Retrieve allocated image
                    let Some(allocated_img) = allocated_ptrs.get($img.name()) else {
                                                                bail!("{} not allocated", $img)
                                                            };

                    // Allocate preimage
                    let allocated_preimg = Self::alloc_preimg(
                        cs,
                        $preimg,
                        &concrete_path,
                        frame,
                        store,
                        &allocated_ptrs,
                    )?;

                    // Add the hash constraints
                    constrain_slot!($preimg, $img, allocated_preimg, allocated_img);

                    // Insert allocated preimage into `allocated_ptrs`
                    for (mptr, allocated_ptr) in $preimg.iter().zip(allocated_preimg) {
                        allocated_ptrs.insert(mptr.name(), allocated_ptr);
                    }
                };
            }

            match op {
                LEMOP::Hash2(img, tag, preimg) => {
                    hash_helper!(img, tag, preimg);
                }
                LEMOP::Hash3(img, tag, preimg) => {
                    hash_helper!(img, tag, preimg);
                }
                LEMOP::Hash4(img, tag, preimg) => {
                    hash_helper!(img, tag, preimg);
                }
                LEMOP::Unhash2(preimg, img) => {
                    unhash_helper!(preimg, img);
                }
                LEMOP::Unhash3(preimg, img) => {
                    unhash_helper!(preimg, img);
                }
                LEMOP::Unhash4(preimg, img) => {
                    unhash_helper!(preimg, img);
                }
                LEMOP::Null(tgt, tag) => {
                    let allocated_tgt = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_frame(&concrete_path, frame, tgt, store)?,
                        tgt.name(),
                        &allocated_ptrs,
                    )?;
                    allocated_ptrs.insert(tgt.name(), allocated_tgt.clone());
                    let allocated_tag = alloc_manager.get_or_alloc_num(cs, tag.to_field())?;

                    // Constrain tag
                    implies_equal(
                        &mut cs.namespace(|| format!("implies equal for {tgt}'s tag")),
                        &concrete_path,
                        allocated_tgt.tag(),
                        &allocated_tag,
                    )
                    .with_context(|| format!("couldn't enforce implies equal for {tgt}'s tag"))?;

                    // Constrain hash
                    implies_equal_zero(
                        &mut cs.namespace(|| format!("implies equal zero for {tgt}'s hash")),
                        &concrete_path,
                        allocated_tgt.hash(),
                    )
                    .with_context(|| {
                        format!("couldn't enforce implies equal zero for {tgt}'s hash")
                    })?;
                }
                LEMOP::MatchTag(match_ptr, cases) => {
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
                LEMOP::Seq(ops) => {
                    stack.extend(
                        ops.iter()
                            .rev()
                            .map(|op| (op, concrete_path.clone(), path.clone())),
                    );
                }
                LEMOP::Return(outputs) => {
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
    pub fn num_constraints(&self, slots_info: &SlotsInfo) -> usize {
        let mut num_constraints = 0;

        // fixed cost for each slot
        for (_, slot_type) in &slots_info.slots {
            match slot_type {
                SlotType::Hash2 => {
                    num_constraints += 289;
                }
                SlotType::Hash3 => {
                    num_constraints += 337;
                }
                SlotType::Hash4 => {
                    num_constraints += 388;
                }
            }
        }

        let mut stack = vec![(&self.lem_op, false)];
        while let Some((op, nested)) = stack.pop() {
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
                LEMOP::Return(..) => {
                    // tag and hash for 3 pointers
                    num_constraints += 6;
                }
                LEMOP::MatchTag(_, cases) => {
                    // `alloc_equal_const` adds 3 constraints for each case and
                    // the `and` is free for non-nested `MatchTag`s, since we
                    // start `concrete_path` with a constant `true`
                    let multiplier = if nested { 4 } else { 3 };

                    // then we add 1 constraint from `enforce_selector_with_premise`
                    num_constraints += multiplier * cases.len() + 1;

                    // stacked ops are now nested
                    for op in cases.values() {
                        stack.push((op, true));
                    }
                }
                LEMOP::Seq(ops) => {
                    // no constraints added here
                    stack.extend(ops.iter().map(|op| (op, nested)));
                }
                _ => todo!(),
            }
        }

        num_constraints
    }
}

/// Structure used to hold the number of slots we want for a `LEMOP`. It's mostly
/// for testing purposes.
#[derive(Debug, Default, PartialEq)]
pub(crate) struct NumSlots {
    pub(crate) hash2: usize,
    pub(crate) hash3: usize,
    pub(crate) hash4: usize,
}

impl NumSlots {
    #[inline]
    pub(crate) fn new(num_slots: (usize, usize, usize)) -> NumSlots {
        NumSlots {
            hash2: num_slots.0,
            hash3: num_slots.1,
            hash4: num_slots.2,
        }
    }
}

/// Computes the number of slots used for each category
#[allow(dead_code)]
pub(crate) fn num_slots(slots_info: &SlotsInfo) -> NumSlots {
    let mut slots2: HashSet<usize> = HashSet::default();
    let mut slots3: HashSet<usize> = HashSet::default();
    let mut slots4: HashSet<usize> = HashSet::default();

    for (slot_idx, slot_type) in &slots_info.slots {
        match slot_type {
            SlotType::Hash2 => {
                slots2.insert(*slot_idx);
            }
            SlotType::Hash3 => {
                slots3.insert(*slot_idx);
            }
            SlotType::Hash4 => {
                slots4.insert(*slot_idx);
            }
        }
    }
    NumSlots::new((slots2.len(), slots3.len(), slots4.len()))
}
*/
