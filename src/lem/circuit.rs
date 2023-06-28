//! ## Constraint system for LEM
//!
//! This module implements the generation of bellperson constraints for LEM, such
//! that it can be used with Nova folding to prove evaluations of Lurk expressions.
//!
//! ### "Concrete" and "virtual" paths
//!
//! LEMs can implement logical branches with the use of some special `LEMCTL`
//! nodes (such as `MatchTag`). But interpretation can only follow one path per
//! iteration, which we call the *concrete path*. The other paths are called
//! *virtual paths*. So we need a mechanism to safely "relax" the constraints
//! for the virtual paths while also properly enforcing the correctness for what
//! happens on the concrete path.
//!
//! We do that by using implication gadgets. An implication of the form `A → B`
//! is trivially true if `A` is false. But if `A` is true, then the implication
//! is true iff `B` is true. In other words, `B` is irrelevant if `A` is false,
//! which is the behavior we want for the virtual paths.
//!
//! With that in mind, we can keep track of booleans that tell us whether we're
//! on a concrete or a virtual path and use such booleans as the premises to build
//! the constraints we care about with implication gadgets.
//!
//! ### Slot optimizations
//!
//! Some LEMs may require expensive gadgets, such as Poseidon hashing. So we use
//! the concept of "slots" to avoid wasting constraints. To explore this idea,
//! let's use the following LEM as an example:
//!
//! ```text
//! a b c {
//!     match_tag c {
//!         Num => {
//!             let x: Cons = hash2(a, b);
//!             return (x, x, x);
//!         },
//!         Char => {
//!             let m: Cons = hash2(b, a);
//!             let n: Cons = hash2(c, a);
//!             return (m, m, n);
//!         }
//!     }
//! }
//! ```
//!
//! On a first impression, one might think that we need to perform three hashing
//! operations in the circuit when in fact we can get away with only two. That
//! is so because interpretation can only follow one of the paths:
//!
//! * If it goes through `Num`, we need to get one hash right
//! * If it goes through `Char`, we need to get two hashes right
//!
//! Either way, that's at most two hashes that we really care about. So we say
//! that we need to allocate two slots. The first slot is for the the hash of `x`
//! or `m` and the second slot is for the hash of `n` (or a "dummy value", as
//! explained ahead). Let's see a sketch of part of the circuit:
//!
//! ```text
//!     ┌─────┐        ┌─────┐
//! s0i0┤slot0├s0  s1i0┤slot1├s1
//! s0i1┤hash2│    s1i1┤hash2│
//!     └─────┘        └─────┘
//! ...
//! PNum = c.tag == Num
//! PChar = c.tag == Char
//!
//! PNum → a == s0i0
//! PNum → b == s0i1
//! PNum → x.hash == s0
//!
//! PChar → b == s0i0
//! PChar → a == s0i1
//! PChar → m.hash == s0
//!
//! PChar → c == s1i0
//! PChar → a == s1i1
//! PChar → n.hash == s1
//! ```
//!
//! `PNum` and `PChar` are boolean premises that indicate whether interpretation
//! went through `Num` or `Char` respectively. They're used as inputs for gadgets
//! that implement implications (hence the right arrows above). We will talk
//! about "concrete" vs "virtual" paths elsewhere.
//!
//! Now we're able to feed the slots with the data that comes from interpretation:
//!
//! 1. If it goes through `Num`, we will collect `[[a, b]]` for the preimages of
//! the slots. So we can feed the preimage of `slot0` with `[a, b]` and the
//! preimage of `slot1` with dummies
//!
//! 2. If it goes through `Char`, we will collect `[[b, a], [c, a]]` for the
//! preimages of the slots. So we can feed the preimage of `slot0` with `[b, a]`
//! and the preimage of `slot1` with `[c, a]`.
//!
//! In the first case, `PNum` will be true, requiring that the conclusions of the
//! implications for which it is the premise must also be true (which is fine!).
//! `PChar`, on the other hand, will be false, making the conclusions of the
//! implications for which it is the premise irrelevant. This is crucial because
//! interpretation won't even produce bindings for `m` or `n`, thus we don't
//! expect to fulfill `m.hash == s0` nor `n.hash == s1`. In fact, we don't expect
//! to fulfill any conclusion in the implications deriving from the `PChar` premise.
//!
//! Finally, we have an analogous situation for the second case, when
//! interpretation goes through `Char`.
//!
//! This example explored slots of type "hash2", but the same line of thought can
//! be expanded to different types of slots, orthogonally.
//!
//! #### The slot optimization algorithm
//!
//! We've separated the process in three steps:
//!
//! 1. Perform a static analysis to compute the number of slots (for each slot
//! type) that are needed. This piece of information will live on a `SlotsCounter`
//! structure, which is populated by the function `LEMCTL::count_slots`;
//!
//! 2. Interpret the LEM and collect the data that will be fed to some (or all)
//! slots, along with all bindings from `MetaPtr`s to `Ptr`s. This piece of
//! information will live on a `Frame` structure;
//!
//! 3. Build the circuit with `SlotsCounter` and `Frame` at hand. This step is
//! better explained in the `LEM::synthesize` function.
//!
//! The 3 steps above will be further referred to as *STEP 1*, *STEP 2* and
//! *STEP 3* respectively. STEP 1 should be performed once per LEM. Then STEP 2
//! will need as many iterations as it takes to evaluate the Lurk expression and
//! so will STEP 3.

use std::collections::{HashMap, HashSet};

use anyhow::{anyhow, bail, Context, Result};
use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    ConstraintSystem,
};

use crate::circuit::gadgets::{
    constraints::{
        alloc_equal_const, and, enforce_selector_with_premise, implies_equal, implies_equal_zero,
    },
    data::{allocate_constant, hash_poseidon},
    pointer::AllocatedPtr,
};

use crate::field::{FWrap, LurkField};

use super::{
    interpreter::Frame,
    pointers::{Ptr, ZPtr},
    store::Store,
    tag::Tag,
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

    #[inline]
    pub(crate) fn consume_hash2(&mut self) -> usize {
        self.hash2 += 1;
        self.hash2 - 1
    }

    #[inline]
    pub(crate) fn consume_hash3(&mut self) -> usize {
        self.hash3 += 1;
        self.hash3 - 1
    }

    #[inline]
    pub(crate) fn consume_hash4(&mut self) -> usize {
        self.hash4 += 1;
        self.hash4 - 1
    }

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
                cases.values().fold(SlotsCounter::default(), |acc, block| {
                    acc.max(block.count_slots())
                })
            }
            LEMCTL::MatchSymbol(_, cases, def) => cases
                .values()
                .fold(def.count_slots(), |acc, block| acc.max(block.count_slots())),
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

impl MetaPtr {
    fn to_zptr<F: LurkField>(&self, frame: &Frame<F>, store: &mut Store<F>) -> Result<ZPtr<F>> {
        match frame.bindings.get(self) {
            Some(ptr) => store.hash_ptr(ptr),
            None => Ok(ZPtr::dummy()),
        }
    }
}

impl LEM {
    /// Allocates an unconstrained pointer
    fn allocate_ptr<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        z_ptr: &ZPtr<F>,
        name: &AString,
        allocated_ptrs: &mut HashMap<AString, AllocatedPtr<F>>,
    ) -> Result<AllocatedPtr<F>> {
        if allocated_ptrs.contains_key(name) {
            bail!("{} already allocated", name);
        };
        let allocated_tag =
            allocate_num(cs, &format!("allocate {name}'s tag"), z_ptr.tag.to_field())?;
        let allocated_hash = allocate_num(cs, &format!("allocate {name}'s hash"), z_ptr.hash)?;
        let allocated_ptr = AllocatedPtr::from_parts(allocated_tag, allocated_hash);
        allocated_ptrs.insert(name.clone(), allocated_ptr.clone());
        Ok(allocated_ptr)
    }

    /// Allocates an unconstrained pointer for each input of the frame
    fn allocate_input<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &mut Store<F>,
        frame: &Frame<F>,
        allocated_ptrs: &mut HashMap<AString, AllocatedPtr<F>>,
    ) -> Result<()> {
        for (i, ptr) in frame.input.iter().enumerate() {
            let name = &self.input_vars[i];
            Self::allocate_ptr(cs, &store.hash_ptr(ptr)?, name, allocated_ptrs)?;
        }
        Ok(())
    }

    /// Allocates an unconstrained pointer for each output of the frame
    fn allocate_output<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        store: &mut Store<F>,
        frame: &Frame<F>,
        allocated_ptrs: &mut HashMap<AString, AllocatedPtr<F>>,
    ) -> Result<Vec<AllocatedPtr<F>>> {
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
        Ok(allocated_output_ptrs)
    }

    /// Allocates an unconstrained pointer for each value of the preimage
    fn allocate_preimg<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        preimg: &[MetaPtr],
        frame: &Frame<F>,
        store: &mut Store<F>,
        allocated_ptrs: &mut HashMap<AString, AllocatedPtr<F>>,
    ) -> Result<Vec<AllocatedPtr<F>>> {
        preimg
            .iter()
            .map(|x| {
                x.to_zptr(frame, store)
                    .and_then(|ref ptr| Self::allocate_ptr(cs, ptr, x.name(), allocated_ptrs))
            })
            .collect::<Result<Vec<_>>>()
    }

    fn get_allocated_preimg<'a, F: LurkField>(
        preimg: &[MetaPtr],
        allocated_ptrs: &'a HashMap<AString, AllocatedPtr<F>>,
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
        preimgs: &[Vec<Ptr<F>>],
        slot_type: SlotType,
        num_slots: usize,
        store: &mut Store<F>,
    ) -> Result<Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>> {
        assert!(
            preimgs.len() <= num_slots,
            "collected preimages exceeded the number of available slots"
        );

        let mut preallocations = vec![];

        // First we perform the allocations for the slots containing data collected
        // by the interpreter
        for (slot_idx, preimg) in preimgs.iter().enumerate() {
            let slot = Slot {
                idx: slot_idx,
                typ: slot_type,
            };
            // Allocate the preimage because the image depends on it
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

            // Allocate the image by calling the arithmetic function according
            // to the slot type
            let preallocated_img =
                Self::allocate_img_for_slot(cs, &slot, preallocated_preimg.clone(), store)?;

            preallocations.push((preallocated_preimg, preallocated_img));
        }

        // Then we do the same with dummies for the remaining slots
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
            let preallocated_img =
                Self::allocate_img_for_slot(cs, &slot, preallocated_preimg.clone(), store)?;

            preallocations.push((preallocated_preimg, preallocated_img));
        }
        Ok(preallocations)
    }

    /// Create R1CS constraints for LEM given an evaluation frame. This function
    /// implements the STEP 3 mentioned above.
    ///
    /// Regarding the slot optimizations, STEP 3 uses information gathered during
    /// STEPs 1 and 2. So we proceed by first allocating preimages and images for
    /// each slot and then, as we traverse the LEM, we add constraints to make sure
    /// that the witness satisfies the arithmetic equations for the corresponding
    /// slots.
    pub fn synthesize<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &mut Store<F>,
        slots_count: &SlotsCounter,
        frame: &Frame<F>,
    ) -> Result<()> {
        let mut global_allocator = GlobalAllocator::default();
        let mut allocated_ptrs: HashMap<AString, AllocatedPtr<F>> = HashMap::default();

        // Inputs are constrained by their usage inside LEM
        self.allocate_input(cs, store, frame, &mut allocated_ptrs)?;
        // Outputs are constrained by return. All LEMs return
        let preallocated_outputs = LEM::allocate_output(cs, store, frame, &mut allocated_ptrs)?;

        // Slots are constrained by their usage inside LEM. The ones not used in throughout the concrete path
        // are effectively unconstrained, that's why they are filled with dummies
        let preallocated_hash2_slots = LEM::allocate_slots(
            cs,
            &frame.preimages.hash2_ptrs,
            SlotType::Hash2,
            slots_count.hash2,
            store,
        )?;

        let preallocated_hash3_slots = LEM::allocate_slots(
            cs,
            &frame.preimages.hash3_ptrs,
            SlotType::Hash3,
            slots_count.hash3,
            store,
        )?;

        let preallocated_hash4_slots = LEM::allocate_slots(
            cs,
            &frame.preimages.hash4_ptrs,
            SlotType::Hash4,
            slots_count.hash4,
            store,
        )?;

        struct Globals<'a, F: LurkField> {
            store: &'a mut Store<F>,
            frame: &'a Frame<F>,
            global_allocator: &'a mut GlobalAllocator<F>,
            allocated_ptrs: HashMap<AString, AllocatedPtr<F>>,
            preallocated_outputs: Vec<AllocatedPtr<F>>,
            preallocated_hash2_slots: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
            preallocated_hash3_slots: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
            preallocated_hash4_slots: Vec<(Vec<AllocatedNum<F>>, AllocatedNum<F>)>,
        }

        fn recurse<F: LurkField, CS: ConstraintSystem<F>>(
            cs: &mut CS,
            block: &LEMCTL,
            concrete_path: Boolean,
            slots_count: &mut SlotsCounter,
            g: &mut Globals<'_, F>,
        ) -> Result<()> {
            match block {
                LEMCTL::Return(output_vars) => {
                    for (i, output_var) in output_vars.iter().enumerate() {
                        let Some(allocated_ptr) = g.allocated_ptrs.get(output_var.name()) else {
                            bail!("{output_var} not allocated")
                        };

                        allocated_ptr
                            .implies_ptr_equal(
                                &mut cs.namespace(|| {
                                    format!("implies_ptr_equal {output_var} (output_var {i})")
                                }),
                                &concrete_path,
                                &g.preallocated_outputs[i],
                            )
                            .with_context(|| "couldn't constrain `implies_ptr_equal`")?;
                    }
                    Ok(())
                }
                LEMCTL::MatchTag(match_ptr, cases) => {
                    let allocated_match_tag = match g.allocated_ptrs.get(match_ptr.name()) {
                        Some(allocated_match_ptr) => allocated_match_ptr.tag().clone(),
                        None => bail!("{match_ptr} not allocated"),
                    };
                    let mut concrete_path_vec = Vec::new();
                    for (tag, op) in cases {
                        let allocated_has_match = alloc_equal_const(
                            &mut cs.namespace(|| format!("{tag}.alloc_equal_const")),
                            &allocated_match_tag,
                            tag.to_field::<F>(),
                        )
                        .with_context(|| "couldn't allocate equal const")?;

                        let concrete_path_and_has_match = and(
                            &mut cs.namespace(|| format!("{tag}.and")),
                            &concrete_path,
                            &allocated_has_match,
                        )
                        .with_context(|| "failed to constrain `and`")?;

                        concrete_path_vec.push(allocated_has_match);

                        let saved_slot = &mut slots_count.clone();
                        recurse(
                            &mut cs.namespace(|| format!("{}", tag)),
                            op,
                            concrete_path_and_has_match,
                            saved_slot,
                            g,
                        )?;
                    }

                    // Now we need to enforce that at exactly one path was taken. We do that by enforcing
                    // that the sum of the previously collected `Boolean`s is one. But, of course, this
                    // irrelevant if we're on a virtual path and thus we use an implication gadget.
                    enforce_selector_with_premise(
                        &mut cs.namespace(|| "enforce_selector_with_premise"),
                        &concrete_path,
                        &concrete_path_vec,
                    )
                    .with_context(|| " couldn't constrain `enforce_selector_with_premise`")?;
                    Ok(())
                }
                LEMCTL::MatchSymbol(..) => Ok(()),
                LEMCTL::Seq(ops, rest) => {
                    for op in ops {
                        macro_rules! constrain_slot {
                            ( $preimg: expr, $img: expr, $allocated_preimg: expr, $allocated_img: expr, $slot: expr ) => {
                                // Retrieve the preallocated preimage and image for this slot
                                let (preallocated_preimg, preallocated_img) =
                                    match $slot {
                                        SlotType::Hash2 => &g.preallocated_hash2_slots[slots_count.consume_hash2()],
                                        SlotType::Hash3 => &g.preallocated_hash3_slots[slots_count.consume_hash3()],
                                        SlotType::Hash4 => &g.preallocated_hash4_slots[slots_count.consume_hash4()],
                                    };

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
                                // Allocate image. Its hash field is constrained by `constrain_slot!`
                                let allocated_img = LEM::allocate_ptr(
                                    cs,
                                    &$img.to_zptr(&g.frame, g.store)?,
                                    $img.name(),
                                    &mut g.allocated_ptrs,
                                )?;
                                // Create constraint for the tag
                                let allocated_tag =
                                    g.global_allocator.get_or_alloc_const(cs, $tag.to_field())?;
                                implies_equal(
                                    &mut cs
                                        .namespace(|| format!("implies equal for {}'s tag", $img)),
                                    &concrete_path,
                                    allocated_img.tag(),
                                    &allocated_tag,
                                )?;

                                // Retrieve allocated preimage
                                let allocated_preimg =
                                    LEM::get_allocated_preimg($preimg, &g.allocated_ptrs)?;

                                // Add the hash constraints
                                constrain_slot!(
                                    $preimg,
                                    $img,
                                    allocated_preimg,
                                    allocated_img,
                                    $slot
                                );
                            };
                        }

                        macro_rules! unhash_helper {
                            ( $preimg: expr, $img: expr, $slot: expr ) => {
                                // Allocate preimage to be constrained later by `constrain_slot!`
                                let allocated_preimg =
                                    LEM::allocate_preimg(cs, $preimg, &g.frame, g.store, &mut g.allocated_ptrs)?;

                                // Retrieve allocated image
                                let Some(allocated_img) = g.allocated_ptrs.get($img.name()) else {
                                                                    bail!("{} not allocated", $img)
                                                                };

                                // Add the hash constraints
                                constrain_slot!($preimg, $img, allocated_preimg, allocated_img, $slot);
                            };
                        }

                        match op {
                            LEMOP::Hash2(img, tag, preimg) => {
                                hash_helper!(img, tag, preimg, SlotType::Hash2);
                            }
                            LEMOP::Hash3(img, tag, preimg) => {
                                hash_helper!(img, tag, preimg, SlotType::Hash3);
                            }
                            LEMOP::Hash4(img, tag, preimg) => {
                                hash_helper!(img, tag, preimg, SlotType::Hash4);
                            }
                            LEMOP::Unhash2(preimg, img) => {
                                unhash_helper!(preimg, img, SlotType::Hash2);
                            }
                            LEMOP::Unhash3(preimg, img) => {
                                unhash_helper!(preimg, img, SlotType::Hash3);
                            }
                            LEMOP::Unhash4(preimg, img) => {
                                unhash_helper!(preimg, img, SlotType::Hash4);
                            }
                            LEMOP::Null(tgt, tag) => {
                                let allocated_tgt = LEM::allocate_ptr(
                                    cs,
                                    &tgt.to_zptr(g.frame, g.store)?,
                                    tgt.name(),
                                    &mut g.allocated_ptrs,
                                )?;
                                let allocated_tag =
                                    g.global_allocator.get_or_alloc_const(cs, tag.to_field())?;

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
                    recurse(cs, rest, concrete_path, slots_count, g)
                }
            }
        }

        recurse(
            cs,
            &self.ctl,
            Boolean::Constant(true),
            &mut SlotsCounter::default(),
            &mut Globals {
                store,
                frame,
                global_allocator: &mut global_allocator,
                allocated_ptrs,
                preallocated_outputs,
                preallocated_hash2_slots,
                preallocated_hash3_slots,
                preallocated_hash4_slots,
            },
        )
    }

    /// Computes the number of constraints that `synthesize` should create. It's
    /// also an explicit way to document and attest how the number of constraints
    /// grow.
    pub fn num_constraints(&self, slots_count: &SlotsCounter) -> usize {
        // fixed cost for each slot
        let mut num_constraints =
            289 * slots_count.hash2 + 337 * slots_count.hash3 + 388 * slots_count.hash4;

        let mut tags: HashSet<&Tag> = HashSet::default();

        let mut stack = vec![(&self.ctl, false)];
        while let Some((block, nested)) = stack.pop() {
            match block {
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
                    for block in cases.values() {
                        stack.push((block, true));
                    }
                }
                LEMCTL::MatchSymbol(..) => todo!(),
                LEMCTL::Seq(ops, rest) => {
                    for op in ops {
                        match op {
                            LEMOP::Null(_, tag) => {
                                // constrain tag and hash
                                num_constraints += 2;
                                tags.insert(tag);
                            }
                            LEMOP::Hash2(_, tag, _) => {
                                // tag and hash for 3 pointers: 1 image + 2 from preimage
                                num_constraints += 6;
                                tags.insert(tag);
                            }
                            LEMOP::Hash3(_, tag, _) => {
                                // tag and hash for 4 pointers: 1 image + 3 from preimage
                                num_constraints += 8;
                                tags.insert(tag);
                            }
                            LEMOP::Hash4(_, tag, _) => {
                                // tag and hash for 5 pointers: 1 image + 4 from preimage
                                num_constraints += 10;
                                tags.insert(tag);
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

        num_constraints + tags.len()
    }
}
