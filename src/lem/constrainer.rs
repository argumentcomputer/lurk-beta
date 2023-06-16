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
    interpreter::Frame, path::Path, pointers::ZPtr, store::Store, MetaPtr, NumSlots, LEM, LEMOP,
};

/// Contains preimage and image.
/// REMARK: this structure will be populated in the second LEM traversal, which
/// corresponds to STEP 2 of the hash slots mechanism. In particular, STEP 2
/// happens during interpretation of LEM and stores the hash witnesses in the
/// order they appear during interpretation
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum HashWitness {
    Hash2([MetaPtr; 2], MetaPtr),
    Hash3([MetaPtr; 3], MetaPtr),
    Hash4([MetaPtr; 4], MetaPtr),
}

impl LEMOP {
    /// STEP 1 from hash slots:
    /// Computes the number of slots needed for a LEMOP
    /// This is the first LEM traversal.
    pub fn num_hash_slots(&self) -> NumSlots {
        match self {
            LEMOP::Hash2(..) | LEMOP::Unhash2(..) => NumSlots::new((1, 0, 0)),
            LEMOP::Hash3(..) | LEMOP::Unhash3(..) => NumSlots::new((0, 1, 0)),
            LEMOP::Hash4(..) | LEMOP::Unhash4(..) => NumSlots::new((0, 0, 1)),
            LEMOP::MatchTag(_, cases) => cases
                .values()
                .fold(NumSlots::default(), |acc, op| acc.max(&op.num_hash_slots())),
            LEMOP::MatchSymPath(_, cases, def) => {
                cases.values().fold(def.num_hash_slots(), |acc, op| {
                    acc.max(&op.num_hash_slots())
                })
            }
            LEMOP::Seq(ops) => ops
                .iter()
                .fold(NumSlots::default(), |acc, op| acc.add(&op.num_hash_slots())),
            _ => NumSlots::default(),
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

#[derive(Default)]
struct PathTracker(HashMap<Path, usize>);

impl PathTracker {
    pub(crate) fn next(&mut self, path: &Path) -> usize {
        match self.0.get(path) {
            Some(i) => {
                let next = i + 1;
                self.0.insert(path.clone(), next);
                next
            }
            None => {
                self.0.insert(path.clone(), 0);
                0
            }
        }
    }
}

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

    fn inputize_ptr<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        allocated_ptr: &AllocatedPtr<F>,
        name: &String,
    ) -> Result<()> {
        allocated_ptr
            .tag()
            .inputize(cs.namespace(|| format!("inputize {}'s tag", name)))
            .with_context(|| format!("couldn't inputize {name}'s tag"))?;
        allocated_ptr
            .hash()
            .inputize(cs.namespace(|| format!("inputize {}'s hash", name)))
            .with_context(|| format!("couldn't inputize {name}'s hash"))?;
        Ok(())
    }

    fn allocate_and_inputize_input<'a, F: LurkField, CS: ConstraintSystem<F>>(
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
            Self::inputize_ptr(cs, &allocated_ptr, name)?;
            allocated_ptrs.insert(name, allocated_ptr);
        }
        Ok(())
    }

    fn allocate_and_inputize_output<'a, F: LurkField, CS: ConstraintSystem<F>>(
        &'a self,
        cs: &mut CS,
        store: &mut Store<F>,
        frame: &Frame<F>,
        allocated_ptrs: &HashMap<&'a String, AllocatedPtr<F>>,
    ) -> Result<[AllocatedPtr<F>; 3]> {
        let mut allocated_output_ptrs = vec![];
        for (i, ptr) in frame.output.iter().enumerate() {
            let output_name = &format!("output[{}]", i);
            let allocated_ptr =
                Self::allocate_ptr(cs, &store.hash_ptr(ptr)?, output_name, allocated_ptrs)?;
            Self::inputize_ptr(cs, &allocated_ptr, output_name)?;
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
            store.hash_ptr(mptr.get_ptr(&frame.ptrs)?)
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
    pub fn constrain<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        alloc_manager: &mut AllocationManager<F>,
        store: &mut Store<F>,
        frame: &Frame<F>,
        num_hash_slots: &NumSlots,
    ) -> Result<()> {
        let mut allocated_ptrs: HashMap<&String, AllocatedPtr<F>> = HashMap::default();

        self.allocate_and_inputize_input(cs, store, frame, &mut allocated_ptrs)?;
        let preallocated_outputs =
            self.allocate_and_inputize_output(cs, store, frame, &allocated_ptrs)?;

        let dummy_val = alloc_manager.get_or_alloc_num(cs, F::ZERO)?;
        let dummy_poseidon2 = hash_poseidon(
            &mut cs.namespace(|| format!("dummy hash 2")),
            vec![
                dummy_val.clone(),
                dummy_val.clone(),
                dummy_val.clone(),
                dummy_val.clone(),
            ],
            store.poseidon_cache.constants.c4(),
        )?;
        let dummy_poseidon3 = hash_poseidon(
            &mut cs.namespace(|| format!("dummy hash 3")),
            vec![
                dummy_val.clone(),
                dummy_val.clone(),
                dummy_val.clone(),
                dummy_val.clone(),
                dummy_val.clone(),
                dummy_val.clone(),
            ],
            store.poseidon_cache.constants.c6(),
        )?;
        let dummy_poseidon4 = hash_poseidon(
            &mut cs.namespace(|| format!("dummy hash 4")),
            vec![
                dummy_val.clone(),
                dummy_val.clone(),
                dummy_val.clone(),
                dummy_val.clone(),
                dummy_val.clone(),
                dummy_val.clone(),
                dummy_val.clone(),
                dummy_val.clone(),
            ],
            store.poseidon_cache.constants.c8(),
        )?;

        let mut slots2: Vec<AllocatedNum<F>> = Vec::default();
        let mut slots3: Vec<AllocatedNum<F>> = Vec::default();
        let mut slots4: Vec<AllocatedNum<F>> = Vec::default();

        for (i, hash_witness) in frame.hash_witnesses.iter().enumerate() {
            match hash_witness {
                HashWitness::Hash2(preimg, _) => {
                    let preimg0 = Self::allocate_ptr(
                        cs,
                        &store.hash_ptr(preimg[0].get_ptr(&frame.ptrs)?)?,
                        &format!("preallocated 2 0 {i}"),
                        &allocated_ptrs,
                    )?;
                    let preimg1 = Self::allocate_ptr(
                        cs,
                        &store.hash_ptr(preimg[1].get_ptr(&frame.ptrs)?)?,
                        &format!("preallocated 2 1 {i}"),
                        &allocated_ptrs,
                    )?;
                    let allocated_hash = hash_poseidon(
                        &mut cs.namespace(|| format!("poseidon2 for {i}")),
                        vec![
                            preimg0.tag().clone(),
                            preimg0.hash().clone(),
                            preimg1.tag().clone(),
                            preimg1.hash().clone(),
                        ],
                        store.poseidon_cache.constants.c4(),
                    )?;
                    slots2.push(allocated_hash);
                }
                HashWitness::Hash3(preimg, _) => {
                    let preimg0 = Self::allocate_ptr(
                        cs,
                        &store.hash_ptr(preimg[0].get_ptr(&frame.ptrs)?)?,
                        &format!("preallocated 3 0 {i}"),
                        &allocated_ptrs,
                    )?;
                    let preimg1 = Self::allocate_ptr(
                        cs,
                        &store.hash_ptr(preimg[1].get_ptr(&frame.ptrs)?)?,
                        &format!("preallocated 3 1 {i}"),
                        &allocated_ptrs,
                    )?;
                    let preimg2 = Self::allocate_ptr(
                        cs,
                        &store.hash_ptr(preimg[2].get_ptr(&frame.ptrs)?)?,
                        &format!("preallocated 3 2 {i}"),
                        &allocated_ptrs,
                    )?;
                    let allocated_hash = hash_poseidon(
                        &mut cs.namespace(|| format!("poseidon3 for {i}")),
                        vec![
                            preimg0.tag().clone(),
                            preimg0.hash().clone(),
                            preimg1.tag().clone(),
                            preimg1.hash().clone(),
                            preimg2.tag().clone(),
                            preimg2.hash().clone(),
                        ],
                        store.poseidon_cache.constants.c6(),
                    )?;
                    slots3.push(allocated_hash);
                }
                HashWitness::Hash4(preimg, _) => {
                    let preimg0 = Self::allocate_ptr(
                        cs,
                        &store.hash_ptr(preimg[0].get_ptr(&frame.ptrs)?)?,
                        &format!("preallocated 4 0 {i}"),
                        &allocated_ptrs,
                    )?;
                    let preimg1 = Self::allocate_ptr(
                        cs,
                        &store.hash_ptr(preimg[1].get_ptr(&frame.ptrs)?)?,
                        &format!("preallocated 4 1 {i}"),
                        &allocated_ptrs,
                    )?;
                    let preimg2 = Self::allocate_ptr(
                        cs,
                        &store.hash_ptr(preimg[2].get_ptr(&frame.ptrs)?)?,
                        &format!("preallocated 4 2 {i}"),
                        &allocated_ptrs,
                    )?;
                    let preimg3 = Self::allocate_ptr(
                        cs,
                        &store.hash_ptr(preimg[3].get_ptr(&frame.ptrs)?)?,
                        &format!("preallocated 4 3 {i}"),
                        &allocated_ptrs,
                    )?;
                    let allocated_hash = hash_poseidon(
                        &mut cs.namespace(|| format!("poseidon4 for {i}")),
                        vec![
                            preimg0.tag().clone(),
                            preimg0.hash().clone(),
                            preimg1.tag().clone(),
                            preimg1.hash().clone(),
                            preimg2.tag().clone(),
                            preimg2.hash().clone(),
                            preimg3.tag().clone(),
                            preimg3.hash().clone(),
                        ],
                        store.poseidon_cache.constants.c8(),
                    )?;
                    slots4.push(allocated_hash);
                }
            }
        }

        // for i in slots2.len()..num_hash_slots.hash2 {
        //     slots2.push(
        //         hash_poseidon(
        //             &mut cs.namespace(|| format!("poseidon 2")),
        //             vec![
        //                 dummy_val.clone(),
        //                 dummy_val.clone(),
        //                 dummy_val.clone(),
        //                 dummy_val.clone(),
        //             ],
        //             store.poseidon_cache.constants.c4(),
        //         )?
        //     )
        // }
        
        let mut path_tracker2 = PathTracker::default();
        let mut path_tracker3 = PathTracker::default();
        let mut path_tracker4 = PathTracker::default();

        let mut stack = vec![(&self.lem_op, Boolean::Constant(true), Path::default())];
        while let Some((op, concrete_path, path)) = stack.pop() {
            macro_rules! hash_helper {
                ( $img: expr, $tag: expr ) => {{
                    // STEP 3: Allocate image
                    let allocated_img = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_frame(&concrete_path, frame, $img, store)?,
                        $img.name(),
                        &allocated_ptrs,
                    )?;

                    // STEP 3: Create constraint for the tag
                    let allocated_tag = alloc_manager.get_or_alloc_num(cs, $tag.to_field())?;
                    implies_equal(
                        &mut cs.namespace(|| format!("implies equal for {}'s tag", $img.name())),
                        &concrete_path,
                        allocated_img.tag(),
                        &allocated_tag,
                    )?;

                    // STEP 3: Insert allocated image into allocated pointers
                    allocated_ptrs.insert($img.name(), allocated_img.clone());
                    allocated_img
                }};
            }
            macro_rules! unhash_helper {
                ( $preimg: expr ) => {
                    // STEP 3: Get preimage from allocated pointers
                    let preimg_vec = Self::alloc_preimg(
                        cs,
                        $preimg,
                        &concrete_path,
                        frame,
                        store,
                        &allocated_ptrs,
                    )?;

                    // STEP 3: Insert preimage pointers in the HashMap
                    for (name, p) in $preimg
                        .iter()
                        .map(|pi| pi.name())
                        .zip(preimg_vec.into_iter())
                    {
                        allocated_ptrs.insert(name, p);
                    }
                };
            }

            match op {
                LEMOP::Hash2(img, tag, _) => {
                    let allocated_img = hash_helper!(img, tag);
                    implies_equal(
                        &mut cs
                            .namespace(|| format!("implies equal hash for hash2{}", img.name(),)),
                        &concrete_path,
                        &allocated_img.hash(),
                        &slots2[path_tracker2.next(&path)],
                    )?;
                }
                LEMOP::Hash3(img, tag, _) => {
                    let allocated_img = hash_helper!(img, tag);
                    implies_equal(
                        &mut cs
                            .namespace(|| format!("implies equal hash for hash3{}", img.name(),)),
                        &concrete_path,
                        &allocated_img.hash(),
                        &slots3[path_tracker3.next(&path)],
                    )?;
                }
                LEMOP::Hash4(img, tag, _) => {
                    let allocated_img = hash_helper!(img, tag);
                    implies_equal(
                        &mut cs
                            .namespace(|| format!("implies equal hash for hash4{}", img.name(),)),
                        &concrete_path,
                        &allocated_img.hash(),
                        &slots4[path_tracker4.next(&path)],
                    )?;
                }
                LEMOP::Unhash2(preimg, _) => {
                    unhash_helper!(preimg);
                }
                LEMOP::Unhash3(preimg, _) => {
                    unhash_helper!(preimg);
                }
                LEMOP::Unhash4(preimg, _) => {
                    unhash_helper!(preimg);
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

                        stack.push((op, concrete_path_and_has_match, path.push_tag(tag)));
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
}
