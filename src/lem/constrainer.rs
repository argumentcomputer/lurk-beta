use std::collections::HashMap;

use anyhow::{anyhow, bail, Context, Result};
use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    ConstraintSystem,
};

use crate::circuit::gadgets::{
    constraints::{
        alloc_equal_const, and, enforce_equal, enforce_equal_zero, enforce_popcount_one,
        enforce_selector_with_premise, implies_equal, implies_equal_zero,
    },
    data::hash_poseidon,
    pointer::AllocatedPtr,
};

use crate::field::{FWrap, LurkField};

use super::{pointers::ZPtr, store::Store, MetaPtr, Tag, Valuation, LEM, LEMOP};

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
            Some(alloc) => Ok(alloc.to_owned()),
            None => {
                let digits = f.hex_digits();
                let alloc =
                    AllocatedNum::alloc(cs.namespace(|| format!("allocate {digits}")), || Ok(f))
                        .with_context(|| format!("couldn't allocate {digits}"))?;
                self.0.insert(wrap, alloc.clone());
                Ok(alloc)
            }
        }
    }

    /// Calls `get_or_alloc_num` to allocate tag and hash for a pointer.
    pub(crate) fn get_or_alloc_ptr<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        z_ptr: &ZPtr<F>,
    ) -> Result<AllocatedPtr<F>> {
        Ok(AllocatedPtr::from_parts(
            &self.get_or_alloc_num(cs, z_ptr.tag.to_field())?,
            &self.get_or_alloc_num(cs, z_ptr.hash)?,
        ))
    }
}

#[derive(Default)]
struct SlotData {
    max_slots: usize,
    implies_data: Vec<(Boolean, usize, MetaPtr, Tag)>,
    enforce_data: Vec<(usize, MetaPtr, Tag)>,
}

#[derive(Default)]
struct HashSlots<F: LurkField> {
    hash2_alloc: Vec<(usize, AllocatedPtr<F>, AllocatedPtr<F>)>,
    hash2_data: SlotData,
    hash3_alloc: Vec<(usize, AllocatedPtr<F>, AllocatedPtr<F>, AllocatedPtr<F>)>,
    hash3_data: SlotData,
    hash4_alloc: Vec<(
        usize,
        AllocatedPtr<F>,
        AllocatedPtr<F>,
        AllocatedPtr<F>,
        AllocatedPtr<F>,
    )>,
    hash4_data: SlotData,
}

enum AllocHashPreimage<F: LurkField> {
    A2(AllocatedPtr<F>, AllocatedPtr<F>),
    A3(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedPtr<F>),
    A4(
        AllocatedPtr<F>,
        AllocatedPtr<F>,
        AllocatedPtr<F>,
        AllocatedPtr<F>,
    ),
}

#[derive(Default, Clone)]
pub struct SlotsIndices {
    pub hash2_idx: usize,
    pub hash3_idx: usize,
    pub hash4_idx: usize,
}

/// Encodes whether we're certainly on a concrete LEM path or on a path that
/// might be concrete or virtual depending on what happened on interpretation.
#[derive(Clone)]
enum PathKind {
    /// No logical branches have happened in the LEM so far
    Concrete,
    /// We're on a logical LEM path, which might be *virtual* or *concrete*
    /// depending on what happened during interpretation.
    MaybeConcrete(Boolean),
}

impl LEM {
    fn allocate_ptr<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        z_ptr: &ZPtr<F>,
        name: &String,
        alloc_ptrs: &HashMap<&String, AllocatedPtr<F>>,
    ) -> Result<AllocatedPtr<F>> {
        if alloc_ptrs.contains_key(name) {
            bail!("{} already allocated", name);
        };
        let alloc_tag =
            AllocatedNum::alloc(cs.namespace(|| format!("allocate {name}'s tag")), || {
                Ok(z_ptr.tag.to_field())
            })
            .with_context(|| format!("couldn't allocate {name}'s tag"))?;
        let alloc_hash =
            AllocatedNum::alloc(cs.namespace(|| format!("allocate {name}'s hash")), || {
                Ok(z_ptr.hash)
            })
            .with_context(|| format!("couldn't allocate {name}'s hash"))?;
        Ok(AllocatedPtr::from_parts(&alloc_tag, &alloc_hash))
    }

    fn inputize_ptr<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        alloc_ptr: &AllocatedPtr<F>,
        name: &String,
    ) -> Result<()> {
        alloc_ptr
            .tag()
            .inputize(cs.namespace(|| format!("inputize {}'s tag", name)))
            .with_context(|| format!("couldn't inputize {name}'s tag"))?;
        alloc_ptr
            .hash()
            .inputize(cs.namespace(|| format!("inputize {}'s hash", name)))
            .with_context(|| format!("couldn't inputize {name}'s hash"))?;
        Ok(())
    }

    fn on_concrete_path(concrete_path: &PathKind) -> Result<bool> {
        match concrete_path {
            PathKind::Concrete => Ok(true),
            PathKind::MaybeConcrete(concrete_path) => concrete_path
                .get_value()
                .ok_or_else(|| anyhow!("Couldn't check whether we're on a concrete path")),
        }
    }

    fn z_ptr_from_valuation<F: LurkField>(
        path_kind: &PathKind,
        valuation: &Valuation<F>,
        name: &String,
        store: &mut Store<F>,
    ) -> Result<ZPtr<F>> {
        if Self::on_concrete_path(path_kind)? {
            let Some(ptr) = valuation.ptrs.get(name) else {
                bail!("Couldn't retrieve {} from valuation", name);
            };
            store.hydrate_ptr(ptr)
        } else {
            Ok(ZPtr::dummy())
        }
    }

    fn allocate_and_inputize_input<'a, F: LurkField, CS: ConstraintSystem<F>>(
        &'a self,
        cs: &mut CS,
        store: &mut Store<F>,
        valuation: &Valuation<F>,
        alloc_ptrs: &mut HashMap<&'a String, AllocatedPtr<F>>,
        idx: usize,
    ) -> Result<()> {
        let alloc_ptr = Self::allocate_ptr(
            cs,
            &store.hydrate_ptr(&valuation.input[idx])?,
            &self.input[idx],
            alloc_ptrs,
        )?;
        alloc_ptrs.insert(&self.input[idx], alloc_ptr.clone());
        Self::inputize_ptr(cs, &alloc_ptr, &self.input[idx])?;
        Ok(())
    }

    /// Accumulates slot data that will be used later to generate the constraints.
    ///
    /// If we're definitely on a concrete path, then we accumulate data to be
    /// constrained with regular enforcements.
    ///
    /// If we're probably on a concrete path, then we accumulate data to be
    /// constrained with implications.
    fn acc_hash_slots_data<F: LurkField>(
        path_kind: &PathKind,
        hash_slots: &mut HashSlots<F>,
        slots: &SlotsIndices,
        hash: MetaPtr,
        alloc_arity: AllocHashPreimage<F>,
        tag: Tag,
    ) -> Result<()> {
        let is_concrete_path = Self::on_concrete_path(path_kind)?;
        match alloc_arity {
            AllocHashPreimage::A2(i0, i1) => {
                match path_kind {
                    PathKind::Concrete => {
                        hash_slots
                            .hash2_data
                            .enforce_data
                            .push((slots.hash2_idx, hash, tag));
                        hash_slots.hash2_alloc.push((slots.hash2_idx, i0, i1))
                    }
                    PathKind::MaybeConcrete(concrete_path) => {
                        if is_concrete_path {
                            // only once per path
                            hash_slots.hash2_alloc.push((slots.hash2_idx, i0, i1));
                        }
                        hash_slots.hash2_data.implies_data.push((
                            concrete_path.clone(),
                            slots.hash2_idx,
                            hash,
                            tag,
                        ));
                    }
                }
            }
            AllocHashPreimage::A3(i0, i1, i2) => {
                match path_kind {
                    PathKind::Concrete => {
                        hash_slots
                            .hash3_data
                            .enforce_data
                            .push((slots.hash3_idx, hash, tag));
                        hash_slots.hash3_alloc.push((slots.hash3_idx, i0, i1, i2))
                    }
                    PathKind::MaybeConcrete(concrete_path) => {
                        if is_concrete_path {
                            // only once per path
                            hash_slots.hash3_alloc.push((slots.hash3_idx, i0, i1, i2));
                        }
                        hash_slots.hash3_data.implies_data.push((
                            concrete_path.clone(),
                            slots.hash3_idx,
                            hash,
                            tag,
                        ));
                    }
                }
            }
            AllocHashPreimage::A4(i0, i1, i2, i3) => {
                match path_kind {
                    PathKind::Concrete => {
                        hash_slots
                            .hash4_data
                            .enforce_data
                            .push((slots.hash4_idx, hash, tag));
                        hash_slots
                            .hash4_alloc
                            .push((slots.hash4_idx, i0, i1, i2, i3))
                    }
                    PathKind::MaybeConcrete(concrete_path) => {
                        if is_concrete_path {
                            // only once per path
                            hash_slots
                                .hash4_alloc
                                .push((slots.hash4_idx, i0, i1, i2, i3));
                        }
                        hash_slots.hash4_data.implies_data.push((
                            concrete_path.clone(),
                            slots.hash4_idx,
                            hash,
                            tag,
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    /// Here we use the implies/enforce logic to contrain tag and hash values.
    /// When many branches are possible we will use the `implies_equal` gadget
    /// to ensure only concrete paths are implied. Otherwise, only one path
    /// exists, therefore it must be enforced. Hence we use two distinct data
    /// vectors, one for implications and another one for enforcements.
    fn create_slot_constraints<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        alloc_ptrs: &HashMap<&String, AllocatedPtr<F>>,
        implies_data: &Vec<(Boolean, usize, MetaPtr, Tag)>,
        enforce_data: &Vec<(usize, MetaPtr, Tag)>,
        hash_slots: &HashMap<usize, AllocatedNum<F>>,
        alloc_manager: &mut AllocationManager<F>,
    ) -> Result<()> {
        // Create hash implications
        for (concrete_path, slot, tgt, tag) in implies_data {
            // get alloc_tgt from tgt
            let Some(alloc_tgt) = alloc_ptrs.get(tgt.name()) else {
                bail!("{} not allocated", tgt.name());
            };

            // get slot_hash from slot name
            let Some(slot_hash) = hash_slots.get(slot) else {
                bail!("Slot {} not allocated", slot)
            };

            implies_equal(
                &mut cs
                    .namespace(|| format!("implies equal hash2 for {} and {}", slot, tgt.name())),
                concrete_path,
                alloc_tgt.hash(),
                slot_hash,
            )?;

            let alloc_tag = alloc_manager.get_or_alloc_num(cs, tag.to_field())?;
            implies_equal(
                &mut cs.namespace(|| {
                    format!("implies equal tag for {} and {} in hash2", slot, tgt.name())
                }),
                concrete_path,
                alloc_tgt.tag(),
                &alloc_tag,
            )?;
        }

        // Create hash enforce
        for (slot, tgt, tag) in enforce_data {
            // get alloc_tgt from tgt
            let Some(alloc_tgt) = alloc_ptrs.get(tgt.name()) else {
                bail!("{} not allocated", tgt.name());
            };

            // get slot_hash from slot name
            let Some(slot_hash) = hash_slots.get(slot) else {
                bail!("Slot number {} not allocated", slot)
            };

            enforce_equal(
                cs,
                || {
                    format!(
                        "enforce equal hash for tgt {} and slot number {}",
                        tgt.name(),
                        slot,
                    )
                },
                alloc_tgt.hash(),
                slot_hash,
            );

            let alloc_tag = alloc_manager.get_or_alloc_num(cs, tag.to_field())?;
            enforce_equal(
                cs,
                || {
                    format!(
                        "enforce equal tag for tgt {} and slot number {}",
                        tgt.name(),
                        slot,
                    )
                },
                alloc_tgt.tag(),
                &alloc_tag,
            );
        }
        Ok(())
    }

    fn alloc_preimage<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        preimg: &[MetaPtr],
        path_kind: &PathKind,
        valuation: &Valuation<F>,
        store: &mut Store<F>,
        alloc_ptrs: &HashMap<&String, AllocatedPtr<F>>,
    ) -> Result<Vec<AllocatedPtr<F>>> {
        preimg
            .iter()
            .map(|pre| {
                let name = pre.name();
                let res_ptr = Self::z_ptr_from_valuation(path_kind, valuation, name, store);
                res_ptr.and_then(|ref ptr| Self::allocate_ptr(cs, ptr, name, alloc_ptrs))
            })
            .collect::<Result<Vec<_>>>()
    }

    fn get_alloc_preimage<'a, F: LurkField>(
        preimg: &[MetaPtr],
        alloc_ptrs: &'a HashMap<&String, AllocatedPtr<F>>,
    ) -> Result<Vec<&'a AllocatedPtr<F>>> {
        let mut res = vec![];
        for i in preimg {
            match alloc_ptrs.get(i.name()) {
                None => bail!("{} not allocated", i.name()),
                Some(alloc_ptr) => {
                    res.push(alloc_ptr);
                }
            }
        }
        Ok(res)
    }

    /// Create R1CS constraints for LEM given an evaluation valuation.
    ///
    /// As we find recursive (non-leaf) LEM operations, we stack them to be
    /// constrained later, using hash maps to manage viariables and pointers in
    /// a way we can reference allocated variables that were previously created.
    ///
    /// Notably, we use a variable `path_kind: PathKind` to encode a three-way
    /// information:
    ///
    /// * If it's `Concrete`, it means that no logical branches have happened in
    /// the LEM so far, thus the evaluation algorithm must have gone through
    /// that operation. In this case, we use regular equality enforcements
    ///
    /// * If it's `MaybeConcrete(concrete_path)`, it means that we're on a logical
    /// LEM branch, which might be *virtual* or *concrete* depending on the
    /// valuation. A virtual path is one that wasn't taken during evaluation and
    /// thus its valuation pointers and variables weren't bound. A concrete path
    /// means that evaluation took that path and the valuation data should be
    /// complete. For virtual paths we need to create dummy bindings and relax the
    /// enforcements with implications whose premises are false. So, in the end,
    /// we use implications on both virtual and concrete paths to make sure that
    /// the circuit structure is always the same, independently of the valuation.
    /// The premise is precicely `concrete_path`.
    pub fn constrain_aux<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        alloc_manager: &mut AllocationManager<F>,
        store: &mut Store<F>,
        valuation: &Valuation<F>,
        max_slots_allowed: Option<&SlotsIndices>,
    ) -> Result<()> {
        let mut alloc_ptrs: HashMap<&String, AllocatedPtr<F>> = HashMap::default();

        // Allocate inputs
        for i in 0..3 {
            self.allocate_and_inputize_input(cs, store, valuation, &mut alloc_ptrs, i)?;
        }

        let mut num_inputized_outputs = 0;

        let mut hash_slots: HashSlots<F> = Default::default();
        let mut stack = vec![(
            &self.lem_op,
            PathKind::Concrete,
            String::new(),
            SlotsIndices::default(),
        )];
        while let Some((op, path_kind, path, slots)) = stack.pop() {
            match op {
                LEMOP::Hash2(hash, tag, preimg) => {
                    // Get preimage from allocated pointers
                    let preimg_vec = Self::get_alloc_preimage(preimg, &alloc_ptrs)?;

                    // Allocate new pointer containing expected hash value
                    let alloc_hash = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_valuation(&path_kind, valuation, hash.name(), store)?,
                        hash.name(),
                        &alloc_ptrs,
                    )?;

                    // Stack expected hash, preimage and tag, together with virtual path information,
                    // such that only concrete path hashes are indeed calculated in the next available
                    // hash slot.
                    Self::acc_hash_slots_data(
                        &path_kind,
                        &mut hash_slots,
                        &slots,
                        hash.clone(),
                        AllocHashPreimage::A2(preimg_vec[0].clone(), preimg_vec[1].clone()),
                        *tag,
                    )?;

                    // Insert hash value pointer in the HashMap
                    alloc_ptrs.insert(hash.name(), alloc_hash.clone());
                }
                LEMOP::Unhash2(preimg, hash, tag) => {
                    // Get preimage from allocated pointers
                    let preimg_vec = Self::alloc_preimage(
                        cs,
                        preimg,
                        &path_kind,
                        valuation,
                        store,
                        &alloc_ptrs,
                    )?;

                    // Stack expected hash, preimage and no tag, together with virtual path information,
                    // such that only concrete path hashes are indeed calculated in the next available
                    // hash slot.
                    Self::acc_hash_slots_data(
                        &path_kind,
                        &mut hash_slots,
                        &slots,
                        hash.clone(),
                        AllocHashPreimage::A2(preimg_vec[0].clone(), preimg_vec[1].clone()),
                        *tag,
                    )?;

                    // Insert preimage pointers in the HashMap
                    for (name, preimg) in preimg
                        .iter()
                        .map(|pi| pi.name())
                        .zip(preimg_vec.into_iter())
                    {
                        alloc_ptrs.insert(name, preimg);
                    }
                }
                LEMOP::Hash3(hash, tag, preimg) => {
                    // Get preimage from allocated pointers
                    let preimg_vec = Self::get_alloc_preimage(preimg, &alloc_ptrs)?;

                    // Allocate new pointer containing expected hash value
                    let alloc_hash = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_valuation(&path_kind, valuation, hash.name(), store)?,
                        hash.name(),
                        &alloc_ptrs,
                    )?;

                    // Stack expected hash, preimage and tag, together with virtual path information,
                    // such that only concrete path hashes are indeed calculated in the next available
                    // hash slot.
                    Self::acc_hash_slots_data(
                        &path_kind,
                        &mut hash_slots,
                        &slots,
                        hash.clone(),
                        AllocHashPreimage::A3(
                            preimg_vec[0].clone(),
                            preimg_vec[1].clone(),
                            preimg_vec[2].clone(),
                        ),
                        *tag,
                    )?;

                    // Insert hash value pointer in the HashMap
                    alloc_ptrs.insert(hash.name(), alloc_hash.clone());
                }
                LEMOP::Unhash3(preimg, hash, tag) => {
                    // Get preimage from allocated pointers
                    let preimg_vec = Self::alloc_preimage(
                        cs,
                        preimg,
                        &path_kind,
                        valuation,
                        store,
                        &alloc_ptrs,
                    )?;

                    // Stack expected hash, preimage and no tag, together with virtual path information,
                    // such that only concrete path hashes are indeed calculated in the next available
                    // hash slot.
                    Self::acc_hash_slots_data(
                        &path_kind,
                        &mut hash_slots,
                        &slots,
                        hash.clone(),
                        AllocHashPreimage::A3(
                            preimg_vec[0].clone(),
                            preimg_vec[1].clone(),
                            preimg_vec[2].clone(),
                        ),
                        *tag,
                    )?;

                    // Insert preimage pointers in the HashMap
                    for (name, preimg) in preimg
                        .iter()
                        .map(|pi| pi.name())
                        .zip(preimg_vec.into_iter())
                    {
                        alloc_ptrs.insert(name, preimg);
                    }
                }
                LEMOP::Hash4(hash, tag, preimg) => {
                    // Get preimage from allocated pointers
                    let preimg_vec = Self::get_alloc_preimage(preimg, &alloc_ptrs)?;

                    // Allocate new pointer containing expected hash value
                    let alloc_hash = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_valuation(&path_kind, valuation, hash.name(), store)?,
                        hash.name(),
                        &alloc_ptrs,
                    )?;

                    // Stack expected hash, preimage and tag, together with virtual path information,
                    // such that only concrete path hashes are indeed calculated in the next available
                    // hash slot.
                    Self::acc_hash_slots_data(
                        &path_kind,
                        &mut hash_slots,
                        &slots,
                        hash.clone(),
                        AllocHashPreimage::A4(
                            preimg_vec[0].clone(),
                            preimg_vec[1].clone(),
                            preimg_vec[2].clone(),
                            preimg_vec[3].clone(),
                        ),
                        *tag,
                    )?;

                    // Insert hash value pointer in the HashMap
                    alloc_ptrs.insert(hash.name(), alloc_hash.clone());
                }
                LEMOP::Unhash4(preimg, hash, tag) => {
                    // Get preimage from allocated pointers
                    let preimg_vec = Self::alloc_preimage(
                        cs,
                        preimg,
                        &path_kind,
                        valuation,
                        store,
                        &alloc_ptrs,
                    )?;

                    // Stack expected hash, preimage and no tag, together with virtual path information,
                    // such that only concrete path hashes are indeed calculated in the next available
                    // hash slot.
                    Self::acc_hash_slots_data(
                        &path_kind,
                        &mut hash_slots,
                        &slots,
                        hash.clone(),
                        AllocHashPreimage::A4(
                            preimg_vec[0].clone(),
                            preimg_vec[1].clone(),
                            preimg_vec[2].clone(),
                            preimg_vec[3].clone(),
                        ),
                        *tag,
                    )?;

                    // Insert preimage pointers in the HashMap
                    for (name, preimg) in preimg
                        .iter()
                        .map(|pi| pi.name())
                        .zip(preimg_vec.into_iter())
                    {
                        alloc_ptrs.insert(name, preimg);
                    }
                }
                LEMOP::Null(tgt, tag) => {
                    let alloc_tgt = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_valuation(&path_kind, valuation, tgt.name(), store)?,
                        tgt.name(),
                        &alloc_ptrs,
                    )?;
                    alloc_ptrs.insert(tgt.name(), alloc_tgt.clone());
                    let alloc_tag = alloc_manager.get_or_alloc_num(cs, tag.to_field())?;

                    // If `path_kind` is Some, then we constrain using "concrete implies ..." logic
                    if let PathKind::MaybeConcrete(concrete_path) = path_kind {
                        implies_equal(
                            &mut cs.namespace(|| format!("implies equal for {}'s tag", tgt.name())),
                            &concrete_path,
                            alloc_tgt.tag(),
                            &alloc_tag,
                        )
                        .with_context(|| {
                            format!("couldn't enforce implies equal for {}'s tag", tgt.name())
                        })?;
                        implies_equal_zero(
                            &mut cs.namespace(|| {
                                format!("implies equal zero for {}'s hash", tgt.name())
                            }),
                            &concrete_path,
                            alloc_tgt.hash(),
                        )
                        .with_context(|| {
                            format!(
                                "couldn't enforce implies equal zero for {}'s hash",
                                tgt.name()
                            )
                        })?;
                    } else {
                        // If `path_kind` is None, we just do regular constraining
                        enforce_equal(
                            cs,
                            || {
                                format!(
                                    "{}'s tag is {}",
                                    tgt.name(),
                                    tag.to_field::<F>().hex_digits()
                                )
                            },
                            alloc_tgt.tag(),
                            &alloc_tag,
                        );
                        enforce_equal_zero(
                            cs,
                            || format!("{}'s hash is zero", tgt.name()),
                            alloc_tgt.hash(),
                        );
                    }
                }
                LEMOP::MatchTag(match_ptr, cases) => {
                    let Some(alloc_match_ptr) = alloc_ptrs.get(match_ptr.name()) else {
                        bail!("{} not allocated", match_ptr.name());
                    };
                    let mut concrete_path_vec = Vec::new();
                    for (tag, op) in cases {
                        let alloc_has_match = alloc_equal_const(
                            &mut cs.namespace(|| format!("{path}.{tag}.alloc_equal_const")),
                            alloc_match_ptr.tag(),
                            tag.to_field::<F>(),
                        )
                        .with_context(|| "couldn't allocate equal const")?;
                        concrete_path_vec.push(alloc_has_match.clone());

                        let new_path_matchtag = format!("{}.{}", &path, tag);
                        if let PathKind::MaybeConcrete(concrete_path) = path_kind.clone() {
                            let concrete_path_and_has_match = and(
                                &mut cs.namespace(|| format!("{path}.{tag}.and")),
                                &concrete_path,
                                &alloc_has_match,
                            )
                            .with_context(|| "failed to constrain `and`")?;
                            stack.push((
                                op,
                                PathKind::MaybeConcrete(concrete_path_and_has_match),
                                new_path_matchtag,
                                slots.clone(),
                            ));
                        } else {
                            stack.push((
                                op,
                                PathKind::MaybeConcrete(alloc_has_match),
                                new_path_matchtag,
                                slots.clone(),
                            ));
                        }
                    }

                    // Now we need to enforce that at least one path was taken. We do that by constraining
                    // that the sum of the previously collected `Boolean`s is one

                    // If `path_kind` is Some, then we constrain using "concrete implies ..." logic
                    if let PathKind::MaybeConcrete(concrete_path) = path_kind {
                        enforce_selector_with_premise(
                            &mut cs.namespace(|| format!("{path}.enforce_selector_with_premise")),
                            &concrete_path,
                            &concrete_path_vec,
                        )
                        .with_context(|| " couldn't constrain `enforce_selector_with_premise`")?;
                    } else {
                        // If `path_kind` is None, we just do regular constraining
                        enforce_popcount_one(
                            &mut cs.namespace(|| format!("{path}.enforce_popcount_one")),
                            &concrete_path_vec[..],
                        )
                        .with_context(|| "couldn't enforce `popcount_one`")?;
                    }
                }
                LEMOP::Seq(ops) => {
                    // Seqs are the only place were multiple hashes can occur in LEM,
                    // so here we need to count the number of times each type of Hash
                    // is used, and accordingly update the slot indices information.
                    let mut next_slots = slots.clone();
                    stack.extend(ops.iter().rev().map(|op| {
                        match op {
                            LEMOP::Hash2(..) => {
                                next_slots.hash2_idx += 1;
                            }
                            LEMOP::Hash3(..) => {
                                next_slots.hash3_idx += 1;
                            }
                            LEMOP::Hash4(..) => {
                                next_slots.hash4_idx += 1;
                            }
                            _ => (),
                        }
                        (op, path_kind.clone(), path.clone(), next_slots.clone())
                    }));
                    // If the slot indices are larger than a previously found value, we update
                    // the respective max indeces information.
                    hash_slots.hash2_data.max_slots =
                        std::cmp::max(hash_slots.hash2_data.max_slots, next_slots.hash2_idx);
                    hash_slots.hash3_data.max_slots =
                        std::cmp::max(hash_slots.hash3_data.max_slots, next_slots.hash3_idx);
                    hash_slots.hash4_data.max_slots =
                        std::cmp::max(hash_slots.hash4_data.max_slots, next_slots.hash4_idx);
                }
                LEMOP::Return(outputs) => {
                    let is_concrete_path = Self::on_concrete_path(&path_kind)?;
                    for (i, output) in outputs.iter().enumerate() {
                        let Some(alloc_ptr_computed) = alloc_ptrs.get(output.name()) else {
                            bail!("Output {} not allocated", output.name())
                        };
                        let output_name = format!("{}.output[{}]", &path, i);
                        let alloc_ptr_expected = Self::allocate_ptr(
                            cs,
                            &Self::z_ptr_from_valuation(
                                &path_kind,
                                valuation,
                                output.name(),
                                store,
                            )?,
                            &output_name,
                            &alloc_ptrs,
                        )?;

                        if is_concrete_path {
                            Self::inputize_ptr(cs, &alloc_ptr_expected, &output_name)?;
                            num_inputized_outputs += 1;
                        }

                        // If `path_kind` is Some, then we constrain using "concrete implies ..." logic
                        if let PathKind::MaybeConcrete(concrete_path) = path_kind.clone() {
                            alloc_ptr_computed
                                .implies_ptr_equal(
                                    &mut cs.namespace(|| {
                                        format!("enforce imply equal for {output_name}")
                                    }),
                                    &concrete_path,
                                    &alloc_ptr_expected,
                                )
                                .with_context(|| "couldn't constrain `implies_ptr_equal`")?;
                        } else {
                            // If `path_kind` is None, we just do regular constraining
                            alloc_ptr_computed.enforce_equal(
                                &mut cs.namespace(|| format!("enforce equal for {output_name}")),
                                &alloc_ptr_expected,
                            );
                        }
                    }
                }
                _ => todo!(),
            }
        }

        if num_inputized_outputs != 3 {
            return Err(anyhow!("Couldn't inputize the right number of outputs"));
        }

        if let Some(max_slots_indices) = max_slots_allowed {
            if max_slots_indices.hash2_idx > hash_slots.hash2_data.max_slots {
                bail!(
                    "Too many slots allocated for Hash2/Unhash2: {}, {}",
                    max_slots_indices.hash2_idx,
                    hash_slots.hash2_data.max_slots
                );
            }
            if max_slots_indices.hash3_idx > hash_slots.hash3_data.max_slots {
                bail!(
                    "Too many slots allocated for Hash3/Unhash3: {}, {}",
                    max_slots_indices.hash2_idx,
                    hash_slots.hash2_data.max_slots
                );
            }
            if max_slots_indices.hash4_idx > hash_slots.hash4_data.max_slots {
                bail!(
                    "Too many slots allocated for Hash4/Unhash4: {}, {}",
                    max_slots_indices.hash2_idx,
                    hash_slots.hash2_data.max_slots
                );
            }
        }

        let alloc_dummy_ptr = alloc_manager.get_or_alloc_ptr(cs, &ZPtr::dummy())?;

        /////////////////////////////////////////////////////////////////////////
        ///////////////////////////// Hash2 /////////////////////////////////////
        /////////////////////////////////////////////////////////////////////////

        // Create hash constraints for each slot
        {
            let mut concrete_slots_hash2_len = 0;
            let mut hash2_slots = HashMap::default();
            for (slot, alloc_car, alloc_cdr) in hash_slots.hash2_alloc {
                let alloc_hash = hash_poseidon(
                    &mut cs.namespace(|| format!("hash2_{}", slot)),
                    vec![
                        alloc_car.tag().clone(),
                        alloc_car.hash().clone(),
                        alloc_cdr.tag().clone(),
                        alloc_cdr.hash().clone(),
                    ],
                    store.poseidon_cache.constants.c4(),
                )?;
                hash2_slots.insert(slot, alloc_hash);
                concrete_slots_hash2_len += 1;
            }

            // In order to get uniform circuit, we fill empty hash slots with dummy values.
            for s in concrete_slots_hash2_len..hash_slots.hash2_data.max_slots {
                hash2_slots.insert(s + 1, alloc_dummy_ptr.hash().clone());
            }

            Self::create_slot_constraints(
                cs,
                &alloc_ptrs,
                &hash_slots.hash2_data.implies_data,
                &hash_slots.hash2_data.enforce_data,
                &hash2_slots,
                alloc_manager,
            )?;
        }

        /////////////////////////////////////////////////////////////////////////
        ///////////////////////////// Hash3 /////////////////////////////////////
        /////////////////////////////////////////////////////////////////////////

        // Create hash constraints for each slot
        {
            let mut concrete_slots_hash3_len = 0;
            let mut hash3_slots = HashMap::default();
            for (slot, alloc_input1, alloc_input2, alloc_input3) in hash_slots.hash3_alloc {
                let alloc_hash = hash_poseidon(
                    &mut cs.namespace(|| format!("hash3_{}", slot)),
                    vec![
                        alloc_input1.tag().clone(),
                        alloc_input1.hash().clone(),
                        alloc_input2.tag().clone(),
                        alloc_input2.hash().clone(),
                        alloc_input3.tag().clone(),
                        alloc_input3.hash().clone(),
                    ],
                    store.poseidon_cache.constants.c6(),
                )?;
                hash3_slots.insert(slot, alloc_hash);
                concrete_slots_hash3_len += 1;
            }

            // In order to get uniform circuit, we fill empty hash slots with dummy values.
            for s in concrete_slots_hash3_len..hash_slots.hash3_data.max_slots {
                hash3_slots.insert(s + 1, alloc_dummy_ptr.hash().clone());
            }

            Self::create_slot_constraints(
                cs,
                &alloc_ptrs,
                &hash_slots.hash3_data.implies_data,
                &hash_slots.hash3_data.enforce_data,
                &hash3_slots,
                alloc_manager,
            )?;
        }

        /////////////////////////////////////////////////////////////////////////
        ///////////////////////////// Hash4 /////////////////////////////////////
        /////////////////////////////////////////////////////////////////////////

        // Create hash constraints for each slot
        {
            let mut concrete_slots_hash4_len = 0;
            let mut hash4_slots = HashMap::default();
            for (slot, alloc_input1, alloc_input2, alloc_input3, alloc_input4) in hash_slots.hash4_alloc {
                let alloc_hash = hash_poseidon(
                    &mut cs.namespace(|| format!("hash4_{}", slot)),
                    vec![
                        alloc_input1.tag().clone(),
                        alloc_input1.hash().clone(),
                        alloc_input2.tag().clone(),
                        alloc_input2.hash().clone(),
                        alloc_input3.tag().clone(),
                        alloc_input3.hash().clone(),
                        alloc_input4.tag().clone(),
                        alloc_input4.hash().clone(),
                    ],
                    store.poseidon_cache.constants.c8(),
                )?;
                hash4_slots.insert(slot, alloc_hash);
                concrete_slots_hash4_len += 1;
            }

            // In order to get uniform circuit, we fill empty hash slots with dummy values.
            for s in concrete_slots_hash4_len..hash_slots.hash4_data.max_slots {
                hash4_slots.insert(s + 1, alloc_dummy_ptr.hash().clone());
            }

            Self::create_slot_constraints(
                cs,
                &alloc_ptrs,
                &hash_slots.hash4_data.implies_data,
                &hash_slots.hash4_data.enforce_data,
                &hash4_slots,
                alloc_manager,
            )?;
        }

        Ok(())
    }

    #[inline]
    pub fn constrain<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        alloc_manager: &mut AllocationManager<F>,
        store: &mut Store<F>,
        valuation: &Valuation<F>,
    ) -> Result<()> {
        self.constrain_aux(cs, alloc_manager, store, valuation, None)
    }

    #[inline]
    pub fn constrain_limited<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        alloc_manager: &mut AllocationManager<F>,
        store: &mut Store<F>,
        valuation: &Valuation<F>,
        limits: &SlotsIndices,
    ) -> Result<()> {
        self.constrain_aux(cs, alloc_manager, store, valuation, Some(limits))
    }
}
