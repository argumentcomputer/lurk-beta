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

use super::{pointers::ZPtr, store::Store, MetaPtr, Valuation, LEM, LEMOP};

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
struct SlotData<F: LurkField> {
    max_slots: usize,
    constraints_data: Vec<(Boolean, usize, Vec<AllocatedNum<F>>, MetaPtr)>,
}

#[derive(Default)]
struct HashSlots<F: LurkField> {
    hash2_data: SlotData<F>,
    hash3_data: SlotData<F>,
    hash4_data: SlotData<F>,
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

    fn on_concrete_path(concrete_path: &Boolean) -> Result<bool> {
        concrete_path
            .get_value()
            .ok_or_else(|| anyhow!("Couldn't check whether we're on a concrete path"))
    }

    fn z_ptr_from_valuation<F: LurkField>(
        concrete_path: &Boolean,
        valuation: &Valuation<F>,
        name: &String,
        store: &mut Store<F>,
    ) -> Result<ZPtr<F>> {
        if Self::on_concrete_path(concrete_path)? {
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
    fn acc_hash_slots_data<F: LurkField>(
        concrete_path: Boolean,
        hash_slots: &mut HashSlots<F>,
        slots: &SlotsIndices,
        hash: MetaPtr,
        alloc_arity: AllocHashPreimage<F>,
    ) -> Result<()> {
        match alloc_arity {
            AllocHashPreimage::A2(i0, i1) => {
                let input_vec = vec![
                    i0.tag().clone(),
                    i0.hash().clone(),
                    i1.tag().clone(),
                    i1.hash().clone(),
                ];
                hash_slots.hash2_data.constraints_data.push((
                    concrete_path,
                    slots.hash2_idx,
                    input_vec,
                    hash,
                ));
            }
            AllocHashPreimage::A3(i0, i1, i2) => {
                let input_vec = vec![
                    i0.tag().clone(),
                    i0.hash().clone(),
                    i1.tag().clone(),
                    i1.hash().clone(),
                    i2.tag().clone(),
                    i2.hash().clone(),
                ];
                hash_slots.hash3_data.constraints_data.push((
                    concrete_path,
                    slots.hash3_idx,
                    input_vec,
                    hash,
                ));
            }
            AllocHashPreimage::A4(i0, i1, i2, i3) => {
                let input_vec = vec![
                    i0.tag().clone(),
                    i0.hash().clone(),
                    i1.tag().clone(),
                    i1.hash().clone(),
                    i2.tag().clone(),
                    i2.hash().clone(),
                    i3.tag().clone(),
                    i3.hash().clone(),
                ];
                hash_slots.hash4_data.constraints_data.push((
                    concrete_path,
                    slots.hash4_idx,
                    input_vec,
                    hash,
                ));
            }
        }
        Ok(())
    }

    /// Use the implies logic to contrain tag and hash values for accumulated
    /// slot data
    fn create_slot_constraints<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        alloc_ptrs: &HashMap<&String, AllocatedPtr<F>>,
        hash_slots: HashSlots<F>,
        store: &mut Store<F>,
        alloc_manager: &mut AllocationManager<F>,
    ) -> Result<()> {
        // Vectors fulls of dummies, so that it will not be required to fill with dummies later
        let alloc_dummy_ptr = alloc_manager.get_or_alloc_ptr(cs, &ZPtr::dummy())?;
        let mut hash2_slots =
            vec![Some(alloc_dummy_ptr.hash().clone()); hash_slots.hash2_data.max_slots + 1];
        let mut hash3_slots =
            vec![Some(alloc_dummy_ptr.hash().clone()); hash_slots.hash3_data.max_slots + 1];
        let mut hash4_slots =
            vec![Some(alloc_dummy_ptr.hash().clone()); hash_slots.hash4_data.max_slots + 1];

        for (concrete_path, slot, input_vec, tgt) in hash_slots.hash2_data.constraints_data {
            let is_concrete_path = Self::on_concrete_path(&concrete_path)?;
            if is_concrete_path {
                let alloc_hash = hash_poseidon(
                    &mut cs.namespace(|| format!("hash3_{}", slot)),
                    input_vec.to_vec(),
                    store.poseidon_cache.constants.c4(),
                )?;
                hash2_slots[slot] = Some(alloc_hash);
            }

            // get alloc_tgt from tgt
            let Some(alloc_tgt) = alloc_ptrs.get(tgt.name()) else {
                bail!("{} not allocated", tgt.name());
            };

            // get slot_hash from slot name
            let Some(ref slot_hash) = hash2_slots[slot] else {
                bail!("Slot {} not allocated", slot)
            };

            implies_equal(
                &mut cs
                    .namespace(|| format!("implies equal hash2 for {} and {}", slot, tgt.name())),
                &concrete_path,
                alloc_tgt.hash(),
                slot_hash,
            )?;
        }
        for (concrete_path, slot, input_vec, tgt) in hash_slots.hash3_data.constraints_data {
            let is_concrete_path = Self::on_concrete_path(&concrete_path)?;
            if is_concrete_path {
                let alloc_hash = hash_poseidon(
                    &mut cs.namespace(|| format!("hash3_{}", slot)),
                    input_vec.to_vec(),
                    store.poseidon_cache.constants.c6(),
                )?;
                hash3_slots[slot] = Some(alloc_hash);
            }
            // get alloc_tgt from tgt
            let Some(alloc_tgt) = alloc_ptrs.get(tgt.name()) else {
                bail!("{} not allocated", tgt.name());
            };

            // get slot_hash from slot name
            let Some(ref slot_hash) = hash3_slots[slot] else {
                bail!("Slot {} not allocated", slot)
            };

            implies_equal(
                &mut cs
                    .namespace(|| format!("implies equal hash2 for {} and {}", slot, tgt.name())),
                &concrete_path,
                alloc_tgt.hash(),
                slot_hash,
            )?;
        }
        for (concrete_path, slot, input_vec, tgt) in hash_slots.hash4_data.constraints_data {
            let is_concrete_path = Self::on_concrete_path(&concrete_path)?;
            if is_concrete_path {
                let alloc_hash = hash_poseidon(
                    &mut cs.namespace(|| format!("hash4_{}", slot)),
                    input_vec.to_vec(),
                    store.poseidon_cache.constants.c8(),
                )?;
                hash4_slots[slot] = Some(alloc_hash);
            }
            // get alloc_tgt from tgt
            let Some(alloc_tgt) = alloc_ptrs.get(tgt.name()) else {
                bail!("{} not allocated", tgt.name());
            };

            // get slot_hash from slot name
            let Some(ref slot_hash) = hash4_slots[slot] else {
                bail!("Slot {} not allocated", slot)
            };

            implies_equal(
                &mut cs
                    .namespace(|| format!("implies equal hash2 for {} and {}", slot, tgt.name())),
                &concrete_path,
                alloc_tgt.hash(),
                slot_hash,
            )?;
        }
        Ok(())
    }

    fn alloc_preimage<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        preimg: &[MetaPtr],
        concrete_path: &Boolean,
        valuation: &Valuation<F>,
        store: &mut Store<F>,
        alloc_ptrs: &HashMap<&String, AllocatedPtr<F>>,
    ) -> Result<Vec<AllocatedPtr<F>>> {
        preimg
            .iter()
            .map(|pre| {
                let name = pre.name();
                let res_ptr = Self::z_ptr_from_valuation(concrete_path, valuation, name, store);
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
    /// Notably, we use a variable `concrete_path: Boolean` to encode whether we
    /// are on a *concrete* or *virtual* path. A virtual path is one that wasn't
    /// taken during evaluation and thus its valuation pointers weren't bound. A
    /// concrete path means that evaluation took that path and the valuation data
    /// should be complete. For virtual paths we need to create dummy bindings
    /// and relax the implications with false premises. The premise is precicely
    /// `concrete_path`.
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
            Boolean::Constant(true),
            String::new(),
            SlotsIndices::default(),
        )];
        while let Some((op, concrete_path, path, slots)) = stack.pop() {
            match op {
                LEMOP::Hash2(hash, tag, preimg) => {
                    // Get preimage from allocated pointers
                    let preimg_vec = Self::get_alloc_preimage(preimg, &alloc_ptrs)?;

                    // Allocate new pointer containing expected hash value
                    let alloc_hash = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_valuation(&concrete_path, valuation, hash.name(), store)?,
                        hash.name(),
                        &alloc_ptrs,
                    )?;

                    let alloc_tag = alloc_manager.get_or_alloc_num(cs, tag.to_field())?;
                    implies_equal(
                        &mut cs.namespace(|| format!("implies equal for {}'s tag", hash.name())),
                        &concrete_path,
                        alloc_hash.tag(),
                        &alloc_tag,
                    )?;

                    // Accumulate expected hash, preimage and tag, together with
                    // path information, such that only concrete path hashes are
                    // indeed calculated in the next available hash slot.
                    Self::acc_hash_slots_data(
                        concrete_path,
                        &mut hash_slots,
                        &slots,
                        hash.clone(),
                        AllocHashPreimage::A2(preimg_vec[0].clone(), preimg_vec[1].clone()),
                    )?;

                    // Insert hash value pointer in the HashMap
                    alloc_ptrs.insert(hash.name(), alloc_hash.clone());
                }
                LEMOP::Unhash2(preimg, hash) => {
                    // Get preimage from allocated pointers
                    let preimg_vec = Self::alloc_preimage(
                        cs,
                        preimg,
                        &concrete_path,
                        valuation,
                        store,
                        &alloc_ptrs,
                    )?;

                    // Accumulate expected hash, preimage and tag, together with
                    // path information, such that only concrete path hashes are
                    // indeed calculated in the next available hash slot.
                    Self::acc_hash_slots_data(
                        concrete_path,
                        &mut hash_slots,
                        &slots,
                        hash.clone(),
                        AllocHashPreimage::A2(preimg_vec[0].clone(), preimg_vec[1].clone()),
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
                        &Self::z_ptr_from_valuation(&concrete_path, valuation, hash.name(), store)?,
                        hash.name(),
                        &alloc_ptrs,
                    )?;

                    let alloc_tag = alloc_manager.get_or_alloc_num(cs, tag.to_field())?;
                    implies_equal(
                        &mut cs.namespace(|| format!("implies equal for {}'s tag", hash.name())),
                        &concrete_path,
                        alloc_hash.tag(),
                        &alloc_tag,
                    )?;

                    // Accumulate expected hash, preimage and tag, together with
                    // path information, such that only concrete path hashes are
                    // indeed calculated in the next available hash slot.
                    Self::acc_hash_slots_data(
                        concrete_path,
                        &mut hash_slots,
                        &slots,
                        hash.clone(),
                        AllocHashPreimage::A3(
                            preimg_vec[0].clone(),
                            preimg_vec[1].clone(),
                            preimg_vec[2].clone(),
                        ),
                    )?;

                    // Insert hash value pointer in the HashMap
                    alloc_ptrs.insert(hash.name(), alloc_hash.clone());
                }
                LEMOP::Unhash3(preimg, hash) => {
                    // Get preimage from allocated pointers
                    let preimg_vec = Self::alloc_preimage(
                        cs,
                        preimg,
                        &concrete_path,
                        valuation,
                        store,
                        &alloc_ptrs,
                    )?;

                    // Accumulate expected hash, preimage and tag, together with
                    // path information, such that only concrete path hashes are
                    // indeed calculated in the next available hash slot.
                    Self::acc_hash_slots_data(
                        concrete_path,
                        &mut hash_slots,
                        &slots,
                        hash.clone(),
                        AllocHashPreimage::A3(
                            preimg_vec[0].clone(),
                            preimg_vec[1].clone(),
                            preimg_vec[2].clone(),
                        ),
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
                        &Self::z_ptr_from_valuation(&concrete_path, valuation, hash.name(), store)?,
                        hash.name(),
                        &alloc_ptrs,
                    )?;

                    let alloc_tag = alloc_manager.get_or_alloc_num(cs, tag.to_field())?;
                    implies_equal(
                        &mut cs.namespace(|| format!("implies equal for {}'s tag", hash.name())),
                        &concrete_path,
                        alloc_hash.tag(),
                        &alloc_tag,
                    )?;

                    // Accumulate expected hash, preimage and tag, together with
                    // path information, such that only concrete path hashes are
                    // indeed calculated in the next available hash slot.
                    Self::acc_hash_slots_data(
                        concrete_path,
                        &mut hash_slots,
                        &slots,
                        hash.clone(),
                        AllocHashPreimage::A4(
                            preimg_vec[0].clone(),
                            preimg_vec[1].clone(),
                            preimg_vec[2].clone(),
                            preimg_vec[3].clone(),
                        ),
                    )?;

                    // Insert hash value pointer in the HashMap
                    alloc_ptrs.insert(hash.name(), alloc_hash.clone());
                }
                LEMOP::Unhash4(preimg, hash) => {
                    // Get preimage from allocated pointers
                    let preimg_vec = Self::alloc_preimage(
                        cs,
                        preimg,
                        &concrete_path,
                        valuation,
                        store,
                        &alloc_ptrs,
                    )?;

                    // Accumulate expected hash, preimage and tag, together with
                    // path information, such that only concrete path hashes are
                    // indeed calculated in the next available hash slot.
                    Self::acc_hash_slots_data(
                        concrete_path,
                        &mut hash_slots,
                        &slots,
                        hash.clone(),
                        AllocHashPreimage::A4(
                            preimg_vec[0].clone(),
                            preimg_vec[1].clone(),
                            preimg_vec[2].clone(),
                            preimg_vec[3].clone(),
                        ),
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
                        &Self::z_ptr_from_valuation(&concrete_path, valuation, tgt.name(), store)?,
                        tgt.name(),
                        &alloc_ptrs,
                    )?;
                    alloc_ptrs.insert(tgt.name(), alloc_tgt.clone());
                    let alloc_tag = alloc_manager.get_or_alloc_num(cs, tag.to_field())?;

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
                        &mut cs
                            .namespace(|| format!("implies equal zero for {}'s hash", tgt.name())),
                        &concrete_path,
                        alloc_tgt.hash(),
                    )
                    .with_context(|| {
                        format!(
                            "couldn't enforce implies equal zero for {}'s hash",
                            tgt.name()
                        )
                    })?;
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
                        let concrete_path_and_has_match = and(
                            &mut cs.namespace(|| format!("{path}.{tag}.and")),
                            &concrete_path,
                            &alloc_has_match,
                        )
                        .with_context(|| "failed to constrain `and`")?;

                        stack.push((
                            op,
                            concrete_path_and_has_match,
                            new_path_matchtag,
                            slots.clone(),
                        ));
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
                    // Seqs are the only place were multiple hashes can occur in LEM,
                    // so here we need to count the number of times each type of Hash
                    // is used, and accordingly update the slot indices information.
                    let mut next_slots = slots;
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
                        (op, concrete_path.clone(), path.clone(), next_slots.clone())
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
                    let is_concrete_path = Self::on_concrete_path(&concrete_path)?;
                    for (i, output) in outputs.iter().enumerate() {
                        let Some(alloc_ptr_computed) = alloc_ptrs.get(output.name()) else {
                            bail!("Output {} not allocated", output.name())
                        };
                        let output_name = format!("{}.output[{}]", &path, i);
                        let alloc_ptr_expected = Self::allocate_ptr(
                            cs,
                            &Self::z_ptr_from_valuation(
                                &concrete_path,
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

                        alloc_ptr_computed
                            .implies_ptr_equal(
                                &mut cs
                                    .namespace(|| format!("enforce imply equal for {output_name}")),
                                &concrete_path,
                                &alloc_ptr_expected,
                            )
                            .with_context(|| "couldn't constrain `implies_ptr_equal`")?;
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

        Self::create_slot_constraints(cs, &alloc_ptrs, hash_slots, store, alloc_manager)?;

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
