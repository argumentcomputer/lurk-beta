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
use crate::lem::SlotsMax;

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

enum HashArity {
    A2,
    A3,
    A4,
}

type SlotsData<F> = Vec<(HashArity, Boolean, Vec<AllocatedNum<F>>, MetaPtr)>;

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
    fn acc_slots_data_data<F: LurkField>(
        concrete_path: Boolean,
        slots_data: &mut SlotsData<F>,
        hash: MetaPtr,
        preimg_vec: Vec<&AllocatedPtr<F>>,
    ) {
        let arity = match preimg_vec.len() {
            2 => HashArity::A2,
            3 => HashArity::A3,
            4 => HashArity::A4,
            _ => unreachable!(),
        };
        let mut input_vec = Vec::new();
        for elem in preimg_vec {
            input_vec.push(elem.tag().clone());
            input_vec.push(elem.hash().clone());
        }
        slots_data.push((arity, concrete_path, input_vec, hash));
    }

    /// Use the implies logic to contrain tag and hash values for accumulated
    /// slot data
    fn create_slot_constraints<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        alloc_ptrs: &HashMap<&String, AllocatedPtr<F>>,
        slots_data: &SlotsData<F>,
        store: &mut Store<F>,
        alloc_manager: &mut AllocationManager<F>,
        num_hash_slots: SlotsMax,
    ) -> Result<()> {
        // Vectors fulls of dummies, so that it will not be required to fill with dummies later
        let alloc_dummy_ptr = alloc_manager.get_or_alloc_ptr(cs, &ZPtr::dummy())?;
        let mut hashes = vec![
            Some(alloc_dummy_ptr.hash().clone());
            num_hash_slots.hash2 + num_hash_slots.hash3 + num_hash_slots.hash4
        ];

        let mut hash2_index = 0;
        let mut hash3_index = num_hash_slots.hash2;
        let mut hash4_index = num_hash_slots.hash3;
        for (arity, concrete_path, input_vec, tgt) in slots_data.iter() {
            let is_concrete_path = Self::on_concrete_path(concrete_path)?;
            if is_concrete_path {
                match arity {
                    HashArity::A2 => {
                        let alloc_hash = hash_poseidon(
                            &mut cs.namespace(|| format!("hash2_{}", hash2_index)),
                            input_vec.to_vec(),
                            store.poseidon_cache.constants.c4(),
                        )?;
                        hashes[hash2_index] = Some(alloc_hash);
                        // get alloc_tgt from tgt
                        let Some(alloc_tgt) = alloc_ptrs.get(tgt.name()) else {
                            bail!("{} not allocated", tgt.name());
                        };
                        // get slot_hash from slot name
                        let Some(ref slot_hash) = hashes[hash2_index] else {
                            bail!("Slot {} not allocated", hash2_index)
                        };
                        implies_equal(
                            &mut cs.namespace(|| {
                                format!("implies equal hash for {} and {}", hash2_index, tgt.name())
                            }),
                            concrete_path,
                            alloc_tgt.hash(),
                            slot_hash,
                        )?;
                        hash2_index += 1;
                    }
                    HashArity::A3 => {
                        let alloc_hash = hash_poseidon(
                            &mut cs.namespace(|| format!("hash3_{}", hash3_index)),
                            input_vec.to_vec(),
                            store.poseidon_cache.constants.c6(),
                        )?;
                        hashes[hash3_index] = Some(alloc_hash);
                        // get alloc_tgt from tgt
                        let Some(alloc_tgt) = alloc_ptrs.get(tgt.name()) else {
                            bail!("{} not allocated", tgt.name());
                        };
                        // get slot_hash from slot name
                        let Some(ref slot_hash) = hashes[hash3_index] else {
                            bail!("Slot {} not allocated", hash3_index)
                        };
                        implies_equal(
                            &mut cs.namespace(|| {
                                format!("implies equal hash for {} and {}", hash3_index, tgt.name())
                            }),
                            concrete_path,
                            alloc_tgt.hash(),
                            slot_hash,
                        )?;
                        hash3_index += 1;
                    }
                    HashArity::A4 => {
                        let alloc_hash = hash_poseidon(
                            &mut cs.namespace(|| format!("hash4_{}", hash4_index)),
                            input_vec.to_vec(),
                            store.poseidon_cache.constants.c8(),
                        )?;
                        hashes[hash4_index] = Some(alloc_hash);
                        // get alloc_tgt from tgt
                        let Some(alloc_tgt) = alloc_ptrs.get(tgt.name()) else {
                            bail!("{} not allocated", tgt.name());
                        };
                        // get slot_hash from slot name
                        let Some(ref slot_hash) = hashes[hash4_index] else {
                            bail!("Slot {} not allocated", hash4_index)
                        };
                        implies_equal(
                            &mut cs.namespace(|| {
                                format!("implies equal hash for {} and {}", hash4_index, tgt.name())
                            }),
                            concrete_path,
                            alloc_tgt.hash(),
                            slot_hash,
                        )?;
                        hash4_index += 1;
                    }
                };
            }
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
        preimg
            .iter()
            .map(|pi| {
                alloc_ptrs
                    .get(pi.name())
                    .ok_or_else(|| anyhow!("{} not allocated", pi.name()))
            })
            .collect::<Result<Vec<_>>>()
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
    pub fn constrain<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        alloc_manager: &mut AllocationManager<F>,
        store: &mut Store<F>,
        valuation: &Valuation<F>,
        num_hash_slots: SlotsMax,
    ) -> Result<()> {
        let mut alloc_ptrs: HashMap<&String, AllocatedPtr<F>> = HashMap::default();

        // Allocate inputs
        for i in 0..3 {
            self.allocate_and_inputize_input(cs, store, valuation, &mut alloc_ptrs, i)?;
        }

        let mut num_inputized_outputs = 0;

        let mut slots_data = SlotsData::default();
        let mut stack = vec![(&self.lem_op, Boolean::Constant(true), String::new())];

        while let Some((op, concrete_path, path)) = stack.pop() {
            macro_rules! acc_hash_data {
                ($hash: expr, $tag: expr, $preimg: expr) => {
                    // Get preimage from allocated pointers
                    let preimg_vec = Self::get_alloc_preimage($preimg, &alloc_ptrs)?;

                    // Allocate new pointer containing expected hash value
                    let alloc_hash = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_valuation(
                            &concrete_path,
                            valuation,
                            $hash.name(),
                            store,
                        )?,
                        $hash.name(),
                        &alloc_ptrs,
                    )?;

                    let alloc_tag = alloc_manager.get_or_alloc_num(cs, $tag.to_field())?;
                    implies_equal(
                        &mut cs.namespace(|| format!("implies equal for {}'s tag", $hash.name())),
                        &concrete_path,
                        alloc_hash.tag(),
                        &alloc_tag,
                    )?;

                    // Accumulate expected hash, wl preimage and tag, together with
                    // path information, such that only concrete path hashes are
                    // indeed calculated in the next available hash slot.
                    Self::acc_slots_data_data(
                        concrete_path.clone(),
                        &mut slots_data,
                        $hash.clone(),
                        preimg_vec,
                    );
                    alloc_ptrs.insert($hash.name(), alloc_hash.clone());
                };
                ($preimg: expr, $hash: expr) => {
                    // Get preimage from allocated pointers
                    let preimg_vec = Self::alloc_preimage(
                        cs,
                        $preimg,
                        &concrete_path,
                        valuation,
                        store,
                        &alloc_ptrs,
                    )?;

                    // Accumulate expected hash, preimage and tag, together with
                    // path information, such that only concrete path hashes are
                    // indeed calculated in the next available hash slot.
                    Self::acc_slots_data_data(
                        concrete_path,
                        &mut slots_data,
                        $hash.clone(),
                        preimg_vec.iter().collect::<Vec<&AllocatedPtr<F>>>(),
                    );

                    // Insert preimage pointers in the HashMap
                    for (name, preimg) in $preimg
                        .iter()
                        .map(|pi| pi.name())
                        .zip(preimg_vec.into_iter())
                    {
                        alloc_ptrs.insert(name, preimg);
                    }
                };
            }

            match op {
                LEMOP::Hash2(hash, tag, preimg) => {
                    acc_hash_data!(hash, tag, preimg);
                }
                LEMOP::Hash3(hash, tag, preimg) => {
                    acc_hash_data!(hash, tag, preimg);
                }
                LEMOP::Hash4(hash, tag, preimg) => {
                    acc_hash_data!(hash, tag, preimg);
                }
                LEMOP::Unhash2(preimg, hash) => {
                    acc_hash_data!(preimg, hash);
                }
                LEMOP::Unhash3(preimg, hash) => {
                    acc_hash_data!(preimg, hash);
                }
                LEMOP::Unhash4(preimg, hash) => {
                    acc_hash_data!(preimg, hash);
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

                        stack.push((op, concrete_path_and_has_match, new_path_matchtag));
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

        Self::create_slot_constraints(
            cs,
            &alloc_ptrs,
            &slots_data,
            store,
            alloc_manager,
            num_hash_slots,
        )?;

        Ok(())
    }
}
