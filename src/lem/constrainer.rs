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

use super::{pointers::ZPtr, store::Store, MetaPtr, Tag, Witness, LEM, LEMOP};

/// Manages allocations for numeric variables in a constraint system
#[derive(Default)]
struct AllocationManager<F: LurkField>(HashMap<FWrap<F>, AllocatedNum<F>>);

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
struct SlotStacks {
    max_slots_len: usize,
    implies_stack: Vec<(Boolean, usize, MetaPtr, Option<Tag>)>,
    enforce_stack: Vec<(usize, MetaPtr, Option<Tag>)>,
}

#[derive(Default)]
struct HashSlots<F: LurkField> {
    hash2_alloc: Vec<(usize, AllocatedPtr<F>, AllocatedPtr<F>)>,
    hash2_stacks: SlotStacks,
    hash3_alloc: Vec<(usize, AllocatedPtr<F>, AllocatedPtr<F>, AllocatedPtr<F>)>,
    hash3_stacks: SlotStacks,
}

#[derive(Default, Clone)]
struct SlotsIndices {
    hash2_idx: usize,
    hash3_idx: usize,
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

    fn on_concrete_path(concrete_path: &Option<Boolean>) -> Result<bool> {
        match concrete_path {
            None => Ok(true),
            Some(concrete_path) => concrete_path
                .get_value()
                .ok_or_else(|| anyhow!("Couldn't check whether we're on a concrete path")),
        }
    }

    fn z_ptr_from_witness<F: LurkField>(
        branch_path_info: &Option<Boolean>,
        witness: &Witness<F>,
        name: &String,
        store: &mut Store<F>,
    ) -> Result<ZPtr<F>> {
        if Self::on_concrete_path(branch_path_info)? {
            let Some(ptr) = witness.ptrs.get(name) else {
                bail!("Couldn't retrieve {} from witness", name);
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
        witness: &Witness<F>,
        alloc_ptrs: &mut HashMap<&'a String, AllocatedPtr<F>>,
        idx: usize,
    ) -> Result<()> {
        let alloc_ptr = Self::allocate_ptr(
            cs,
            &store.hydrate_ptr(&witness.input[idx])?,
            &self.input[idx],
            alloc_ptrs,
        )?;
        alloc_ptrs.insert(&self.input[idx], alloc_ptr.clone());
        Self::inputize_ptr(cs, &alloc_ptr, &self.input[idx])?;
        Ok(())
    }

    /// Create R1CS constraints for LEM given an evaluation witness.
    ///
    /// As we find recursive (non-leaf) LEM operations, we stack them to be
    /// constrained later, using hash maps to manage viariables and pointers in
    /// a way we can reference allocated variables that were previously created.
    ///
    /// Notably, we use a variable `branch_path_info: Option<Boolean>` to encode
    /// a three-way information:
    ///
    /// * If it's `None`, it means that no logical branches have happened in the
    /// LEM so far, meaning that the evaluation algorithm must have gone through
    /// that operation. In this case, we use regular equality enforcements
    ///
    /// * If it's `Some(concrete_path)`, it means that we're on a logical LEM
    /// branch, which might be *virtual* or *concrete* depending on the witness.
    /// A virtual path is one that wasn't taken during evaluation and thus its
    /// witness pointers and variables weren't bound. A concrete path means that
    /// evaluation took that path and the witness data should be complete. For
    /// virtual paths we need to create dummy bindings and relax the enforcements
    /// with implications whose premises are false. So, in the end, we use
    /// implications on both virtual and concrete paths to make sure that the
    /// circuit structure is always the same, independently of the witness. The
    /// premise is precicely `concrete_path`.
    pub fn constrain<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &mut Store<F>,
        witness: &Witness<F>,
    ) -> Result<()> {
        let mut alloc_ptrs: HashMap<&String, AllocatedPtr<F>> = HashMap::default();

        // Allocate inputs
        for i in 0..3 {
            self.allocate_and_inputize_input(cs, store, witness, &mut alloc_ptrs, i)?;
        }

        let mut num_inputized_outputs = 0;

        let mut alloc_manager = AllocationManager::default();

        let mut hash_slots: HashSlots<F> = Default::default();
        let mut stack = vec![(
            &self.lem_op,
            None::<Boolean>,
            String::new(),
            SlotsIndices::default(),
        )];
        while let Some((op, branch_path_info, path, slots)) = stack.pop() {
            match op {
                LEMOP::Hash2(tgt, tag, src) => {
                    let Some(alloc_car) = alloc_ptrs.get(src[0].name()) else {
                        bail!("{} not allocated", src[0].name());
                    };
                    let Some(alloc_cdr) = alloc_ptrs.get(src[1].name()) else {
                        bail!("{} not allocated", src[1].name());
                    };

                    let alloc_tgt = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_witness(&branch_path_info, witness, tgt.name(), store)?,
                        tgt.name(),
                        &alloc_ptrs,
                    )?;

                    let is_concrete_path = Self::on_concrete_path(&branch_path_info)?;
                    if let Some(concrete_path) = branch_path_info {
                        // if concrete_path is true, push to slots
                        if is_concrete_path {
                            hash_slots.hash2_alloc.push((
                                slots.hash2_idx,
                                alloc_car.clone(),
                                alloc_cdr.clone(),
                            ));
                            // only once per path
                        }
                        // concrete path implies alloc_tgt has the same value as in the current slot
                        hash_slots.hash2_stacks.implies_stack.push((
                            concrete_path,
                            slots.hash2_idx,
                            tgt.clone(),
                            Some(*tag),
                        ));
                    // many
                    } else {
                        hash_slots.hash2_stacks.enforce_stack.push((
                            slots.hash2_idx,
                            tgt.clone(),
                            Some(*tag),
                        ));
                        hash_slots.hash2_alloc.push((
                            slots.hash2_idx,
                            alloc_car.clone(),
                            alloc_cdr.clone(),
                        ))
                    };

                    alloc_ptrs.insert(tgt.name(), alloc_tgt.clone());
                }
                LEMOP::Unhash2(tgt, src) => {
                    let alloc_car = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_witness(
                            &branch_path_info,
                            witness,
                            tgt[0].name(),
                            store,
                        )?,
                        tgt[0].name(),
                        &alloc_ptrs,
                    )?;
                    let alloc_cdr = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_witness(
                            &branch_path_info,
                            witness,
                            tgt[1].name(),
                            store,
                        )?,
                        tgt[1].name(),
                        &alloc_ptrs,
                    )?;

                    let is_concrete_path = Self::on_concrete_path(&branch_path_info)?;
                    if let Some(concrete_path) = branch_path_info {
                        // if concrete_path is true, push to slots
                        if is_concrete_path {
                            hash_slots.hash2_alloc.push((
                                slots.hash2_idx,
                                alloc_car.clone(),
                                alloc_cdr.clone(),
                            ));
                            // only once per path
                        }
                        // concrete path implies alloc_tgt has the same value as in the current slot
                        hash_slots.hash2_stacks.implies_stack.push((
                            concrete_path,
                            slots.hash2_idx,
                            src.clone(),
                            None,
                        ));
                    // many
                    } else {
                        hash_slots.hash2_stacks.enforce_stack.push((
                            slots.hash2_idx,
                            src.clone(),
                            None,
                        ));
                        hash_slots.hash2_alloc.push((
                            slots.hash2_idx,
                            alloc_car.clone(),
                            alloc_cdr.clone(),
                        ))
                    };

                    alloc_ptrs.insert(tgt[0].name(), alloc_car.clone());
                    alloc_ptrs.insert(tgt[1].name(), alloc_cdr.clone());
                }
                LEMOP::Hash3(tgt, tag, src) => {
                    let Some(alloc_input1) = alloc_ptrs.get(src[0].name()) else {
                        bail!("{} not allocated", src[0].name());
                    };
                    let Some(alloc_input2) = alloc_ptrs.get(src[1].name()) else {
                        bail!("{} not allocated", src[1].name());
                    };
                    let Some(alloc_input3) = alloc_ptrs.get(src[2].name()) else {
                        bail!("{} not allocated", src[2].name());
                    };

                    let alloc_tgt = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_witness(&branch_path_info, witness, tgt.name(), store)?,
                        tgt.name(),
                        &alloc_ptrs,
                    )?;

                    let is_concrete_path = Self::on_concrete_path(&branch_path_info)?;
                    if let Some(concrete_path) = branch_path_info {
                        // if concrete_path is true, push to slots
                        if is_concrete_path {
                            hash_slots.hash3_alloc.push((
                                slots.hash3_idx,
                                alloc_input1.clone(),
                                alloc_input2.clone(),
                                alloc_input3.clone(),
                            ));
                            // only once per path
                        }
                        // concrete path implies alloc_tgt has the same value as in the current slot
                        hash_slots.hash3_stacks.implies_stack.push((
                            concrete_path,
                            slots.hash3_idx,
                            tgt.clone(),
                            Some(*tag),
                        ));
                    // many
                    } else {
                        hash_slots.hash3_stacks.enforce_stack.push((
                            slots.hash3_idx,
                            tgt.clone(),
                            Some(*tag),
                        ));
                        hash_slots.hash3_alloc.push((
                            slots.hash3_idx,
                            alloc_input1.clone(),
                            alloc_input2.clone(),
                            alloc_input3.clone(),
                        ))
                    };

                    alloc_ptrs.insert(tgt.name(), alloc_tgt.clone());
                }
                LEMOP::Unhash3(tgt, src) => {
                    let alloc_input1 = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_witness(
                            &branch_path_info,
                            witness,
                            tgt[0].name(),
                            store,
                        )?,
                        tgt[0].name(),
                        &alloc_ptrs,
                    )?;

                    let alloc_input2 = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_witness(
                            &branch_path_info,
                            witness,
                            tgt[1].name(),
                            store,
                        )?,
                        tgt[1].name(),
                        &alloc_ptrs,
                    )?;

                    let alloc_input3 = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_witness(
                            &branch_path_info,
                            witness,
                            tgt[2].name(),
                            store,
                        )?,
                        tgt[2].name(),
                        &alloc_ptrs,
                    )?;

                    let is_concrete_path = Self::on_concrete_path(&branch_path_info)?;
                    if let Some(concrete_path) = branch_path_info {
                        // if concrete_path is true, push to slots
                        if is_concrete_path {
                            hash_slots.hash3_alloc.push((
                                slots.hash3_idx,
                                alloc_input1.clone(),
                                alloc_input2.clone(),
                                alloc_input3.clone(),
                            ));
                            // only once per path
                        }
                        // concrete path implies alloc_tgt has the same value as in the current slot
                        hash_slots.hash3_stacks.implies_stack.push((
                            concrete_path,
                            slots.hash3_idx,
                            src.clone(),
                            None,
                        ));
                    // many
                    } else {
                        hash_slots.hash3_stacks.enforce_stack.push((
                            slots.hash3_idx,
                            src.clone(),
                            None,
                        ));
                        hash_slots.hash3_alloc.push((
                            slots.hash3_idx,
                            alloc_input1.clone(),
                            alloc_input2.clone(),
                            alloc_input3.clone(),
                        ))
                    };

                    alloc_ptrs.insert(tgt[0].name(), alloc_input1.clone());
                    alloc_ptrs.insert(tgt[1].name(), alloc_input2.clone());
                    alloc_ptrs.insert(tgt[2].name(), alloc_input3.clone());
                }

                LEMOP::Null(tgt, tag) => {
                    let alloc_tgt = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_witness(&branch_path_info, witness, tgt.name(), store)?,
                        tgt.name(),
                        &alloc_ptrs,
                    )?;
                    alloc_ptrs.insert(tgt.name(), alloc_tgt.clone());
                    let alloc_tag = alloc_manager.get_or_alloc_num(cs, tag.to_field())?;

                    // If `branch_path_info` is Some, then we constrain using "concrete implies ..." logic
                    if let Some(concrete_path) = branch_path_info {
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
                        // If `branch_path_info` is None, we just do regular constraining
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
                        if let Some(concrete_path) = branch_path_info.clone() {
                            let concrete_path_and_has_match = and(
                                &mut cs.namespace(|| format!("{path}.{tag}.and")),
                                &concrete_path,
                                &alloc_has_match,
                            )
                            .with_context(|| "failed to constrain `and`")?;
                            stack.push((
                                op,
                                Some(concrete_path_and_has_match),
                                new_path_matchtag,
                                slots.clone(),
                            ));
                        } else {
                            stack.push((
                                op,
                                Some(alloc_has_match),
                                new_path_matchtag,
                                slots.clone(),
                            ));
                        }
                    }

                    // Now we need to enforce that at least one path was taken. We do that by constraining
                    // that the sum of the previously collected `Boolean`s is one

                    // If `branch_path_info` is Some, then we constrain using "concrete implies ..." logic
                    if let Some(concrete_path) = branch_path_info {
                        enforce_selector_with_premise(
                            &mut cs.namespace(|| format!("{path}.enforce_selector_with_premise")),
                            &concrete_path,
                            &concrete_path_vec,
                        )
                        .with_context(|| " couldn't constrain `enforce_selector_with_premise`")?;
                    } else {
                        // If `branch_path_info` is None, we just do regular constraining
                        enforce_popcount_one(
                            &mut cs.namespace(|| format!("{path}.enforce_popcount_one")),
                            &concrete_path_vec[..],
                        )
                        .with_context(|| "couldn't enforce `popcount_one`")?;
                    }
                }
                LEMOP::Seq(ops) => {
                    let mut next_slots = slots.clone();
                    stack.extend(ops.iter().rev().map(|op| {
                        match op {
                            LEMOP::Hash2(..) => {
                                next_slots.hash2_idx += 1;
                            }
                            LEMOP::Hash3(..) => {
                                next_slots.hash3_idx += 1;
                            }
                            _ => (),
                        }
                        (
                            op,
                            branch_path_info.clone(),
                            path.clone(),
                            next_slots.clone(),
                        )
                    }));
                    hash_slots.hash2_stacks.max_slots_len =
                        std::cmp::max(hash_slots.hash2_stacks.max_slots_len, next_slots.hash2_idx);
                    hash_slots.hash3_stacks.max_slots_len =
                        std::cmp::max(hash_slots.hash3_stacks.max_slots_len, next_slots.hash3_idx);
                }
                LEMOP::Return(outputs) => {
                    let is_concrete_path = Self::on_concrete_path(&branch_path_info)?;
                    for (i, output) in outputs.iter().enumerate() {
                        let Some(alloc_ptr_computed) = alloc_ptrs.get(output.name()) else {
                            bail!("Output {} not allocated", output.name())
                        };
                        let output_name = format!("{}.output[{}]", &path, i);
                        let alloc_ptr_expected = Self::allocate_ptr(
                            cs,
                            &Self::z_ptr_from_witness(
                                &branch_path_info,
                                witness,
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

                        // If `branch_path_info` is Some, then we constrain using "concrete implies ..." logic
                        if let Some(concrete_path) = branch_path_info.clone() {
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
                            // If `branch_path_info` is None, we just do regular constraining
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

        dbg!(hash_slots.hash2_stacks.max_slots_len);
        dbg!(hash_slots.hash3_stacks.max_slots_len);

        /////////////////////////////////////////////////////////////////////////
        ///////////////////////////// Hash2 /////////////////////////////////////
        /////////////////////////////////////////////////////////////////////////

        // Create hash constraints for each stacked slot
        let mut concrete_slots_hash2_len = 0;
        let mut hash2_slots: HashMap<usize, AllocatedNum<F>> = HashMap::default();
        while let Some((slot, alloc_car, alloc_cdr)) = hash_slots.hash2_alloc.pop() {
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

        let alloc_dummy_ptr = alloc_manager.get_or_alloc_ptr(cs, &ZPtr::dummy())?;

        // complete hash slot with dummies
        for s in concrete_slots_hash2_len..hash_slots.hash2_stacks.max_slots_len {
            hash2_slots.insert(s + 1, alloc_dummy_ptr.hash().clone());
        }

        // Create hash implications
        while let Some((concrete_path, slot, tgt, tag)) =
            hash_slots.hash2_stacks.implies_stack.pop()
        {
            // get alloc_tgt from tgt
            let Some(alloc_tgt) = alloc_ptrs.get(tgt.name()) else {
                bail!("{} not allocated", tgt.name());
            };

            // get slot_hash from slot name
            let Some(slot_hash) = hash2_slots.get(&slot) else {
                bail!("Slot {} not allocated", slot)
            };

            implies_equal(
                &mut cs
                    .namespace(|| format!("implies equal hash2 for {} and {}", slot, tgt.name())),
                &concrete_path,
                alloc_tgt.hash(),
                slot_hash,
            )?;

            if tag.is_some() {
                let alloc_tag = alloc_manager.get_or_alloc_num(cs, tag.unwrap().to_field())?;
                implies_equal(
                    &mut cs.namespace(|| {
                        format!("implies equal tag for {} and {} in hash2", slot, tgt.name())
                    }),
                    &concrete_path,
                    alloc_tgt.tag(),
                    &alloc_tag,
                )?;
            }
        }

        // Create hash enforce
        while let Some((slot, tgt, tag)) = hash_slots.hash2_stacks.enforce_stack.pop() {
            // get alloc_tgt from tgt
            let Some(alloc_tgt) = alloc_ptrs.get(tgt.name()) else {
                bail!("{} not allocated", tgt.name());
            };

            // get slot_hash from slot name
            let Some(slot_hash) = hash2_slots.get(&slot) else {
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
            if tag.is_some() {
                enforce_equal(
                    cs,
                    || {
                        format!(
                            "enforce equal tag for tgt {} and slot number {}",
                            tgt.name(),
                            slot,
                        )
                    },
                    alloc_tgt.hash(),
                    slot_hash,
                );
            }
        }

        /////////////////////////////////////////////////////////////////////////
        ///////////////////////////// Hash3 /////////////////////////////////////
        /////////////////////////////////////////////////////////////////////////

        // Create hash constraints for each stacked slot
        let mut concrete_slots_hash3_len = 0;
        let mut hash3_slots: HashMap<usize, AllocatedNum<F>> = HashMap::default();
        while let Some((slot, alloc_input1, alloc_input2, alloc_input3)) =
            hash_slots.hash3_alloc.pop()
        {
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

        // complete hash slot with dummies
        for s in concrete_slots_hash3_len..hash_slots.hash3_stacks.max_slots_len {
            hash3_slots.insert(s + 1, alloc_dummy_ptr.hash().clone());
        }

        // Create hash implications
        while let Some((concrete_path, slot, tgt, tag)) =
            hash_slots.hash3_stacks.implies_stack.pop()
        {
            // get alloc_tgt from tgt
            let Some(alloc_tgt) = alloc_ptrs.get(tgt.name()) else {
                bail!("{} not allocated", tgt.name());
            };

            // get slot_hash from slot name
            let Some(slot_hash) = hash3_slots.get(&slot) else {
                bail!("Slot {} not allocated", slot)
            };

            implies_equal(
                &mut cs.namespace(|| {
                    format!(
                        "implies equal hash for {} and {} in hash3",
                        slot,
                        tgt.name()
                    )
                }),
                &concrete_path,
                alloc_tgt.hash(),
                slot_hash,
            )?;

            if tag.is_some() {
                let alloc_tag = alloc_manager.get_or_alloc_num(cs, tag.unwrap().to_field())?;
                implies_equal(
                    &mut cs.namespace(|| {
                        format!("implies equal tag for {} and {} in hash3", slot, tgt.name())
                    }),
                    &concrete_path,
                    alloc_tgt.tag(),
                    &alloc_tag,
                )?;
            }
        }

        // Create hash enforce
        while let Some((slot, tgt, tag)) = hash_slots.hash3_stacks.enforce_stack.pop() {
            // get alloc_tgt from tgt
            let Some(alloc_tgt) = alloc_ptrs.get(tgt.name()) else {
                bail!("{} not allocated", tgt.name());
            };

            // get slot_hash from slot name
            let Some(slot_hash) = hash3_slots.get(&slot) else {
                bail!("Slot hash3 number {} not allocated", slot)
            };

            enforce_equal(
                cs,
                || {
                    format!(
                        "enforce equal hash for tgt {} and slot hash3 number {}",
                        tgt.name(),
                        slot,
                    )
                },
                alloc_tgt.hash(),
                slot_hash,
            );
            if tag.is_some() {
                enforce_equal(
                    cs,
                    || {
                        format!(
                            "enforce equal tag for tgt {} and slot hash3 number {}",
                            tgt.name(),
                            slot,
                        )
                    },
                    alloc_tgt.hash(),
                    slot_hash,
                );
            }
        }

        Ok(())
    }
}
