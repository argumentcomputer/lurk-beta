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
    data::{hash_poseidon},
    pointer::AllocatedPtr,
};

use crate::field::{FWrap, LurkField};

use super::{pointers::ZPtr, store::Store, Witness, LEM, LEMOP, Tag};

/// Manages allocations for numeric variables in a constraint system
#[derive(Default)]
struct AllocationManager<F: LurkField>(HashMap<FWrap<F>, AllocatedNum<F>>);

impl<F: LurkField> AllocationManager<F> {
    /// Checks if the allocation for a numeric variable has already been cached.
    /// If so, return the cached allocation variable. Allocate, cache and return
    /// otherwise.
    pub(crate) fn alloc<CS: ConstraintSystem<F>>(
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
}

impl LEM {
    fn allocate_ptr<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        z_ptr: &ZPtr<F>,
        name: &String,
    ) -> Result<AllocatedPtr<F>> {
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

    fn allocate_and_inputize_input<'a, F: LurkField, CS: ConstraintSystem<F>>(
        &'a self,
        cs: &mut CS,
        store: &mut Store<F>,
        witness: &Witness<F>,
        alloc_ptrs: &mut HashMap<&'a String, AllocatedPtr<F>>,
        idx: usize,
    ) -> Result<()> {
        if alloc_ptrs.contains_key(&self.input[idx]) {
            bail!("{} already allocated", &self.input[idx]);
        }
        let alloc_ptr = Self::allocate_ptr(
            &mut cs.namespace(|| format!("allocate input {}", &self.input[idx])),
            &store.hydrate_ptr(&witness.input[idx])?,
            &self.input[idx],
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

        let mut slots_len = 0;
        let mut hash2_stack = Vec::new();
        let mut hash2_implies_stack = Vec::new();
        let mut hash2_enforce_stack = Vec::new();
        let mut stack = vec![(&self.lem_op, None::<Boolean>, String::new(), 0)];
        while let Some((op, branch_path_info, path, slot)) = stack.pop() {
            match op {
                LEMOP::Hash2Ptrs(tgt, tag, src) => {

                    let alloc_car = alloc_ptrs.get(src[0].name()).expect(format!("{} not allocated", src[0].name()).as_str());
                    let alloc_cdr = alloc_ptrs.get(src[1].name()).expect(format!("{} not allocated", src[1].name()).as_str());

                    if alloc_ptrs.contains_key(tgt.name()) {
                        bail!("{} already allocated", tgt.name());
                    };
                    let z_ptr = {
                        if Self::on_concrete_path(&branch_path_info)? {
                            let Some(ptr) = witness.ptrs.get(tgt.name()) else {
                                bail!("Couldn't retrieve witness {}", tgt.name());
                            };
                            store.hydrate_ptr(ptr)?
                        } else {
                            ZPtr::dummy()
                        }
                    };
                    let alloc_tgt = Self::allocate_ptr(
                        &mut cs.namespace(|| format!("allocate pointer {}", tgt.name())),
                        &z_ptr,
                        tgt.name(),
                    )?;

                    let is_concrete_path = Self::on_concrete_path(&branch_path_info)?;
                    if let Some(concrete_path) = branch_path_info {

                        // if concrete_path is true, push to slots
                        if is_concrete_path {
                            hash2_stack.push((slot, tag, alloc_car.clone(), alloc_cdr.clone())); // only once per path
                        }
                        // concrete path implies alloc_tgt has the same value as in the current slot
                        hash2_implies_stack.push((concrete_path, slot, tgt.clone())); // many
                    } else {
                        hash2_enforce_stack.push((slot, tgt.clone()));
                        hash2_stack.push((slot, tag, alloc_car.clone(), alloc_cdr.clone()))
                    };

                    alloc_ptrs.insert(tgt.name(), alloc_tgt.clone());
                }
                LEMOP::MkNull(tgt, tag) => {
                    if alloc_ptrs.contains_key(tgt.name()) {
                        bail!("{} already allocated", tgt.name());
                    };
                    let z_ptr = {
                        if Self::on_concrete_path(&branch_path_info)? {
                            let Some(ptr) = witness.ptrs.get(tgt.name()) else {
                                bail!("Couldn't retrieve witness {}", tgt.name());
                            };
                            store.hydrate_ptr(ptr)?
                        } else {
                            ZPtr::dummy()
                        }
                    };
                    let alloc_tgt = Self::allocate_ptr(
                        &mut cs.namespace(|| format!("allocate pointer {}", tgt.name())),
                        &z_ptr,
                        tgt.name(),
                    )?;
                    alloc_ptrs.insert(tgt.name(), alloc_tgt.clone());
                    let alloc_tag = alloc_manager.alloc(cs, tag.to_field())?;

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
                            stack.push((op, Some(concrete_path_and_has_match), new_path_matchtag, slot));
                        } else {
                            stack.push((op, Some(alloc_has_match), new_path_matchtag, slot));
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
                    let mut next_slot = slot;
                    stack.extend(
                        ops.iter()
                           .rev()
                           .map(|op| {
                               if matches!(op, LEMOP::Hash2Ptrs(_, _, _)) {
                                   next_slot += 1;
                               };
                               (op, branch_path_info.clone(), path.clone(), next_slot)
                           }),
                    );
                    if next_slot > slots_len {
                        slots_len = next_slot;
                    };
                },
                LEMOP::SetReturn(outputs) => {
                    let is_concrete_path = Self::on_concrete_path(&branch_path_info)?;
                    for (i, output) in outputs.iter().enumerate() {
                        let Some(alloc_ptr_computed) = alloc_ptrs.get(output.name()) else {
                            bail!("Output {} not allocated", output.name())
                        };
                        let z_ptr = {
                            if is_concrete_path {
                                let Some(ptr) = witness.ptrs.get(output.name()) else {
                                    bail!("Output {} not found in the witness", output.name())
                                };
                                store.hydrate_ptr(ptr)?
                            } else {
                                ZPtr::dummy()
                            }
                        };
                        let output_name = format!("{}.output[{}]", &path, i);
                        let alloc_ptr_expected = Self::allocate_ptr(
                            &mut cs.namespace(|| format!("allocate input for {output_name}")),
                            &z_ptr,
                            &output_name,
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

        dbg!(slots_len);

        // Create hash constraints for each stacked slot
        let mut concrete_slots_len = 0;
        let mut hash2_slots: HashMap<usize, AllocatedPtr<F>> = HashMap::default();
        while let Some((slot, tag, alloc_car, alloc_cdr)) = hash2_stack.pop() {
            let alloc_hash = hash_poseidon(
                &mut cs.namespace(|| format!("hash2_{}", slot)),
                vec![alloc_car.tag().clone(), alloc_car.hash().clone(), alloc_cdr.tag().clone(), alloc_cdr.hash().clone()],
                store.poseidon_cache.constants.c4(),
            )?;
            let alloc_tag = alloc_manager.alloc(cs, tag.to_field())?; // TODO: add tags to globals
            let alloc_ptr = AllocatedPtr::from_parts(&alloc_tag, &alloc_hash);
            //let hash2_slot_name = format!("hash2_{}", slot).clone();
            hash2_slots.insert(slot, alloc_ptr);
            concrete_slots_len += 1;
        }

        // TODO: create dummy pointer as global
        let alloc_dummy_hash = AllocatedNum::alloc(cs.namespace(|| "dummy hash"), || Ok(F::ZERO))?;
        // TODO: all tags should be global, then only allocated once
        let alloc_dummy_tag = alloc_manager.alloc(&mut cs.namespace(|| "dummy tag"), Tag::Dummy.to_field())?; // TODO: add tags to globals
        let alloc_dummy_ptr = AllocatedPtr::from_parts(&alloc_dummy_tag, &alloc_dummy_hash); // TODO: use globals

        // complete hash slot with dummies
        for s in concrete_slots_len..slots_len {
            hash2_slots.insert(s+1, alloc_dummy_ptr.clone());
        }

        // Create hash implications
        while let Some((concrete_path, slot, tgt)) = hash2_implies_stack.pop() {

            // get alloc_tgt from tgt
            let alloc_tgt = alloc_ptrs.get(tgt.name()).expect(format!("{} not allocated", tgt.name()).as_str());

            // get slot_hash from slot name
            let Some(slot_hash_ptr) = hash2_slots.get(&slot) else {
                bail!("Slot {} not allocated", slot)
            };

            let slot_hash = slot_hash_ptr.hash();

            implies_equal(
                &mut cs.namespace(|| format!("implies equal hash for {} and {}", slot, tgt.name())),
                &concrete_path,
                alloc_tgt.hash(),
                &slot_hash,
            )?;
        }

        // Create hash enforce
        while let Some((slot, tgt)) = hash2_enforce_stack.pop() {

            // get alloc_tgt from tgt
            let alloc_tgt = alloc_ptrs.get(tgt.name()).expect(format!("{} not allocated", tgt.name()).as_str());

            // get slot_hash from slot name
            let Some(slot_hash_ptr) = hash2_slots.get(&slot) else {
                bail!("Slot {} not allocated", slot)
            };

            let slot_hash = slot_hash_ptr.hash();

            enforce_equal(
                cs,
                || {
                    format!(
                        "enforce equal hash for tgt {} and slot {}",
                        tgt.name(),
                        slot,
                    )
                },
                alloc_tgt.hash(),
                &slot_hash,
            );
        }



        if num_inputized_outputs != 3 {
            return Err(anyhow!("Couldn't inputize the right number of outputs"));
        }
        Ok(())
    }
}
