use std::collections::HashMap;

use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    ConstraintSystem,
};

use crate::circuit::gadgets::{
    constraints::{
        alloc_equal_const, and, enforce_equal, enforce_equal_zero, enforce_selector_with_premise,
        implies_equal, implies_equal_zero, popcount_one,
    },
    pointer::AllocatedPtr,
};

use crate::field::{FWrap, LurkField};

use super::{pointers::ZPtr, store::Store, Witness, LEM, LEMOP};

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
    ) -> Result<AllocatedNum<F>, String> {
        let wrap = FWrap(f);
        match self.0.get(&wrap) {
            Some(alloc) => Ok(alloc.to_owned()),
            None => {
                let digits = f.hex_digits();
                let Ok(alloc) = AllocatedNum::alloc(cs.namespace(|| format!("allocate {}", &digits)), || Ok(f)) else {
                    return Err(format!("Couldn't allocate {}", &digits));
                };
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
    ) -> Result<AllocatedPtr<F>, String> {
        let Ok(alloc_tag) = AllocatedNum::alloc(cs.namespace(|| format!("allocate {}'s tag", name)), || 
            Ok(z_ptr.tag.to_field())
        ) else {
            return Err(format!("Couldn't allocate {}'s tag", name))
        };
        let Ok(alloc_hash) = AllocatedNum::alloc(cs.namespace(|| format!("allocate {}'s hash", name)), || 
            Ok(z_ptr.hash)
        ) else {
            return Err(format!("Couldn't allocate {}'s hash", name))
        };
        Ok(AllocatedPtr::from_parts(&alloc_tag, &alloc_hash))
    }

    fn inputize_ptr<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        alloc_ptr: &AllocatedPtr<F>,
        name: &String,
    ) -> Result<(), String> {
        let Ok(_) = alloc_ptr.tag().inputize(cs.namespace(|| format!("inputize {}'s tag", name))) else {
            return Err(format!("Couldn't inputize {}'s tag", name))
        };
        let Ok(_) = alloc_ptr.hash().inputize(cs.namespace(|| format!("inputize {}'s hash", name))) else {
            return Err(format!("Couldn't inputize {}'s hash", name))
        };
        Ok(())
    }

    fn on_concrete_path(concrete_path: &Option<Boolean>) -> Result<bool, String> {
        match concrete_path {
            None => Ok(true),
            Some(concrete_path) => match concrete_path.get_value() {
                Some(b) => Ok(b),
                None => Err("Couldn't check whether we're on a concrete path".to_string()),
            },
        }
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
    ) -> Result<(), String> {
        let mut alloc_ptrs: HashMap<&String, AllocatedPtr<F>> = HashMap::default();

        // TODO: consider creating `initialize` function
        // allocate first input
        {
            let alloc_ptr = Self::allocate_ptr(
                &mut cs.namespace(|| format!("allocate input {}", &self.input[0])),
                &store.hydrate_ptr(&witness.input[0])?,
                &self.input[0],
            )?;
            alloc_ptrs.insert(&self.input[0], alloc_ptr.clone());
            Self::inputize_ptr(cs, &alloc_ptr, &self.input[0])?;
        }

        // allocate second input
        {
            if alloc_ptrs.contains_key(&self.input[1]) {
                return Err(format!("{} already allocated", &self.input[1]));
            }
            let alloc_ptr = Self::allocate_ptr(
                &mut cs.namespace(|| format!("allocate input {}", &self.input[1])),
                &store.hydrate_ptr(&witness.input[1])?,
                &self.input[1],
            )?;
            alloc_ptrs.insert(&self.input[1], alloc_ptr.clone());
            Self::inputize_ptr(cs, &alloc_ptr, &self.input[1])?;
        }

        // allocate third input
        {
            if alloc_ptrs.contains_key(&self.input[2]) {
                return Err(format!("{} already allocated", &self.input[2]));
            }
            let alloc_ptr = Self::allocate_ptr(
                &mut cs.namespace(|| format!("allocate input {}", &self.input[2])),
                &store.hydrate_ptr(&witness.input[2])?,
                &self.input[2],
            )?;
            alloc_ptrs.insert(&self.input[2], alloc_ptr.clone());
            Self::inputize_ptr(cs, &alloc_ptr, &self.input[2])?;
        }

        let mut num_inputized_outputs = 0;

        let mut alloc_manager = AllocationManager::default();

        let mut stack = vec![(&self.lem_op, None::<Boolean>, String::new())];
        while let Some((op, branch_path_info, path)) = stack.pop() {
            match op {
                LEMOP::MkNull(tgt, tag) => {
                    if alloc_ptrs.contains_key(tgt.name()) {
                        return Err(format!("{} already allocated", tgt.name()));
                    };
                    let z_ptr = {
                        if Self::on_concrete_path(&branch_path_info)? {
                            let Some(ptr) = witness.ptrs.get(tgt.name()) else {
                                return Err(format!("Couldn't retrieve witness {}", tgt.name()));
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

                    // If `concrete_path` is Some, then we constrain using "concrete implies ..." logic
                    if let Some(concrete_path) = branch_path_info {
                        let Ok(_) = implies_equal(
                            &mut cs.namespace(|| format!("implies equal for {}'s tag", tgt.name())),
                            &concrete_path,
                            alloc_tgt.tag(),
                            &alloc_tag,
                        ) else {
                            return Err(format!("Couldn't enforce implies equal for {}'s tag", tgt.name()))
                        };
                        let Ok(_) = implies_equal_zero(
                            &mut cs.namespace(|| format!("implies equal zero for {}'s hash (must be zero)", tgt.name())),
                            &concrete_path,
                            alloc_tgt.hash(),
                        ) else {
                            return Err(format!("Couldn't enforce implies equal for {}'s hash", tgt.name()))
                        };
                    } else {
                        // If `concrete_path` is None, we just do regular constraining
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
                        return Err(format!("{} not allocated", match_ptr.name()));
                    };
                    let mut concrete_path_vec = Vec::new();
                    for (tag, op) in cases {
                        let Ok(alloc_has_match) = alloc_equal_const(
                            &mut cs.namespace(
                                || format!("{}.alloc_equal_const (tag:{})", &path, tag)
                            ),
                            alloc_match_ptr.tag(),
                            tag.to_field::<F>(),
                        ) else {
                            return Err("Allocated variable does not have the expected tag".to_string());
                        };
                        concrete_path_vec.push(alloc_has_match.clone());

                        let new_path_matchtag = format!("{}.{}", &path, tag);
                        if let Some(concrete_path) = branch_path_info.clone() {
                            let Ok(concrete_path_and_has_match) = and
                                (
                                    &mut cs.namespace(|| format!("{}.and (tag:{})", &path, tag)),
                                    &concrete_path,
                                    &alloc_has_match
                                ) else {
                                    return Err("Failed to constrain `and`".to_string());
                                };
                            stack.push((op, Some(concrete_path_and_has_match), new_path_matchtag));
                        } else {
                            stack.push((op, Some(alloc_has_match), new_path_matchtag));
                        }
                    }

                    // If `concrete_path` is Some, then we constrain using "concrete implies ..." logic
                    if let Some(concrete_path) = branch_path_info {
                        let Ok(_) = enforce_selector_with_premise(
                            &mut cs.namespace(|| {
                                format!(
                                    "{}.enforce exactly one selected (if concrete, tag: {:?})",
                                    &path,
                                    alloc_match_ptr.tag().get_value()
                                )
                            }),
                            &concrete_path,
                            &concrete_path_vec,
                        ) else {
                            return Err("Failed to enforce selector if concrete".to_string());
                        };
                    } else {
                        // If `concrete_path` is None, we just do regular constraining
                        let Ok(_) = popcount_one(
                            &mut cs.namespace(|| format!("{}.enforce exactly one selected", &path)),
                            &concrete_path_vec[..],
                        ) else {
                            return Err("Failed to enforce selector".to_string())
                        };
                    }
                }
                LEMOP::Seq(ops) => stack.extend(
                    ops.iter()
                        .rev()
                        .map(|op| (op, branch_path_info.clone(), path.clone())),
                ),
                LEMOP::SetReturn(outputs) => {
                    let is_concrete_path = Self::on_concrete_path(&branch_path_info)?;
                    for (i, output) in outputs.iter().enumerate() {
                        let Some(alloc_ptr_computed) = alloc_ptrs.get(output.name()) else {
                            return Err(format!("Output {} not allocated", output.name()))
                        };
                        let z_ptr = {
                            if is_concrete_path {
                                let Some(ptr) = witness.ptrs.get(output.name()) else {
                                    return Err(format!("Output {} not found in the witness", output.name()))
                                };
                                store.hydrate_ptr(ptr)?
                            } else {
                                ZPtr::dummy()
                            }
                        };
                        let output_name = format!("{}.output[{}]", &path, i);
                        let alloc_ptr_expected = Self::allocate_ptr(
                            &mut cs.namespace(|| format!("allocate input for {}", &output_name)),
                            &z_ptr,
                            &output_name,
                        )?;

                        if is_concrete_path {
                            Self::inputize_ptr(cs, &alloc_ptr_expected, &output_name)?;
                            num_inputized_outputs += 1;
                        }

                        // If `concrete_path` is Some, then we constrain using "concrete implies ..." logic
                        if let Some(concrete_path) = branch_path_info.clone() {
                            let Ok(_) = alloc_ptr_computed.implies_ptr_equal(
                                &mut cs.namespace(|| format!("enforce imply equal for {}", &output_name)),
                                &concrete_path,
                                &alloc_ptr_expected,
                            ) else {
                                return Err("Failed to constrain implies_ptr_equal".to_string())
                            };
                        } else {
                            // If `concrete_path` is None, we just do regular constraining
                            alloc_ptr_computed.enforce_equal(
                                &mut cs.namespace(|| format!("enforce equal for {}", &output_name)),
                                &alloc_ptr_expected,
                            );
                        }
                    }
                }
                _ => todo!(),
            }
        }
        if num_inputized_outputs != 3 {
            return Err("Couldn't inputize the right number of outputs".to_string());
        }
        Ok(())
    }
}
