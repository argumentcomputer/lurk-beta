use std::collections::HashMap;

use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    ConstraintSystem,
};

use crate::circuit::gadgets::{
    constraints::{
        alloc_equal_const, and, enforce_equal, enforce_selector_with_premise, implies_equal,
        popcount,
    },
    pointer::AllocatedPtr,
};

use crate::field::LurkField;

use super::{pointers::AquaPtr, store::Store, tag::Tag, Witness, LEM, LEMOP};

impl<F: LurkField> LEM<F> {
    fn allocate_ptr<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        aqua_ptr: &AquaPtr<F>,
        name: &String,
    ) -> Result<AllocatedPtr<F>, String> {
        let Ok(alloc_tag) = AllocatedNum::alloc(cs.namespace(|| format!("allocate {}'s tag", name)), || {
            Ok(aqua_ptr.tag.field())
        }) else {
            return Err(format!("Couldn't allocate tag for {}", name))
        };
        let Ok(alloc_val) = AllocatedNum::alloc(cs.namespace(|| format!("allocate {}'s val", name)), || {
            Ok(aqua_ptr.val)
        }) else {
            return Err(format!("Couldn't allocate val for {}", name))
        };
        Ok(AllocatedPtr::from_parts(&alloc_tag, &alloc_val))
    }

    fn inputize_ptr<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        alloc_ptr: &AllocatedPtr<F>,
        name: &String,
    ) -> Result<(), String> {
        let Ok(_) = alloc_ptr.tag().inputize(cs.namespace(|| format!("inputize {}'s tag", name))) else {
            return Err(format!("Couldn't inputize tag for {}", name))
        };
        let Ok(_) = alloc_ptr.hash().inputize(cs.namespace(|| format!("inputize {}'s val", name))) else {
            return Err(format!("Couldn't inputize val for {}", name))
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

    /// TODO: improve
    /// Create R1CS constraints for LEM.
    /// As we find new operations, we stack them to be constrained later.
    /// We use hash maps we manage viariables and pointers.
    /// This way we can reference allocated variables that were
    /// created previously.
    /// We have real paths and virtual paths.
    /// Then we can constrain LEM using implications.
    pub fn constrain<CS: ConstraintSystem<F>>(
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
                &mut cs.namespace(|| format!("allocate input {}", self.input[0])),
                &store.hydrate_ptr(&witness.input[0])?,
                &self.input[0],
            )?;
            alloc_ptrs.insert(&self.input[0], alloc_ptr.clone());
            Self::inputize_ptr(cs, &alloc_ptr, &self.input[0])?;
        }

        // allocate second input
        {
            if alloc_ptrs.contains_key(&self.input[1]) {
                return Err(format!("{} already allocated", self.input[1]));
            }
            let alloc_ptr = Self::allocate_ptr(
                &mut cs.namespace(|| format!("allocate input {}", self.input[1])),
                &store.hydrate_ptr(&witness.input[1])?,
                &self.input[1],
            )?;
            alloc_ptrs.insert(&self.input[1], alloc_ptr.clone());
            Self::inputize_ptr(cs, &alloc_ptr, &self.input[1])?;
        }

        // allocate third input
        {
            if alloc_ptrs.contains_key(&self.input[2]) {
                return Err(format!("{} already allocated", self.input[2]));
            }
            let alloc_ptr = Self::allocate_ptr(
                &mut cs.namespace(|| format!("allocate input {}", self.input[2])),
                &store.hydrate_ptr(&witness.input[2])?,
                &self.input[2],
            )?;
            alloc_ptrs.insert(&self.input[2], alloc_ptr.clone());
            Self::inputize_ptr(cs, &alloc_ptr, &self.input[2])?;
        }

        let mut num_inputized_outputs = 0;

        // TODO: consider greating globals
        let zero = AllocatedNum::alloc(cs.namespace(|| "#zero"), || Ok(F::zero())).unwrap();
        let one = AllocatedNum::alloc(cs.namespace(|| "#one"), || Ok(F::one())).unwrap();
        let mut alloc_tags: HashMap<&Tag, AllocatedNum<F>> = HashMap::default();
        let mut stack = vec![(&self.lem_op, None::<Boolean>, String::new())];
        while let Some((op, concrete_path, path)) = stack.pop() {
            match op {
                LEMOP::MkNull(tgt, tag) => {
                    if alloc_ptrs.contains_key(tgt.name()) {
                        return Err(format!("{} already allocated", tgt.name()));
                    };
                    let aqua_ptr = {
                        if Self::on_concrete_path(&concrete_path)? {
                            let Some(ptr) = witness.ptrs.get(tgt.name()) else {
                                return Err(format!("Couldn't retrieve witness {}", tgt.name()));
                            };
                            store.hydrate_ptr(ptr)?
                        } else {
                            AquaPtr::dummy()
                        }
                    };
                    let alloc_tgt = Self::allocate_ptr(
                        &mut cs.namespace(|| format!("allocate pointer {}", tgt.name())),
                        &aqua_ptr,
                        tgt.name(),
                    )?;
                    alloc_ptrs.insert(tgt.name(), alloc_tgt.clone());
                    let alloc_tag = {
                        match alloc_tags.get(tag) {
                            Some(alloc_tag) => alloc_tag.clone(),
                            None => {
                                let Ok(alloc_tag) = AllocatedNum::alloc(
                                    cs.namespace(|| format!("Tag {:?}", tag)),
                                    || Ok(tag.field()),
                                ) else {
                                    return Err(format!("Couldn't allocate tag for {}", tgt.name()));
                                };
                                alloc_tags.insert(tag, alloc_tag.clone());
                                alloc_tag
                            }
                        }
                    };

                    // If `concrete_path` is Some, then we constrain using "concrete implies ..." logic
                    if let Some(concrete_path) = concrete_path {
                        let Ok(_) = implies_equal(
                            &mut cs.namespace(|| format!("implies equal for {}'s tag", tgt.name())),
                            &concrete_path,
                            alloc_tgt.tag(),
                            &alloc_tag,
                        ) else {
                            return Err("TODO".to_string())
                        };
                        let Ok(_) = implies_equal(
                            &mut cs.namespace(|| format!("implies equal for {}'s val (must be zero)", tgt.name())),
                            &concrete_path,
                            alloc_tgt.hash(),
                            &zero,
                        ) else {
                            return Err("TODO".to_string())
                        };
                    } else {
                        // If `concrete_path` is None, we just do regular constraining
                        enforce_equal(
                            cs,
                            || format!("{}'s tag is {}", tgt.name(), tag.field::<F>().hex_digits()),
                            &alloc_tgt.tag(),
                            &alloc_tag,
                        );
                        enforce_equal(
                            cs,
                            || format!("{}'s val is zero", tgt.name()),
                            &alloc_tgt.hash(),
                            &zero,
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
                            tag.field::<F>(),
                        ) else {
                            return Err("Allocated variable does not have the expected tag".to_string());
                        };
                        concrete_path_vec.push(alloc_has_match.clone());

                        let new_path_matchtag = format!("{}.{}", &path, tag);
                        if let Some(concrete_path) = concrete_path.clone() {
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
                    if let Some(concrete_path) = concrete_path {
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
                        let Ok(_) = popcount(
                            &mut cs.namespace(|| format!("{}.enforce exactly one selected", &path)),
                            &concrete_path_vec[..],
                            &one,
                        ) else {
                            return Err("Failed to enforce selector".to_string())
                        };
                    }
                }
                LEMOP::Seq(ops) => stack.extend(
                    ops.iter()
                        .rev()
                        .map(|op| (op, concrete_path.clone(), path.clone())),
                ),
                LEMOP::SetReturn(outputs) => {
                    let is_concrete_path = Self::on_concrete_path(&concrete_path)?;
                    for (i, output) in outputs.iter().enumerate() {
                        let Some(alloc_ptr_computed) = alloc_ptrs.get(output.name()) else {
                            return Err(format!("Output {} not allocated", output.name()))
                        };
                        let aqua_ptr = {
                            if is_concrete_path {
                                let Some(ptr) = witness.ptrs.get(output.name()) else {
                                    return Err(format!("Output {} not found in the witness", output.name()))
                                };
                                store.hydrate_ptr(ptr)?
                            } else {
                                AquaPtr::dummy()
                            }
                        };
                        let output_name = format!("{}.output[{}]", &path, i);
                        let alloc_ptr_expected = Self::allocate_ptr(
                            &mut cs.namespace(|| format!("allocate input for {}", &output_name)),
                            &aqua_ptr,
                            &output_name,
                        )?;

                        if is_concrete_path {
                            Self::inputize_ptr(cs, &alloc_ptr_expected, &output_name)?;
                            num_inputized_outputs += 1;
                        }

                        // If `concrete_path` is Some, then we constrain using "concrete implies ..." logic
                        if let Some(concrete_path) = concrete_path.clone() {
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
