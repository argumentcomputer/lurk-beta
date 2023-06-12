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

use super::{pointers::ZPtr, store::Store, MetaPtr, NumSlots, Valuation, LEM, LEMOP};

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

/// Information needed to constrain each hash slot
struct SlotData<F: LurkField> {
    // Arity of the hash
    arity: HashArity,
    // Variable that indicates if we are in a concrete path or not
    concrete_path: Boolean,
    // Hash preimage
    preimg: Vec<AllocatedNum<F>>,
    // Hash value
    img: AllocatedNum<F>,
    // Allocated pointer name containing the result of the hash
    img_name: String,
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

    /// Accumulates slot data that will be used later to generate the constraints.
    fn acc_slots_data_data<F: LurkField>(
        concrete_path: Boolean,
        slots_data: &mut Vec<SlotData<F>>,
        img: AllocatedNum<F>,
        img_name: String,
        preimg_vec: Vec<&AllocatedPtr<F>>,
    ) {
        let arity = match preimg_vec.len() {
            2 => HashArity::A2,
            3 => HashArity::A3,
            4 => HashArity::A4,
            _ => unreachable!(),
        };
        let mut preimg = Vec::with_capacity(preimg_vec.len() * 2);
        for elem in preimg_vec {
            preimg.push(elem.tag().clone());
            preimg.push(elem.hash().clone());
        }
        slots_data.push(SlotData {
            arity,
            concrete_path,
            preimg,
            img,
            img_name,
        });
    }

    /// Use the implies logic to constrain tag and hash values for accumulated
    /// slot data
    fn create_slot_constraints<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        slots_data: &Vec<SlotData<F>>,
        store: &mut Store<F>,
        alloc_manager: &mut AllocationManager<F>,
        num_hash_slots: &NumSlots,
    ) -> Result<()> {
        // Vector fulls of dummies, so that it will not be required to fill with dummies later
        let alloc_dummy_ptr = alloc_manager.get_or_alloc_ptr(cs, &ZPtr::dummy())?;
        let mut hashes = vec![Some(alloc_dummy_ptr.hash().clone()); num_hash_slots.total()];

        // In order to get a uniform circuit each type of hash has its own constant-size subvector
        // Hash2 uses subvector from 0 to num_hash_slots.hash2
        let mut hash2_index = 0;
        // Hash3 uses subvector from num_hash_slots.hash2 to num_hash_slots.hash3
        let mut hash3_index = num_hash_slots.hash2;
        // Hash4 uses subvector from num_hash_slots.hash3 to num_hash_slots.hash4
        let mut hash4_index = num_hash_slots.hash3;
        for SlotData {
            arity,
            concrete_path,
            preimg,
            img,
            img_name,
        } in slots_data
        {
            macro_rules! constrain_slot {
                ($hash_index: expr, $constants: expr) => {
                    let alloc_hash = hash_poseidon(
                        &mut cs.namespace(|| format!("hash{}", $hash_index)),
                        preimg.to_vec(),
                        $constants,
                    )?;
                    // Replace dummy by allocated hash
                    hashes[$hash_index] = Some(alloc_hash);

                    // get slot_hash from slot name
                    let Some(ref slot_hash) = hashes[$hash_index] else {
                                                bail!("Slot {} not allocated", $hash_index)
                                            };
                    // if on cocnrete path then img must be equal to hash in slot
                    implies_equal(
                        &mut cs.namespace(|| {
                            format!("implies equal hash for {} and {}", $hash_index, img_name)
                        }),
                        concrete_path,
                        img,
                        slot_hash,
                    )?;
                    $hash_index += 1;
                };
            }

            if Self::on_concrete_path(concrete_path)? {
                match arity {
                    HashArity::A2 => {
                        constrain_slot!(hash2_index, store.poseidon_cache.constants.c4());
                    }
                    HashArity::A3 => {
                        constrain_slot!(hash3_index, store.poseidon_cache.constants.c6());
                    }
                    HashArity::A4 => {
                        constrain_slot!(hash4_index, store.poseidon_cache.constants.c8());
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
            .map(|x| {
                Self::z_ptr_from_valuation(concrete_path, valuation, x.name(), store)
                    .and_then(|ref ptr| Self::allocate_ptr(cs, ptr, x.name(), alloc_ptrs))
            })
            .collect::<Result<Vec<_>>>()
    }

    fn get_alloc_preimage<'a, F: LurkField>(
        preimg: &[MetaPtr],
        alloc_ptrs: &'a HashMap<&String, AllocatedPtr<F>>,
    ) -> Result<Vec<&'a AllocatedPtr<F>>> {
        preimg
            .iter()
            .map(|x| {
                alloc_ptrs
                    .get(x.name())
                    .ok_or_else(|| anyhow!("{} not allocated", x.name()))
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
        num_hash_slots: &NumSlots,
    ) -> Result<()> {
        let mut alloc_ptrs: HashMap<&String, AllocatedPtr<F>> = HashMap::default();

        // Allocate inputs
        for i in 0..3 {
            self.allocate_and_inputize_input(cs, store, valuation, &mut alloc_ptrs, i)?;
        }

        let mut num_inputized_outputs = 0;

        let mut slots_data = Vec::default();
        let mut stack = vec![(&self.lem_op, Boolean::Constant(true), String::new())];

        while let Some((op, concrete_path, path)) = stack.pop() {
            macro_rules! acc_hash_data {
                ($img: expr, $tag: expr, $preimg: expr) => {
                    // Get preimage from allocated pointers
                    let preimg_vec = Self::get_alloc_preimage($preimg, &alloc_ptrs)?;

                    // Allocate new pointer containing expected hash value
                    let alloc_img = Self::allocate_ptr(
                        cs,
                        &Self::z_ptr_from_valuation(&concrete_path, valuation, $img.name(), store)?,
                        $img.name(),
                        &alloc_ptrs,
                    )?;

                    let alloc_tag = alloc_manager.get_or_alloc_num(cs, $tag.to_field())?;
                    implies_equal(
                        &mut cs.namespace(|| format!("implies equal for {}'s tag", $img.name())),
                        &concrete_path,
                        alloc_img.tag(),
                        &alloc_tag,
                    )?;

                    // Accumulate expected hash, preimage and tag, together with
                    // path information, such that only concrete path hashes are
                    // indeed calculated in the next available hash slot.
                    Self::acc_slots_data_data(
                        concrete_path.clone(),
                        &mut slots_data,
                        alloc_img.hash().clone(),
                        $img.name().clone(),
                        preimg_vec,
                    );
                    alloc_ptrs.insert($img.name(), alloc_img.clone());
                };
                ($preimg: expr, $img: expr) => {
                    // Get preimage from allocated pointers
                    let preimg_vec = Self::alloc_preimage(
                        cs,
                        $preimg,
                        &concrete_path,
                        valuation,
                        store,
                        &alloc_ptrs,
                    )?;

                    // get alloc_tgt from img
                    let Some(alloc_img) = alloc_ptrs.get($img.name()) else {
                                            bail!("{} not allocated", $img.name());
                                        };

                    // Accumulate expected hash, preimage and tag, together with
                    // path information, such that only concrete path hashes are
                    // indeed calculated in the next available hash slot.
                    Self::acc_slots_data_data(
                        concrete_path,
                        &mut slots_data,
                        alloc_img.hash().clone(),
                        $img.name().clone(),
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
                LEMOP::Hash2(img, tag, preimg) => {
                    acc_hash_data!(img, tag, preimg);
                }
                LEMOP::Hash3(img, tag, preimg) => {
                    acc_hash_data!(img, tag, preimg);
                }
                LEMOP::Hash4(img, tag, preimg) => {
                    acc_hash_data!(img, tag, preimg);
                }
                LEMOP::Unhash2(preimg, img) => {
                    acc_hash_data!(preimg, img);
                }
                LEMOP::Unhash3(preimg, img) => {
                    acc_hash_data!(preimg, img);
                }
                LEMOP::Unhash4(preimg, img) => {
                    acc_hash_data!(preimg, img);
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

        Self::create_slot_constraints(cs, &slots_data, store, alloc_manager, num_hash_slots)?;

        Ok(())
    }
}
