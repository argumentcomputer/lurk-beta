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
#[derive(Clone)]
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
        input_idx: usize,
    ) -> Result<()> {
        let allocated_ptr = Self::allocate_ptr(
            cs,
            &store.hash_ptr(&frame.input[input_idx])?,
            &self.input[input_idx],
            allocated_ptrs,
        )?;
        allocated_ptrs.insert(&self.input[input_idx], allocated_ptr.clone());
        Self::inputize_ptr(cs, &allocated_ptr, &self.input[input_idx])?;
        Ok(())
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

    /// Use the implies logic to constrain tag and hash values for accumulated
    /// slot data
    fn constrain_slots<F: LurkField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        hash_witness: &Vec<HashWitness>,
        store: &mut Store<F>,
        alloc_manager: &mut AllocationManager<F>,
        allocated_ptrs: &HashMap<&String, AllocatedPtr<F>>,
        num_hash_slots: &NumSlots,
    ) -> Result<()> {
        let virtual_hash = alloc_manager.get_or_alloc_num(cs, F::ZERO)?;

        // We separate slots by arity to constrain them in a fixed order later,
        // to keep the circuit always uniform
        let mut hash2_slots = Vec::with_capacity(num_hash_slots.hash2);
        let mut hash3_slots = Vec::with_capacity(num_hash_slots.hash3);
        let mut hash4_slots = Vec::with_capacity(num_hash_slots.hash4);
        for h in hash_witness {
            match h {
                HashWitness::Hash2(preimg, img) => {
                    hash2_slots.push((preimg, img));
                }
                HashWitness::Hash3(preimg, img) => {
                    hash3_slots.push((preimg, img));
                }
                HashWitness::Hash4(preimg, img) => {
                    hash4_slots.push((preimg, img));
                }
            }
        }

        macro_rules! constrain_slot {
            (
                $concrete_path: expr,
                $hash_index: expr,
                $preimg: expr,
                $img: expr,
                $poseidon_constants: expr
            ) => {
                let allocated_hash = hash_poseidon(
                    &mut cs.namespace(|| format!("slot_hash{}_{}", $preimg.len() / 2, $hash_index)),
                    $preimg.to_vec(),
                    $poseidon_constants,
                )?;

                implies_equal(
                    &mut cs.namespace(|| {
                        format!(
                            "implies equal hash for hash{}_{}",
                            $preimg.len() / 2,
                            $hash_index
                        )
                    }),
                    $concrete_path,
                    $img,
                    &allocated_hash,
                )?;
            };
        }
        macro_rules! constrain_concrete_slots {
            (
                $slots: expr,
                $counter: expr,
                $poseidon_constants: expr
            ) => {
                for (preimg, img) in $slots {
                    // Get preimage from allocated pointers
                    let preimg_vec = Self::get_allocated_preimage(preimg, &allocated_ptrs)?;
                    let preimg: Vec<AllocatedNum<F>> = preimg_vec
                        .iter()
                        .flat_map(|x| [x.tag().clone(), x.hash().clone()])
                        .collect();

                    // get allocated_img from img
                    let Some(allocated_img) = allocated_ptrs.get(img.name()) else {
                                                            bail!("{} not allocated", img.name());
                                                        };

                    constrain_slot!(
                        &Boolean::Constant(true),
                        $counter,
                        preimg,
                        &allocated_img.hash(),
                        $poseidon_constants
                    );
                    $counter += 1;
                }
            };
        }
        macro_rules! constrain_virtual_slots {
            (
                $lower: expr,
                $upper: expr,
                $preimg_size: expr,
                $poseidon_constants: expr
            ) => {
                for slot_index in $lower..$upper {
                    constrain_slot!(
                        &Boolean::Constant(false),
                        slot_index,
                        vec![virtual_hash.clone(); $preimg_size],
                        &virtual_hash,
                        $poseidon_constants
                    );
                }
            };
        }

        let mut hash2_count = 0;
        let mut hash3_count = 0;
        let mut hash4_count = 0;

        // First we constrain the hashes on the concrete path and then the ones
        // in the virtual path in order to always use the same number of hashes.
        constrain_concrete_slots!(
            hash2_slots,
            hash2_count,
            store.poseidon_cache.constants.c4()
        );
        constrain_concrete_slots!(
            hash3_slots,
            hash3_count,
            store.poseidon_cache.constants.c6()
        );
        constrain_concrete_slots!(
            hash4_slots,
            hash4_count,
            store.poseidon_cache.constants.c8()
        );

        ///////////////// Fill with dummies: /////////////////
        constrain_virtual_slots!(
            hash2_count,
            num_hash_slots.hash2,
            4,
            store.poseidon_cache.constants.c4()
        );
        constrain_virtual_slots!(
            hash3_count,
            num_hash_slots.hash3,
            6,
            store.poseidon_cache.constants.c6()
        );
        constrain_virtual_slots!(
            hash4_count,
            num_hash_slots.hash4,
            8,
            store.poseidon_cache.constants.c8()
        );
        Ok(())
    }

    fn alloc_preimage<F: LurkField, CS: ConstraintSystem<F>>(
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

    fn get_allocated_preimage<'a, F: LurkField>(
        preimg: &[MetaPtr],
        allocated_ptrs: &'a HashMap<&String, AllocatedPtr<F>>,
    ) -> Result<Vec<&'a AllocatedPtr<F>>> {
        preimg
            .iter()
            .map(|x| {
                allocated_ptrs
                    .get(x.name())
                    .ok_or_else(|| anyhow!("{} not allocated", x.name()))
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

        // Allocate inputs
        for i in 0..3 {
            self.allocate_and_inputize_input(cs, store, frame, &mut allocated_ptrs, i)?;
        }

        let mut num_inputized_outputs = 0;

        let mut stack = vec![(&self.lem_op, Boolean::Constant(true), Path::default())];

        while let Some((op, concrete_path, path)) = stack.pop() {
            macro_rules! hash_helper {
                ( $img: expr, $tag: expr ) => {
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
                };
            }
            macro_rules! unhash_helper {
                ( $preimg: expr ) => {
                    // STEP 3: Get preimage from allocated pointers
                    let preimg_vec = Self::alloc_preimage(
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
                    hash_helper!(img, tag);
                }
                LEMOP::Hash3(img, tag, _) => {
                    hash_helper!(img, tag);
                }
                LEMOP::Hash4(img, tag, _) => {
                    hash_helper!(img, tag);
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
                        &mut cs.namespace(|| format!("implies equal for {}'s tag", tgt.name())),
                        &concrete_path,
                        allocated_tgt.tag(),
                        &allocated_tag,
                    )
                    .with_context(|| {
                        format!("couldn't enforce implies equal for {}'s tag", tgt.name())
                    })?;

                    // Constrain hash
                    implies_equal_zero(
                        &mut cs
                            .namespace(|| format!("implies equal zero for {}'s hash", tgt.name())),
                        &concrete_path,
                        allocated_tgt.hash(),
                    )
                    .with_context(|| {
                        format!(
                            "couldn't enforce implies equal zero for {}'s hash",
                            tgt.name()
                        )
                    })?;
                }
                LEMOP::MatchTag(match_ptr, cases) => {
                    let Some(allocated_match_ptr) = allocated_ptrs.get(match_ptr.name()) else {
                        bail!("{} not allocated", match_ptr.name());
                    };
                    let mut concrete_path_vec = Vec::new();
                    for (tag, op) in cases {
                        dbg!(tag);
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
                    let is_concrete_path = Self::on_concrete_path(&concrete_path)?;
                    for (i, output) in outputs.iter().enumerate() {
                        let Some(allocated_ptr_computed) = allocated_ptrs.get(output.name()) else {
                            bail!("Output {} not allocated", output.name())
                        };
                        let output_name = format!("{}.output[{}]", &path, i);
                        let allocated_ptr_expected = Self::allocate_ptr(
                            cs,
                            &Self::z_ptr_from_frame(&concrete_path, frame, output, store)?,
                            &output_name,
                            &allocated_ptrs,
                        )?;

                        if is_concrete_path {
                            Self::inputize_ptr(cs, &allocated_ptr_expected, &output_name)?;
                            num_inputized_outputs += 1;
                        }

                        allocated_ptr_computed
                            .implies_ptr_equal(
                                &mut cs
                                    .namespace(|| format!("enforce imply equal for {output_name}")),
                                &concrete_path,
                                &allocated_ptr_expected,
                            )
                            .with_context(|| "couldn't constrain `implies_ptr_equal`")?;
                    }
                }
                _ => todo!(),
            }
        }

        if num_inputized_outputs != 3 {
            bail!("Couldn't inputize the right number of outputs");
        }

        // STEP 3 of hash slots system just finished. In this step we allocated
        // all preimages and images based of information collected during STEP 2.
        // Now that the third traversal of LEM finished we have constrained
        // everything except for hashes and their implications, which we do next.
        Self::constrain_slots(
            cs,
            &frame.hash_witnesses,
            store,
            alloc_manager,
            &allocated_ptrs,
            num_hash_slots,
        )?;

        Ok(())
    }
}
