use std::collections::HashMap;
use std::fmt::Debug;

use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};

use neptune::circuit2::poseidon_hash_allocated as poseidon_hash;
use neptune::circuit2_witness::{poseidon_hash_allocated_witness, poseidon_hash_scalar_witness};

use crate::circuit::gadgets::pointer::AllocatedPtr;

use crate::field::{FWrap, LurkField};
use crate::hash::HashConst;
use crate::hash_witness::{ConsName, ContName, Digest, HashName, WitnessBlock};
use crate::ptr::ContPtr;

#[derive(Clone, Debug)]
pub struct AllocatedHash<F: LurkField, PreimageType> {
    preimage: Vec<PreimageType>,
    digest: AllocatedNum<F>,
}

pub(crate) type AllocatedPtrHash<F> = AllocatedHash<F, AllocatedPtr<F>>;
pub(crate) type AllocatedNumHash<F> = AllocatedHash<F, AllocatedNum<F>>;

#[derive(Clone, Debug)]
pub(crate) struct Slot<Name: Debug, AllocatedType> {
    name: Result<Name, ()>,
    allocated: AllocatedType,
    consumed: bool,
}

impl<Name: Debug, F: LurkField, PreimageType> Slot<Name, AllocatedHash<F, PreimageType>> {
    pub(crate) fn is_blank(&self) -> bool {
        self.allocated.digest.get_value().is_none()
    }
    pub(crate) fn is_consumed(&self) -> bool {
        self.consumed
    }
    fn consume(&mut self) {
        self.consumed = true
    }
}

#[derive(Debug)]
pub struct AllocatedWitness<Name: Debug, AllocatedType> {
    #[allow(dead_code)]
    // pub(crate) witness: &'a VanillaWitness, // Sometimes used for debugging.
    slots: Vec<Slot<Name, AllocatedType>>,
}

impl<Name: Debug, F: LurkField, PreimageType>
    AllocatedWitness<Name, AllocatedHash<F, PreimageType>>
{
    pub fn assert_final_invariants(&self) {
        if self.slots[0].is_blank() {
            return;
        }
        let unconsumed = self
            .slots
            .iter()
            .enumerate()
            .filter(|(_, x)| !x.is_consumed())
            .map(|(i, x)| (i, &x.name))
            .collect::<Vec<_>>();
        assert_eq!(
            0,
            unconsumed.len(),
            "some slots were unconsumed: {unconsumed:?}"
        );
    }
}

pub(crate) type AllocatedConsWitness<'a, F> = AllocatedWitness<ConsName, AllocatedPtrHash<F>>;
pub(crate) type AllocatedContWitness<'a, F> = AllocatedWitness<ContName, AllocatedNumHash<F>>;

type HashCircuitWitnessCache<F> = HashMap<Vec<FWrap<F>>, (Vec<F>, F)>;

impl<'a, F: LurkField> HashConst<'a, F> {
    #[allow(dead_code)]
    fn cache_hash_witness<CS: ConstraintSystem<F>>(
        &self,
        cs: &CS,
        preimage: &[F],
        hash_circuit_witness_cache: &mut HashCircuitWitnessCache<F>,
    ) {
        macro_rules! hash {
            ($c:ident) => {{
                assert!(cs.is_witness_generator());
                let key: Vec<FWrap<F>> = preimage.iter().map(|f| FWrap(*f)).collect();

                let _ = hash_circuit_witness_cache
                    .entry(key)
                    .or_insert_with(|| poseidon_hash_scalar_witness(&preimage, $c));
            }};
        }
        match self {
            HashConst::A3(c) => hash!(c),
            HashConst::A4(c) => hash!(c),
            HashConst::A6(c) => hash!(c),
            HashConst::A8(c) => hash!(c),
        }
    }
}

impl<'a, F: LurkField> HashConst<'a, F> {
    pub fn cache_hash_witness_aux(&self, preimage: &[F]) -> (Vec<F>, F) {
        macro_rules! hash {
            ($c:ident) => {{
                poseidon_hash_scalar_witness(&preimage, $c)
            }};
        }
        match self {
            HashConst::A3(c) => hash!(c),
            HashConst::A4(c) => hash!(c),
            HashConst::A6(c) => hash!(c),
            HashConst::A8(c) => hash!(c),
        }
    }
}

impl<'a, F: LurkField> HashConst<'a, F> {
    pub(crate) fn hash<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        preimage: Vec<AllocatedNum<F>>,
        hash_circuit_witness_cache: Option<&mut HashCircuitWitnessCache<F>>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let witness_block = if cs.is_witness_generator() {
            hash_circuit_witness_cache.map(|cache| {
                let key = preimage
                    .iter()
                    .map(|allocated| FWrap(allocated.get_value().unwrap()))
                    .collect::<Vec<_>>();

                let cached = cache.get(&key).unwrap();
                cached
            })
        } else {
            None
        };

        self.hash_with_witness(cs, preimage, witness_block)
    }

    fn hash_with_witness<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        preimage: Vec<AllocatedNum<F>>,
        circuit_witness: Option<&(WitnessBlock<F>, Digest<F>)>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        macro_rules! hash {
            ($c:ident) => {
                if cs.is_witness_generator() {
                    if let Some((aux_buf, res)) = circuit_witness {
                        cs.extend_aux(aux_buf);

                        AllocatedNum::alloc(cs, || Ok(*res))
                    } else {
                        // We have no cache, just allocate the witness.
                        poseidon_hash_allocated_witness(cs, &preimage, $c)
                    }
                } else {
                    // CS is not a witness generator, just hash.
                    poseidon_hash(cs, preimage, $c)
                }
            };
        }
        match self {
            HashConst::A3(c) => hash!(c),
            HashConst::A4(c) => hash!(c),
            HashConst::A6(c) => hash!(c),
            HashConst::A8(c) => hash!(c),
        }
    }
}

impl<'a, F: LurkField> AllocatedConsWitness<'a, F> {
    pub fn get_cons(
        &mut self,
        name: ConsName,
        expect_dummy: bool,
    ) -> (&AllocatedPtr<F>, &AllocatedPtr<F>, &AllocatedNum<F>) {
        let index = name.index();
        self.slots[index].consume();
        let Slot {
            name: allocated_name,
            allocated: allocated_hash,
            consumed: _,
        } = &self.slots[index];
        if !expect_dummy {
            match allocated_name {
                Err(_) => panic!("requested {name:?} but found a dummy allocation"),
                Ok(alloc_name) => assert_eq!(
                    name, *alloc_name,
                    "requested and allocated names don't match."
                ),
            };
        }
        assert_eq!(2, allocated_hash.preimage.len());
        (
            &allocated_hash.preimage[0],
            &allocated_hash.preimage[1],
            &allocated_hash.digest,
        )
    }
}

impl<'a, F: LurkField> AllocatedContWitness<'a, F> {
    // Currently unused, but not necessarily useless.
    #[allow(dead_code)]
    fn make_hash_cache<CS: ConstraintSystem<F>>(
        cs: &CS,
        names_and_ptrs: &[(ContName, (Option<ContPtr<F>>, Option<Vec<F>>))],
        hash_constants: &HashConst<'_, F>,
    ) -> Option<HashCircuitWitnessCache<F>> {
        if cs.is_witness_generator() {
            let mut c = HashMap::new();

            let results = names_and_ptrs
                .iter()
                .map(|(_, (_, p))| {
                    let preimage = p.as_ref().unwrap();
                    (
                        preimage.clone(),
                        hash_constants.cache_hash_witness_aux(preimage),
                    )
                })
                .collect::<Vec<_>>();

            for (preimage, x) in results.iter() {
                let key: Vec<FWrap<F>> = preimage.iter().map(|f| FWrap(*f)).collect();
                c.insert(key, x.clone());
            }
            Some(c)
        } else {
            None
        }
    }

    pub fn get_components(
        &mut self,
        name: ContName,
        expect_dummy: bool,
    ) -> (Vec<AllocatedNum<F>>, AllocatedNum<F>) {
        let index = name.index();
        let Slot {
            name: allocated_name,
            allocated: allocated_hash,
            consumed: _,
        } = self.slots[index].clone();
        if !expect_dummy {
            match allocated_name {
                Err(_) => {
                    panic!("requested {name:?} but found a dummy allocation")
                }
                Ok(alloc_name) => {
                    assert_eq!(
                        name, alloc_name,
                        "requested and allocated names don't match."
                    )
                }
            };
        }
        assert_eq!(8, allocated_hash.preimage.len());
        self.slots[index].consume();

        (allocated_hash.preimage, allocated_hash.digest)
    }

    pub fn get_components_unconstrained(
        &mut self,
        name: ContName,
    ) -> (Vec<AllocatedNum<F>>, AllocatedNum<F>) {
        let index = name.index();
        let Slot {
            name: allocated_name,
            allocated: allocated_hash,
            consumed: _,
        } = self.slots[index].clone();

        // Debugging
        let _names_match = allocated_name
            .map(|alloc_name| alloc_name == name)
            .unwrap_or(false);

        assert_eq!(8, allocated_hash.preimage.len());
        self.slots[index].consume();

        (allocated_hash.preimage, allocated_hash.digest)
    }
}
