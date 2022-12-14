use bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};

use neptune::circuit2::poseidon_hash_allocated as poseidon_hash;

use crate::circuit::gadgets::pointer::{AllocatedPtr, AsAllocatedHashComponents};

use crate::field::LurkField;
use crate::hash_witness::{ConsName, HashStub, HashWitness, MAX_CONSES_PER_REDUCTION};
use crate::store::{HashConst, HashConstants, ScalarPointer, ScalarPtr, Store};

pub struct AllocatedHash<F: LurkField> {
    preimage: Vec<AllocatedPtr<F>>,
    digest: AllocatedNum<F>,
}

pub struct AllocatedHashWitness<'a, F: LurkField> {
    #[allow(dead_code)]
    pub(crate) hash_witness: &'a HashWitness<F>, // Sometimes used for debugging.
    slots: Vec<(Result<ConsName, ()>, AllocatedHash<F>)>,
}

impl<F: LurkField> AllocatedHash<F> {
    fn alloc<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        constants: &HashConstants<F>,
        preimage: Vec<AllocatedPtr<F>>,
    ) -> Result<AllocatedHash<F>, SynthesisError> {
        let constants = constants.constants((2 * preimage.len()).into());

        let pr: Vec<AllocatedNum<F>> = preimage
            .iter()
            .flat_map(|x| x.as_allocated_hash_components())
            .cloned()
            .collect();

        let digest = constants.hash(cs, pr)?;

        Ok(Self { preimage, digest })
    }
}

impl<'a, F: LurkField> HashConst<'a, F> {
    fn hash<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        preimage: Vec<AllocatedNum<F>>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        match self {
            HashConst::A3(c) => poseidon_hash(cs, preimage, c),
            HashConst::A4(c) => poseidon_hash(cs, preimage, c),
            HashConst::A6(c) => poseidon_hash(cs, preimage, c),
            HashConst::A8(c) => poseidon_hash(cs, preimage, c),
        }
    }
}

impl<'a, F: LurkField> AllocatedHashWitness<'a, F> {
    pub fn from_hash_witness<CS: ConstraintSystem<F>>(
        cs0: &mut CS,
        s: &Store<F>,
        hw: &'a HashWitness<F>,
    ) -> Result<Self, SynthesisError> {
        let mut slots = Vec::with_capacity(MAX_CONSES_PER_REDUCTION);
        // FIXME:
        // Then we need to ensure the correct ordering, and that get_cons called on missing names
        // returns that name's consistent slot hash.
        for (i, (name, p)) in hw.slots.iter().enumerate() {
            let cs = &mut cs0.namespace(|| format!("slot-{}", i));

            let (car_ptr, cdr_ptr, cons_hash) = match p {
                HashStub::Dummy => (
                    Some(ScalarPtr::from_parts(F::zero(), F::zero())),
                    Some(ScalarPtr::from_parts(F::zero(), F::zero())),
                    None,
                ),
                HashStub::Blank => (None, None, None),
                HashStub::Value(hash) => (
                    s.hash_expr(&hash.car),
                    s.hash_expr(&hash.cdr),
                    s.hash_expr(&hash.cons),
                ),
            };

            let allocated_car =
                AllocatedPtr::alloc(&mut cs.namespace(|| "car"), || match car_ptr {
                    Some(p) => Ok(p),
                    None => Err(SynthesisError::AssignmentMissing),
                })?;

            let allocated_cdr =
                AllocatedPtr::alloc(&mut cs.namespace(|| "cdr"), || match cdr_ptr {
                    Some(p) => Ok(p),
                    None => Err(SynthesisError::AssignmentMissing),
                })?;

            let allocated_hash = AllocatedHash::alloc(
                &mut cs.namespace(|| "cons"),
                s.poseidon_constants(),
                vec![allocated_car, allocated_cdr],
            )?;

            if cons_hash.is_some() {
                slots.push((Ok(*name), allocated_hash));
            } else {
                slots.push((Err(()), allocated_hash));
            }
        }

        Ok(Self {
            hash_witness: hw,
            slots,
        })
    }

    pub fn get_cons(
        &self,
        name: ConsName,
        expect_dummy: bool,
    ) -> (&AllocatedPtr<F>, &AllocatedPtr<F>, &AllocatedNum<F>) {
        let (allocated_name, allocated_hash) = &self.slots[name.index()];
        if !expect_dummy {
            match allocated_name {
                Err(_) => panic!("requested {:?} but found a dummy allocation", name),
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
