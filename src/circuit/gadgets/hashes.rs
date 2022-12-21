use bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};

use neptune::circuit2::poseidon_hash_allocated as poseidon_hash;

use crate::circuit::gadgets::pointer::{AllocatedPtr, AsAllocatedHashComponents};

use crate::field::LurkField;
use crate::hash_witness::{ConsName, ConsWitness, ContName, ContWitness, HashName, Stub};
use crate::store::{HashConst, HashConstants, ScalarPointer, ScalarPtr, Store};

pub struct AllocatedPtrHash<F: LurkField> {
    preimage: Vec<AllocatedPtr<F>>,
    digest: AllocatedNum<F>,
}

pub struct AllocatedNumHash<F: LurkField> {
    preimage: Vec<AllocatedNum<F>>,
    digest: AllocatedNum<F>,
}

pub struct AllocatedConsWitness<'a, F: LurkField> {
    #[allow(dead_code)]
    pub(crate) cons_witness: &'a ConsWitness<F>, // Sometimes used for debugging.
    slots: Vec<(Result<ConsName, ()>, AllocatedPtrHash<F>)>,
}

pub struct AllocatedContWitness<'a, F: LurkField> {
    #[allow(dead_code)]
    pub(crate) cont_witness: &'a ContWitness<F>, // Sometimes used for debugging.
    slots: Vec<(Result<ContName, ()>, AllocatedNumHash<F>)>,
}

impl<F: LurkField> AllocatedPtrHash<F> {
    fn alloc<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        constants: &HashConstants<F>,
        preimage: Vec<AllocatedPtr<F>>,
    ) -> Result<Self, SynthesisError> {
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
impl<F: LurkField> AllocatedNumHash<F> {
    fn alloc<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        constants: &HashConstants<F>,
        preimage: Vec<AllocatedNum<F>>,
    ) -> Result<Self, SynthesisError> {
        let constants = constants.constants(preimage.len().into());

        let pr: Vec<AllocatedNum<F>> = preimage.to_vec();

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

impl<'a, F: LurkField> AllocatedConsWitness<'a, F> {
    pub fn from_cons_witness<CS: ConstraintSystem<F>>(
        cs0: &mut CS,
        s: &Store<F>,
        cons_witness: &'a ConsWitness<F>,
    ) -> Result<Self, SynthesisError> {
        let mut slots = Vec::with_capacity(cons_witness.slots.len());
        for (i, (name, p)) in cons_witness.slots.iter().enumerate() {
            let cs = &mut cs0.namespace(|| format!("slot-{}", i));

            let (car_ptr, cdr_ptr, cons_hash) = match p {
                Stub::Dummy => (
                    Some(ScalarPtr::from_parts(F::zero(), F::zero())),
                    Some(ScalarPtr::from_parts(F::zero(), F::zero())),
                    None,
                ),
                Stub::Blank => (None, None, None),
                Stub::Value(hash) => (
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

            let allocated_hash = AllocatedPtrHash::alloc(
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
            cons_witness,
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

impl<'a, F: LurkField> AllocatedContWitness<'a, F> {
    pub fn from_cont_witness<CS: ConstraintSystem<F>>(
        cs0: &mut CS,
        s: &Store<F>,
        cont_witness: &'a ContWitness<F>,
    ) -> Result<Self, SynthesisError> {
        let mut slots = Vec::with_capacity(cont_witness.slots.len());
        for (i, (name, p)) in cont_witness.slots.iter().enumerate() {
            let cs = &mut cs0.namespace(|| format!("slot-{}", i));

            let (cont_ptr, components) = match p {
                Stub::Dummy => (
                    None,
                    Some([
                        F::zero(),
                        F::zero(),
                        F::zero(),
                        F::zero(),
                        F::zero(),
                        F::zero(),
                        F::zero(),
                        F::zero(),
                    ]),
                ),
                Stub::Blank => (None, None),
                Stub::Value(cont) => (
                    Some(cont.cont_ptr),
                    s.get_hash_components_cont(&cont.cont_ptr),
                ),
            };

            let allocated_components = if let Some(components) = components {
                components
                    .iter()
                    .enumerate()
                    .map(|(i, component)| {
                        AllocatedNum::alloc(
                            &mut cs.namespace(|| format!("component_{}", i)),
                            || Ok(*component),
                        )
                        .unwrap()
                    })
                    .collect::<Vec<_>>()
            } else {
                (0..8usize)
                    .map(|i| {
                        AllocatedNum::alloc(
                            &mut cs.namespace(|| format!("component_{}", i)),
                            // This should never be called, because this branch is only taken when stub is blank.
                            || Err(SynthesisError::AssignmentMissing),
                        )
                        .unwrap()
                    })
                    .collect::<Vec<_>>()
            };

            let allocated_hash = AllocatedNumHash::alloc(
                &mut cs.namespace(|| "cont"),
                s.poseidon_constants(),
                allocated_components,
            )?;

            if cont_ptr.is_some() {
                slots.push((Ok(*name), allocated_hash));
            } else {
                slots.push((Err(()), allocated_hash));
            }
        }

        Ok(Self {
            cont_witness,
            slots,
        })
    }

    pub fn get_components(
        &self,
        name: ContName,
        expect_dummy: bool,
    ) -> (&[AllocatedNum<F>], &AllocatedNum<F>) {
        let (allocated_name, allocated_hash) = &self.slots[name.index()];

        if !expect_dummy {
            match allocated_name {
                Err(_) => {
                    dbg!(&self.cont_witness);
                    panic!("requested {:?} but found a dummy allocation", name)
                }
                Ok(alloc_name) => {
                    dbg!(&self.cont_witness);
                    assert_eq!(
                        name, *alloc_name,
                        "requested and allocated names don't match."
                    )
                }
            };
        }
        assert_eq!(8, allocated_hash.preimage.len());
        (&allocated_hash.preimage, &allocated_hash.digest)
    }
}
