use std::fmt::Debug;

use bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};

use neptune::circuit2::poseidon_hash_allocated as poseidon_hash;

use crate::circuit::gadgets::pointer::{AllocatedPtr, AsAllocatedHashComponents};

use crate::field::LurkField;
use crate::hash_witness::{ConsName, ConsWitness, ContName, ContWitness, HashName, Stub};
use crate::store::{HashConst, HashConstants, ScalarPtr, Store};
use crate::tag::ExprTag;

#[derive(Clone)]
pub struct AllocatedHash<F: LurkField, PreimageType> {
    preimage: Vec<PreimageType>,
    digest: AllocatedNum<F>,
}

pub type AllocatedPtrHash<F> = AllocatedHash<F, AllocatedPtr<F>>;
pub type AllocatedNumHash<F> = AllocatedHash<F, AllocatedNum<F>>;

#[derive(Clone, Debug)]
pub struct Slot<Name: Debug, AllocatedType> {
    name: Result<Name, ()>,
    allocated: AllocatedType,
    consumed: bool,
}

impl<Name: Debug, F: LurkField, PreimageType> Slot<Name, AllocatedHash<F, PreimageType>> {
    pub fn new(name: Name, allocated: AllocatedHash<F, PreimageType>) -> Self {
        Self {
            name: Ok(name),
            allocated,
            consumed: false,
        }
    }
    pub fn new_dummy(allocated: AllocatedHash<F, PreimageType>) -> Self {
        Self {
            name: Err(()),
            allocated,
            consumed: false,
        }
    }
    #[allow(dead_code)]
    pub fn is_dummy(&self) -> bool {
        self.name.is_err()
    }
    pub fn is_blank(&self) -> bool {
        self.allocated.digest.get_value().is_none()
    }
    pub fn is_consumed(&self) -> bool {
        self.consumed
    }
    fn consume(&mut self) {
        self.consumed = true
    }
}

pub struct AllocatedWitness<'a, VanillaWitness, Name: Debug, AllocatedType> {
    #[allow(dead_code)]
    pub(crate) witness: &'a VanillaWitness, // Sometimes used for debugging.
    slots: Vec<Slot<Name, AllocatedType>>,
}

impl<'a, VanillaWitness, Name: Debug, F: LurkField, PreimageType>
    AllocatedWitness<'a, VanillaWitness, Name, AllocatedHash<F, PreimageType>>
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

pub type AllocatedConsWitness<'a, F> =
    AllocatedWitness<'a, ConsWitness<F>, ConsName, AllocatedPtrHash<F>>;
pub type AllocatedContWitness<'a, F> =
    AllocatedWitness<'a, ContWitness<F>, ContName, AllocatedNumHash<F>>;

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
            let cs = &mut cs0.namespace(|| format!("slot-{i}"));

            let (car_ptr, cdr_ptr, cons_hash) = match p {
                Stub::Dummy => (
                    Some(ScalarPtr::from_parts(ExprTag::Nil, F::zero())),
                    Some(ScalarPtr::from_parts(ExprTag::Nil, F::zero())),
                    None,
                ),
                Stub::Blank => (None, None, None),
                Stub::Value(hash) => (
                    s.hash_expr(&hash.car),
                    s.hash_expr(&hash.cdr),
                    s.hash_expr(&hash.cons),
                ),
            };

            let allocated_car = AllocatedPtr::alloc(&mut cs.namespace(|| "car"), || {
                car_ptr.ok_or(SynthesisError::AssignmentMissing)
            })?;

            let allocated_cdr = AllocatedPtr::alloc(&mut cs.namespace(|| "cdr"), || {
                cdr_ptr.ok_or(SynthesisError::AssignmentMissing)
            })?;

            let allocated_hash = AllocatedPtrHash::alloc(
                &mut cs.namespace(|| "cons"),
                s.poseidon_constants(),
                vec![allocated_car, allocated_cdr],
            )?;

            if cons_hash.is_some() {
                slots.push(Slot::new(*name, allocated_hash));
            } else {
                slots.push(Slot::new_dummy(allocated_hash));
            }
        }

        Ok(Self {
            witness: cons_witness,
            slots,
        })
    }

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
            let cs = &mut cs0.namespace(|| format!("slot-{i}"));

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
                        AllocatedNum::alloc(&mut cs.namespace(|| format!("component_{i}")), || {
                            Ok(*component)
                        })
                        .unwrap()
                    })
                    .collect::<Vec<_>>()
            } else {
                (0..8usize)
                    .map(|i| {
                        AllocatedNum::alloc(
                            &mut cs.namespace(|| format!("component_{i}")),
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
                slots.push(Slot::new(*name, allocated_hash));
            } else {
                slots.push(Slot::new_dummy(allocated_hash));
            }
        }

        Ok(Self {
            witness: cont_witness,
            slots,
        })
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
                    dbg!(&self.witness);
                    panic!("requested {:?} but found a dummy allocation", name)
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
