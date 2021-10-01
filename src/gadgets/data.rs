use crate::data::{BaseContinuationTag, Continuation, Tag};
use crate::gadgets::constraints::{equal, pick};
use bellperson::{
    bls::{Bls12, Engine, Fr},
    gadgets::{
        boolean::{AllocatedBit, Boolean},
        num::AllocatedNum,
    },
    groth16::{self, verify_proof},
    Circuit, ConstraintSystem, SynthesisError,
};
use ff::Field;
use neptune::circuit::poseidon_hash;

#[derive(Clone)]
pub struct AllocatedTaggedHash<E: Engine> {
    pub tag: AllocatedNum<E>,
    pub hash: AllocatedNum<E>,
}

impl<E: Engine> AllocatedTaggedHash<E> {
    pub fn from_tag_and_hash(tag: AllocatedNum<E>, hash: AllocatedNum<E>) -> Self {
        Self { tag, hash }
    }

    pub fn enforce_equal<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Self) {
        equal(cs, || "tags equal", &self.tag, &other.tag);
        equal(cs, || "hashes equal", &self.hash, &other.hash);
    }
}

impl Continuation {
    pub fn allocate_constant_tagged_hash<CS: ConstraintSystem<Bls12>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedTaggedHash<Bls12>, SynthesisError> {
        // TODO: This actually hashes, so when possible we should cache.
        // When this is constant, we should not hash on every circuit synthesis.
        let tagged_hash = self.continuation_tagged_hash();
        let allocated_tag = allocate_constant(&mut cs.namespace(|| "tag"), tagged_hash.tag)?;
        let allocated_hash = allocate_constant(&mut cs.namespace(|| "hash"), tagged_hash.hash)?;

        Ok(AllocatedTaggedHash::from_tag_and_hash(
            allocated_tag,
            allocated_hash,
        ))
    }
}

pub fn allocate_constant<CS: ConstraintSystem<Bls12>>(
    cs: &mut CS,
    val: Fr,
) -> Result<AllocatedNum<Bls12>, SynthesisError> {
    let allocated = AllocatedNum::<Bls12>::alloc(cs.namespace(|| "allocate"), || Ok(val))?;

    // allocated * 1 = val
    cs.enforce(
        || "enforce constant",
        |lc| lc + allocated.get_variable(),
        |lc| lc + CS::one(),
        |_| Boolean::Constant(true).lc(CS::one(), val),
    );

    Ok(allocated)
}

impl Tag {
    pub fn allocate_constant<CS: ConstraintSystem<Bls12>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Bls12>, SynthesisError> {
        allocate_constant(&mut cs.namespace(|| format!("{:?} tag", self)), self.fr())
    }
}

impl BaseContinuationTag {
    pub fn allocate_constant<CS: ConstraintSystem<Bls12>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Bls12>, SynthesisError> {
        allocate_constant(
            &mut cs.namespace(|| format!("{:?} base continuation tag", self)),
            self.cont_tag_fr(),
        )
    }
}

/// Takes two allocated numbers (`a`, `b`) and returns `a` if the condition is true, and `b` otherwise.
pub fn pick_tagged_hash<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    condition: &Boolean,
    a: &AllocatedTaggedHash<E>,
    b: &AllocatedTaggedHash<E>,
) -> Result<AllocatedTaggedHash<E>, SynthesisError>
where
    CS: ConstraintSystem<E>,
{
    let tag = pick(cs.namespace(|| "tag"), condition, &a.tag, &b.tag)?;
    let hash = pick(cs.namespace(|| "hash"), condition, &a.hash, &b.hash)?;
    Ok(AllocatedTaggedHash::<E>::from_tag_and_hash(tag, hash))
}
