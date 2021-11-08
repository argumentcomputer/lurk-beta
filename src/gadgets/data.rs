use crate::data::{BaseContinuationTag, Continuation, Expression, Op1, Op2, Rel2, Tag, TaggedHash};
use crate::gadgets::constraints::{alloc_equal, equal, pick};
use bellperson::{
    gadgets::{
        boolean::{AllocatedBit, Boolean},
        num::AllocatedNum,
    },
    groth16::{self, verify_proof},
    Circuit, ConstraintSystem, SynthesisError,
};
use blstrs::Scalar as Fr;
use ff::{Field, PrimeField};
use neptune::circuit::poseidon_hash;

#[derive(Clone)]
pub struct AllocatedTaggedHash {
    pub tag: AllocatedNum<Fr>,
    pub hash: AllocatedNum<Fr>,
}

impl AllocatedTaggedHash {
    pub fn from_tag_and_hash(tag: AllocatedNum<Fr>, hash: AllocatedNum<Fr>) -> Self {
        Self { tag, hash }
    }

    pub fn from_unallocated_tag_and_hash<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        unallocated_tag: Fr,
        unallocated_hash: Fr,
    ) -> Result<Self, SynthesisError> {
        let tag = AllocatedNum::alloc(&mut cs.namespace(|| "tag"), || Ok(unallocated_tag))?;
        let hash = AllocatedNum::alloc(&mut cs.namespace(|| "hash"), || Ok(unallocated_hash))?;
        Ok(Self { tag, hash })
    }

    pub fn from_tagged_hash<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        tagged_hash: TaggedHash,
    ) -> Result<Self, SynthesisError> {
        let tag =
            AllocatedNum::alloc(&mut cs.namespace(|| "allocate tag"), || Ok(tagged_hash.tag))?;
        let hash = AllocatedNum::alloc(&mut cs.namespace(|| "allocate hash"), || {
            Ok(tagged_hash.hash)
        })?;
        Ok(Self::from_tag_and_hash(tag, hash))
    }

    pub fn enforce_equal<CS: ConstraintSystem<Fr>>(&self, cs: &mut CS, other: &Self) {
        equal(cs, || "tags equal", &self.tag, &other.tag);
        equal(cs, || "hashes equal", &self.hash, &other.hash);
    }

    pub fn alloc_equal<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Boolean, SynthesisError> {
        let tags_equal = alloc_equal(&mut cs.namespace(|| "tags equal"), &self.tag, &other.tag)?;
        let hashes_equal = alloc_equal(
            &mut cs.namespace(|| "hashes equal"),
            &self.hash,
            &other.hash,
        )?;

        Boolean::and(
            &mut cs.namespace(|| "tags and hashes equal"),
            &tags_equal,
            &hashes_equal,
        )
    }

    pub fn tagged_hash(&self) -> TaggedHash {
        TaggedHash {
            tag: self.tag.get_value().unwrap(),
            hash: self.hash.get_value().unwrap(),
        }
    }
}

impl Expression {
    pub fn allocated_tagged_hash<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedTaggedHash, SynthesisError> {
        AllocatedTaggedHash::from_tagged_hash(cs, self.tagged_hash())
    }

    pub fn allocate_constant_tagged_hash<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedTaggedHash, SynthesisError> {
        // TODO: This actually hashes, so when possible we should cache.
        // When this is constant, we should not hash on every circuit synthesis.
        let tagged_hash = self.tagged_hash();
        let allocated_tag = allocate_constant(&mut cs.namespace(|| "tag"), tagged_hash.tag)?;
        let allocated_hash = allocate_constant(&mut cs.namespace(|| "hash"), tagged_hash.hash)?;

        Ok(AllocatedTaggedHash::from_tag_and_hash(
            allocated_tag,
            allocated_hash,
        ))
    }
}

impl Continuation {
    pub fn allocated_tagged_hash<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedTaggedHash, SynthesisError> {
        AllocatedTaggedHash::from_tagged_hash(cs, self.continuation_tagged_hash())
    }

    pub fn allocate_constant_tagged_hash<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedTaggedHash, SynthesisError> {
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

pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    val: Fr,
) -> Result<AllocatedNum<Fr>, SynthesisError> {
    let allocated = AllocatedNum::<Fr>::alloc(cs.namespace(|| "allocate"), || Ok(val))?;

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
    pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        allocate_constant(&mut cs.namespace(|| format!("{:?} tag", self)), self.fr())
    }
}

impl BaseContinuationTag {
    pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        allocate_constant(
            &mut cs.namespace(|| format!("{:?} base continuation tag", self)),
            self.cont_tag_fr(),
        )
    }
}

impl Op1 {
    pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        allocate_constant(&mut cs.namespace(|| format!("{:?} tag", self)), self.fr())
    }
}

impl Op2 {
    pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        allocate_constant(&mut cs.namespace(|| format!("{:?} tag", self)), self.fr())
    }
}

impl Rel2 {
    pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        allocate_constant(&mut cs.namespace(|| format!("{:?} tag", self)), self.fr())
    }
}

/// Takes two allocated numbers (`a`, `b`) and returns `a` if the condition is true, and `b` otherwise.
pub fn pick_tagged_hash<CS>(
    mut cs: CS,
    condition: &Boolean,
    a: &AllocatedTaggedHash,
    b: &AllocatedTaggedHash,
) -> Result<AllocatedTaggedHash, SynthesisError>
where
    CS: ConstraintSystem<Fr>,
{
    let tag = pick(cs.namespace(|| "tag"), condition, &a.tag, &b.tag)?;
    let hash = pick(cs.namespace(|| "hash"), condition, &a.hash, &b.hash)?;
    Ok(AllocatedTaggedHash::from_tag_and_hash(tag, hash))
}
