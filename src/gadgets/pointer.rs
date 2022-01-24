use std::fmt::Debug;

use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    ConstraintSystem, SynthesisError,
};
use blstrs::Scalar as Fr;
use neptune::circuit::poseidon_hash;

use crate::{
    pool::{
        ContPtr, Continuation, Expression, Pool, Ptr, ScalarContPtr, ScalarPointer, ScalarPtr,
        Thunk, POSEIDON_CONSTANTS_8,
    },
    writer::Write,
};

use super::{
    constraints::{alloc_equal, equal, pick},
    data::allocate_constant,
};

#[derive(Clone)]
pub struct AllocatedPtr {
    tag: AllocatedNum<Fr>,
    hash: AllocatedNum<Fr>,
}

impl Debug for AllocatedPtr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let tag = format!(
            "AllocatedNum {{ value: {:?}, variable: {:?} }}",
            self.tag.get_value(),
            self.tag.get_variable()
        );
        let hash = format!(
            "AllocatedNum {{ value: {:?}, variable: {:?} }}",
            self.hash.get_value(),
            self.hash.get_variable()
        );
        f.debug_struct("AllocatedPtr")
            .field("tag", &tag)
            .field("hash", &hash)
            .finish()
    }
}

impl AllocatedPtr {
    pub fn tag(&self) -> &AllocatedNum<Fr> {
        &self.tag
    }

    pub fn hash(&self) -> &AllocatedNum<Fr> {
        &self.hash
    }

    pub fn get_tag_value(&self) -> Option<Fr> {
        self.tag.get_value()
    }

    pub fn get_hash_value(&self) -> Option<Fr> {
        self.hash.get_value()
    }

    pub fn from_allocated_parts(
        tag: AllocatedNum<Fr>,
        hash: AllocatedNum<Fr>,
        pool: &Pool,
    ) -> Self {
        if let (Some(tag), Some(hash)) = (tag.get_value(), hash.get_value()) {
            assert!(
                pool.verify_scalar_ptr(tag, hash),
                "trying to allocate invalid AllocatedPtr: {:?}, {:?}",
                tag,
                hash,
            );
        }
        Self::from_allocated_parts_unchecked(tag, hash)
    }

    pub fn from_allocated_parts_unchecked(tag: AllocatedNum<Fr>, hash: AllocatedNum<Fr>) -> Self {
        Self { tag, hash }
    }

    pub fn from_unallocated_parts<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        unallocated_tag: Fr,
        unallocated_hash: Fr,
        pool: &Pool,
    ) -> Result<Self, SynthesisError> {
        assert!(
            pool.verify_scalar_ptr(unallocated_tag, unallocated_hash),
            "trying to allocate invalid AllocatedContPtr"
        );

        Self::from_unallocated_parts_unchecked(cs, unallocated_tag, unallocated_hash)
    }

    pub fn from_unallocated_parts_unchecked<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        unallocated_tag: Fr,
        unallocated_hash: Fr,
    ) -> Result<Self, SynthesisError> {
        let tag = AllocatedNum::alloc(&mut cs.namespace(|| "tag"), || Ok(unallocated_tag))?;
        let hash = AllocatedNum::alloc(&mut cs.namespace(|| "hash"), || Ok(unallocated_hash))?;
        Ok(Self { tag, hash })
    }

    pub fn from_ptr<CS>(cs: &mut CS, pool: &Pool, ptr: Option<&Ptr>) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Fr>,
    {
        let scalar_ptr = ptr.and_then(|ptr| pool.hash_expr(ptr));
        Self::from_scalar_ptr(cs, scalar_ptr.as_ref())
    }

    pub fn constant_from_ptr<CS>(
        cs: &mut CS,
        pool: &Pool,
        ptr: &Ptr,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Fr>,
    {
        let scalar_ptr = pool.hash_expr(ptr).expect("missing constant ptr");
        Self::constant_from_scalar_ptr(cs, &scalar_ptr)
    }

    pub fn from_scalar_ptr<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        ptr: Option<&ScalarPtr>,
    ) -> Result<Self, SynthesisError> {
        let tag = AllocatedNum::alloc(&mut cs.namespace(|| "allocate tag"), || {
            ptr.map(|x| *x.tag())
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        let hash = AllocatedNum::alloc(&mut cs.namespace(|| "allocate hash"), || {
            ptr.map(|x| *x.value())
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        Ok(Self::from_allocated_parts_unchecked(tag, hash))
    }

    pub fn constant_from_scalar_ptr<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        ptr: &ScalarPtr,
    ) -> Result<Self, SynthesisError> {
        let tag = allocate_constant(&mut cs.namespace(|| "allocate tag"), *ptr.tag())?;
        let hash = allocate_constant(&mut cs.namespace(|| "allocate hash"), *ptr.value())?;
        Ok(Self::from_allocated_parts_unchecked(tag, hash))
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

    pub fn expr<'a>(&self, pool: &'a Pool) -> Option<Expression<'a>> {
        let ptr = self.ptr(pool)?;
        pool.fetch(&ptr)
    }

    pub fn ptr(&self, pool: &Pool) -> Option<Ptr> {
        let scalar_ptr = self.scalar_ptr(pool)?;
        pool.fetch_scalar(&scalar_ptr)
    }

    pub fn scalar_ptr(&self, pool: &Pool) -> Option<ScalarPtr> {
        let (tag, value) = (self.tag.get_value()?, self.hash.get_value()?);
        match pool.scalar_from_parts(tag, value) {
            Some(ptr) => Some(ptr),
            None => panic!("Missing ScalarPtr for {:?}", self),
        }
    }

    pub fn fetch_and_write_str(&self, pool: &Pool) -> String {
        self.ptr(pool)
            .map(|a| a.fmt_to_string(pool))
            .unwrap_or("no ptr".to_string())
    }

    pub fn allocate_thunk_components<CS: ConstraintSystem<Fr>>(
        &self,
        cs: CS,
        pool: &Pool,
    ) -> Result<(AllocatedNum<Fr>, AllocatedPtr, AllocatedContPtr), SynthesisError> {
        let maybe_thunk = if let Some(ptr) = self.scalar_ptr(pool) {
            if let Some(Expression::Thunk(thunk)) =
                pool.fetch_scalar(&ptr).and_then(|ptr| pool.fetch(&ptr))
            {
                Some(thunk)
            } else {
                None
            }
        } else {
            None
        };
        dbg!(&maybe_thunk, self);

        // self.expr(pool).and_then(|expr| {
        //             if let Expression::Thunk(thunk) = expr {
        //                 Some(thunk)
        //             } else {
        //                 None
        //             }
        //         });
        Thunk::allocate_maybe_dummy_components(cs, maybe_thunk.as_ref(), pool)
    }
}

#[derive(Clone)]
pub struct AllocatedContPtr {
    tag: AllocatedNum<Fr>,
    hash: AllocatedNum<Fr>,
}

impl Debug for AllocatedContPtr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let tag = format!(
            "AllocatedNum {{ value: {:?}, variable: {:?} }}",
            self.tag.get_value(),
            self.tag.get_variable()
        );
        let hash = format!(
            "AllocatedNum {{ value: {:?}, variable: {:?} }}",
            self.hash.get_value(),
            self.hash.get_variable()
        );
        f.debug_struct("AllocatedContPtr")
            .field("tag", &tag)
            .field("hash", &hash)
            .finish()
    }
}

impl Ptr {
    pub fn allocate_ptr<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
        pool: &Pool,
    ) -> Result<AllocatedPtr, SynthesisError> {
        let scalar_ptr = pool.hash_expr(self).expect("missing ptr");
        scalar_ptr.allocate_ptr(cs)
    }

    pub fn allocate_constant_ptr<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
        pool: &Pool,
    ) -> Result<AllocatedPtr, SynthesisError> {
        dbg!(self);
        let scalar_ptr = pool.hash_expr(self).expect("missing ptr");
        scalar_ptr.allocate_constant_ptr(cs)
    }
}

impl ScalarPtr {
    pub fn allocate_ptr<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedPtr, SynthesisError> {
        AllocatedPtr::from_scalar_ptr(cs, Some(self))
    }

    pub fn allocate_constant_ptr<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedPtr, SynthesisError> {
        let allocated_tag = allocate_constant(&mut cs.namespace(|| "tag"), *self.tag())?;
        let allocated_hash = allocate_constant(&mut cs.namespace(|| "hash"), *self.value())?;

        Ok(AllocatedPtr::from_allocated_parts_unchecked(
            allocated_tag,
            allocated_hash,
        ))
    }
}

impl AllocatedContPtr {
    pub fn alloc<CS: ConstraintSystem<Fr>, F>(cs: &mut CS, value: F) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<ScalarContPtr, SynthesisError>,
    {
        let mut hash = None;
        let alloc_tag = AllocatedNum::alloc(&mut cs.namespace(|| "allocate tag"), || {
            let ptr = value()?;
            hash = Some(*ptr.value());
            Ok(*ptr.tag())
        })?;

        let alloc_hash = AllocatedNum::alloc(&mut cs.namespace(|| "allocate hash"), || {
            hash.ok_or(SynthesisError::AssignmentMissing)
        })?;

        Ok(AllocatedContPtr {
            tag: alloc_tag,
            hash: alloc_hash,
        })
    }

    pub fn alloc_constant<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        value: ScalarContPtr,
    ) -> Result<Self, SynthesisError> {
        let alloc_tag = allocate_constant(&mut cs.namespace(|| "tag"), *value.tag())?;
        let alloc_hash = allocate_constant(&mut cs.namespace(|| "hash"), *value.value())?;

        Ok(AllocatedContPtr {
            tag: alloc_tag,
            hash: alloc_hash,
        })
    }

    pub fn tag(&self) -> &AllocatedNum<Fr> {
        &self.tag
    }

    pub fn hash(&self) -> &AllocatedNum<Fr> {
        &self.hash
    }

    pub fn alloc_cont_ptr<'a, CS, F>(
        cs: &mut CS,
        pool: &Pool,
        value: F,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Fr>,
        F: FnOnce() -> Result<&'a ContPtr, SynthesisError>,
    {
        AllocatedContPtr::alloc(cs, || {
            let ptr = value()?;
            pool.hash_cont(ptr).ok_or(SynthesisError::AssignmentMissing)
        })
    }

    pub fn alloc_constant_cont_ptr<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        pool: &Pool,
        value: &ContPtr,
    ) -> Result<Self, SynthesisError> {
        let ptr = pool
            .hash_cont(value)
            .ok_or(SynthesisError::AssignmentMissing)?;
        AllocatedContPtr::alloc_constant(cs, ptr)
    }

    pub fn enforce_equal<CS: ConstraintSystem<Fr>>(&self, cs: &mut CS, other: &Self) {
        // debug_assert_eq!(self.tag.get_value(), other.tag.get_value());
        equal(cs, || "tags equal", &self.tag, &other.tag);
        // debug_assert_eq!(self.hash.get_value(), other.hash.get_value());
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

    pub fn get_cont<'a>(&self, pool: &Pool) -> Option<Continuation> {
        let ptr = self.get_cont_ptr(pool)?;
        pool.fetch_cont(&ptr)
    }

    pub fn get_cont_ptr(&self, pool: &Pool) -> Option<ContPtr> {
        let scalar_ptr = self.get_scalar_ptr_cont(pool)?;
        pool.fetch_scalar_cont(&scalar_ptr)
    }

    pub fn get_scalar_ptr_cont(&self, pool: &Pool) -> Option<ScalarContPtr> {
        let (tag, value) = (self.tag.get_value()?, self.hash.get_value()?);

        match pool.scalar_from_parts_cont(tag, value) {
            Some(ptr) => Some(ptr),
            None => panic!("Missing ScalarContPtr for {:?}", self),
        }
    }

    pub fn fetch_and_write_cont_str(&self, pool: &Pool) -> String {
        self.get_cont_ptr(pool)
            .map(|a| a.fmt_to_string(pool))
            .unwrap_or("no cont ptr".to_string())
    }

    /// Takes two allocated numbers (`a`, `b`) and returns `a` if the condition is true, and `b` otherwise.
    pub fn pick<CS>(
        mut cs: CS,
        condition: &Boolean,
        a: &Self,
        b: &Self,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Fr>,
    {
        let tag = pick(cs.namespace(|| "tag"), condition, a.tag(), b.tag())?;
        let hash = pick(cs.namespace(|| "hash"), condition, a.hash(), b.hash())?;

        Ok(AllocatedContPtr { tag, hash })
    }

    pub fn bind_input<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        cont: Option<&ContPtr>,
        pool: &Pool,
    ) -> Result<AllocatedContPtr, SynthesisError> {
        let ptr = cont.and_then(|c| pool.hash_cont(c));

        let tag = AllocatedNum::alloc(cs.namespace(|| "continuation tag"), || {
            ptr.map(|c| *c.tag())
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        tag.inputize(cs.namespace(|| "continuation tag input"))?;

        let hash = AllocatedNum::alloc(cs.namespace(|| "continuation hash"), || {
            ptr.map(|c| *c.value())
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        hash.inputize(cs.namespace(|| "continuation hash input"))?;

        Ok(AllocatedContPtr { tag, hash })
    }

    pub fn by_index(n: usize, case_results: &[AllocatedNum<Fr>]) -> Self {
        AllocatedContPtr {
            tag: case_results[n * 2].clone(),
            hash: case_results[1 + n * 2].clone(),
        }
    }

    pub fn construct<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        cont_tag: &AllocatedNum<Fr>,
        components: &[&dyn AsAllocatedHashComponents; 4],
        _pool: &Pool,
    ) -> Result<Self, SynthesisError> {
        let components = components
            .iter()
            .map(|c| c.as_allocated_hash_components())
            .flatten()
            .map(|p| p.clone())
            .collect();

        let hash = poseidon_hash(
            cs.namespace(|| "Continuation"),
            components,
            &POSEIDON_CONSTANTS_8,
        )?;

        let cont = AllocatedContPtr {
            tag: cont_tag.clone(),
            hash: hash, /*, pool*/
        };
        Ok(cont)
    }
}

pub trait AsAllocatedHashComponents {
    fn as_allocated_hash_components(&self) -> [&AllocatedNum<Fr>; 2];
}

impl AsAllocatedHashComponents for AllocatedPtr {
    fn as_allocated_hash_components(&self) -> [&AllocatedNum<Fr>; 2] {
        [&self.tag, &self.hash]
    }
}

impl AsAllocatedHashComponents for AllocatedContPtr {
    fn as_allocated_hash_components(&self) -> [&AllocatedNum<Fr>; 2] {
        [&self.tag, &self.hash]
    }
}

impl AsAllocatedHashComponents for [&AllocatedNum<Fr>; 2] {
    fn as_allocated_hash_components(&self) -> [&AllocatedNum<Fr>; 2] {
        [self[0], self[1]]
    }
}
