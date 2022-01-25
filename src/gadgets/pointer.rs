use std::fmt::Debug;

use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    ConstraintSystem, SynthesisError,
};
use blstrs::Scalar as Fr;
use neptune::circuit::poseidon_hash;

use crate::{
    pool::{
        ContPtr, Continuation, Expression, IntoHashComponents, Pool, Ptr, ScalarContPtr,
        ScalarPointer, ScalarPtr, Thunk, POSEIDON_CONSTANTS_4, POSEIDON_CONSTANTS_6,
        POSEIDON_CONSTANTS_8,
    },
    writer::Write,
};

use super::{
    constraints::{alloc_equal, equal, pick},
    data::{allocate_constant, GlobalAllocations},
};

/// Allocated version of `Ptr`.
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
    pub fn alloc<CS: ConstraintSystem<Fr>, F>(cs: &mut CS, value: F) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<ScalarPtr, SynthesisError>,
    {
        let mut hash = None;
        let alloc_tag = AllocatedNum::alloc(&mut cs.namespace(|| "tag"), || {
            let ptr = value()?;
            hash = Some(*ptr.value());
            Ok(*ptr.tag())
        })?;

        let alloc_hash = AllocatedNum::alloc(&mut cs.namespace(|| "hash"), || {
            hash.ok_or(SynthesisError::AssignmentMissing)
        })?;

        Ok(AllocatedPtr {
            tag: alloc_tag,
            hash: alloc_hash,
        })
    }

    pub fn alloc_constant<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        value: ScalarPtr,
    ) -> Result<Self, SynthesisError> {
        let alloc_tag = allocate_constant(&mut cs.namespace(|| "tag"), *value.tag())?;
        let alloc_hash = allocate_constant(&mut cs.namespace(|| "hash"), *value.value())?;

        Ok(AllocatedPtr {
            tag: alloc_tag,
            hash: alloc_hash,
        })
    }

    pub fn alloc_ptr<'a, CS, F>(cs: &mut CS, pool: &Pool, value: F) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Fr>,
        F: FnOnce() -> Result<&'a Ptr, SynthesisError>,
    {
        AllocatedPtr::alloc(cs, || {
            let ptr = value()?;
            pool.hash_expr(ptr).ok_or(SynthesisError::AssignmentMissing)
        })
    }

    pub fn alloc_constant_ptr<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        pool: &Pool,
        value: &Ptr,
    ) -> Result<Self, SynthesisError> {
        let ptr = pool
            .hash_expr(value)
            .ok_or(SynthesisError::AssignmentMissing)?;
        AllocatedPtr::alloc_constant(cs, ptr)
    }

    pub fn from_parts(tag: AllocatedNum<Fr>, hash: AllocatedNum<Fr>) -> Self {
        AllocatedPtr { tag, hash }
    }

    pub fn tag(&self) -> &AllocatedNum<Fr> {
        &self.tag
    }

    pub fn hash(&self) -> &AllocatedNum<Fr> {
        &self.hash
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

    pub fn ptr(&self, pool: &Pool) -> Option<Ptr> {
        let scalar_ptr = self.scalar_ptr(pool)?;
        pool.fetch_scalar(&scalar_ptr)
    }

    pub fn scalar_ptr(&self, pool: &Pool) -> Option<ScalarPtr> {
        let (tag, value) = (self.tag.get_value()?, self.hash.get_value()?);
        pool.scalar_from_parts(tag, value)
    }

    pub fn fetch_and_write_str(&self, pool: &Pool) -> String {
        self.ptr(pool)
            .map(|a| a.fmt_to_string(pool))
            .unwrap_or_else(|| "no ptr".to_string())
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

        Thunk::allocate_maybe_dummy_components(cs, maybe_thunk.as_ref(), pool)
    }

    pub fn alloc_hash_components<CS: ConstraintSystem<Fr>, T: IntoHashComponents>(
        cs: &mut CS,
        t: T,
    ) -> Result<Self, SynthesisError> {
        let [tag, hash] = t.into_hash_components();

        let tag = AllocatedNum::alloc(&mut cs.namespace(|| "tag"), || Ok(tag))?;
        let hash = AllocatedNum::alloc(&mut cs.namespace(|| "hash"), || Ok(hash))?;

        Ok(Self { tag, hash })
    }

    pub fn construct_cons<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        g: &GlobalAllocations,
        car: &AllocatedPtr,
        cdr: &AllocatedPtr,
    ) -> Result<AllocatedPtr, SynthesisError> {
        // This is actually binary_hash, considering creating that helper for use elsewhere.
        let preimage = vec![
            car.tag().clone(),
            car.hash().clone(),
            cdr.tag().clone(),
            cdr.hash().clone(),
        ];

        let hash = poseidon_hash(
            cs.namespace(|| "Cons hash"),
            preimage,
            &POSEIDON_CONSTANTS_4,
        )?;

        Ok(AllocatedPtr {
            tag: g.cons_tag.clone(),
            hash,
        })
    }

    pub fn construct_fun<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        g: &GlobalAllocations,
        arg: &AllocatedPtr,
        body: &AllocatedPtr,
        closed_env: &AllocatedPtr,
    ) -> Result<AllocatedPtr, SynthesisError> {
        let preimage = vec![
            arg.tag().clone(),
            arg.hash().clone(),
            body.tag().clone(),
            body.hash().clone(),
            closed_env.tag().clone(),
            closed_env.hash().clone(),
        ];

        let hash = poseidon_hash(cs.namespace(|| "Fun hash"), preimage, &POSEIDON_CONSTANTS_6)?;

        Ok(AllocatedPtr {
            tag: g.fun_tag.clone(),
            hash,
        })
    }

    pub fn construct_list<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        g: &GlobalAllocations,
        elts: &[&AllocatedPtr],
    ) -> Result<Self, SynthesisError> {
        if elts.is_empty() {
            return Ok(g.nil_ptr.clone());
        }

        let tail = Self::construct_list(&mut cs.namespace(|| "Cons tail"), g, &elts[1..])?;
        Self::construct_cons(&mut cs.namespace(|| "Cons"), g, elts[0], &tail)
    }

    pub fn construct_thunk<CS: ConstraintSystem<Fr>>(
        cs: CS,
        g: &GlobalAllocations,
        val: &AllocatedPtr,
        cont: &AllocatedContPtr,
    ) -> Result<Self, SynthesisError> {
        let thunk_hash = Thunk::hash_components(cs, val, cont)?;

        Ok(AllocatedPtr {
            tag: g.thunk_tag.clone(),
            hash: thunk_hash,
        })
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

        Ok(AllocatedPtr { tag, hash })
    }

    pub fn by_index(n: usize, case_results: &[AllocatedNum<Fr>]) -> Self {
        AllocatedPtr {
            tag: case_results[n * 2].clone(),
            hash: case_results[1 + n * 2].clone(),
        }
    }

    pub fn bind_input<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        expr: Option<&Ptr>,
        pool: &Pool,
    ) -> Result<Self, SynthesisError> {
        let ptr = expr.and_then(|e| pool.hash_expr(e));

        let tag = AllocatedNum::alloc(cs.namespace(|| "tag"), || {
            ptr.as_ref()
                .map(|th| *th.tag())
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        tag.inputize(cs.namespace(|| "tag input"))?;

        let hash = AllocatedNum::alloc(cs.namespace(|| "hash"), || {
            ptr.as_ref()
                .map(|th| *th.value())
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        hash.inputize(cs.namespace(|| "hash input"))?;

        Ok(AllocatedPtr { tag, hash })
    }
}

/// Allocated version of `ContPtr`.
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

impl AllocatedContPtr {
    pub fn alloc<CS: ConstraintSystem<Fr>, F>(cs: &mut CS, value: F) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<ScalarContPtr, SynthesisError>,
    {
        let mut hash = None;
        let alloc_tag = AllocatedNum::alloc(&mut cs.namespace(|| "tag"), || {
            let ptr = value()?;
            hash = Some(*ptr.value());
            Ok(*ptr.tag())
        })?;

        let alloc_hash = AllocatedNum::alloc(&mut cs.namespace(|| "hash"), || {
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

    pub fn get_cont(&self, pool: &Pool) -> Option<Continuation> {
        let ptr = self.get_cont_ptr(pool)?;
        pool.fetch_cont(&ptr)
    }

    pub fn get_cont_ptr(&self, pool: &Pool) -> Option<ContPtr> {
        let scalar_ptr = self.get_scalar_ptr_cont(pool)?;
        pool.fetch_scalar_cont(&scalar_ptr)
    }

    pub fn get_scalar_ptr_cont(&self, pool: &Pool) -> Option<ScalarContPtr> {
        let (tag, value) = (self.tag.get_value()?, self.hash.get_value()?);
        pool.scalar_from_parts_cont(tag, value)
    }

    pub fn fetch_and_write_cont_str(&self, pool: &Pool) -> String {
        self.get_cont_ptr(pool)
            .map(|a| a.fmt_to_string(pool))
            .unwrap_or_else(|| "no cont ptr".to_string())
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
    ) -> Result<Self, SynthesisError> {
        let components = components
            .iter()
            .flat_map(|c| c.as_allocated_hash_components())
            .cloned()
            .collect();

        let hash = poseidon_hash(
            cs.namespace(|| "Continuation"),
            components,
            &POSEIDON_CONSTANTS_8,
        )?;

        let cont = AllocatedContPtr {
            tag: cont_tag.clone(),
            hash,
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
