use std::fmt::Debug;

use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    ConstraintSystem, SynthesisError,
};
use ff::PrimeField;

use crate::{
    field::LurkField,
    hash_witness::ConsName,
    store::{
        ContPtr, Continuation, Expression, IntoHashComponents, Ptr, ScalarContPtr, ScalarPointer,
        ScalarPtr, Store, Thunk,
    },
    writer::Write,
};

use super::{
    constraints::{alloc_equal, enforce_implication, equal, pick},
    data::{allocate_constant, hash_poseidon, GlobalAllocations},
    hashes::AllocatedHashWitness,
};

/// Allocated version of `Ptr`.
#[derive(Clone)]
pub struct AllocatedPtr<F: PrimeField> {
    tag: AllocatedNum<F>,
    hash: AllocatedNum<F>,
}

impl<F: LurkField> Debug for AllocatedPtr<F> {
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

impl<F: LurkField> AllocatedPtr<F> {
    pub fn alloc<Fo, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        value: Fo,
    ) -> Result<Self, SynthesisError>
    where
        Fo: FnOnce() -> Result<ScalarPtr<F>, SynthesisError>,
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

    pub fn alloc_constant<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        value: ScalarPtr<F>,
    ) -> Result<Self, SynthesisError> {
        let alloc_tag = allocate_constant(&mut cs.namespace(|| "tag"), *value.tag())?;
        let alloc_hash = allocate_constant(&mut cs.namespace(|| "hash"), *value.value())?;

        Ok(AllocatedPtr {
            tag: alloc_tag,
            hash: alloc_hash,
        })
    }

    pub fn alloc_ptr<'a, Fo, CS>(
        cs: &mut CS,
        store: &Store<F>,
        value: Fo,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
        Fo: FnOnce() -> Result<&'a Ptr<F>, SynthesisError>,
    {
        AllocatedPtr::alloc(cs, || {
            let ptr = value()?;
            store
                .get_expr_hash(ptr)
                .ok_or(SynthesisError::AssignmentMissing)
        })
    }

    pub fn alloc_constant_ptr<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        store: &Store<F>,
        value: &Ptr<F>,
    ) -> Result<Self, SynthesisError> {
        let ptr = store
            .get_expr_hash(value)
            .ok_or(SynthesisError::AssignmentMissing)?;
        AllocatedPtr::alloc_constant(cs, ptr)
    }

    pub fn from_parts(tag: &AllocatedNum<F>, hash: &AllocatedNum<F>) -> Self {
        AllocatedPtr {
            tag: tag.clone(),
            hash: hash.clone(),
        }
    }

    pub fn tag(&self) -> &AllocatedNum<F> {
        &self.tag
    }

    pub fn hash(&self) -> &AllocatedNum<F> {
        &self.hash
    }

    pub fn enforce_equal<CS: ConstraintSystem<F>>(&self, cs: &mut CS, other: &Self) {
        // debug_assert_eq!(self.tag.get_value(), other.tag.get_value());
        equal(cs, || "tags equal", &self.tag, &other.tag);
        // debug_assert_eq!(self.hash.get_value(), other.hash.get_value());
        equal(cs, || "hashes equal", &self.hash, &other.hash);
    }

    pub fn alloc_equal<CS: ConstraintSystem<F>>(
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

    pub fn ptr(&self, store: &Store<F>) -> Option<Ptr<F>> {
        let scalar_ptr = self.scalar_ptr(store)?;
        store.fetch_scalar(&scalar_ptr)
    }

    pub fn scalar_ptr(&self, store: &Store<F>) -> Option<ScalarPtr<F>> {
        let (tag, value) = (self.tag.get_value()?, self.hash.get_value()?);
        store.scalar_from_parts(tag, value)
    }

    pub fn fetch_and_write_str(&self, store: &Store<F>) -> String {
        self.ptr(store)
            .map(|a| a.fmt_to_string(store))
            .unwrap_or_else(|| "<PTR MISSING>".to_string())
    }

    pub fn allocate_thunk_components<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        store: &Store<F>,
    ) -> Result<(AllocatedNum<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        let maybe_thunk = if let Some(ptr) = self.scalar_ptr(store) {
            if let Some(Expression::Thunk(thunk)) =
                store.fetch_scalar(&ptr).and_then(|ptr| store.fetch(&ptr))
            {
                Some(thunk)
            } else {
                None
            }
        } else {
            None
        };

        Thunk::allocate_maybe_dummy_components(cs, maybe_thunk.as_ref(), store)
    }

    pub fn alloc_hash_components<CS: ConstraintSystem<F>, T: IntoHashComponents<F>>(
        cs: &mut CS,
        t: T,
    ) -> Result<Self, SynthesisError> {
        let [tag, hash] = t.into_hash_components();

        let tag = AllocatedNum::alloc(&mut cs.namespace(|| "tag"), || Ok(tag))?;
        let hash = AllocatedNum::alloc(&mut cs.namespace(|| "hash"), || Ok(hash))?;

        Ok(Self { tag, hash })
    }

    pub fn construct_cons<CS: ConstraintSystem<F>>(
        mut cs: CS,
        g: &GlobalAllocations<F>,
        store: &Store<F>,
        car: &AllocatedPtr<F>,
        cdr: &AllocatedPtr<F>,
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        // This is actually binary_hash, considering creating that helper for use elsewhere.
        let preimage = vec![
            car.tag().clone(),
            car.hash().clone(),
            cdr.tag().clone(),
            cdr.hash().clone(),
        ];

        let hash = hash_poseidon(
            cs.namespace(|| "Cons hash"),
            preimage,
            store.poseidon_constants().c4(),
        )?;

        Ok(AllocatedPtr {
            tag: g.cons_tag.clone(),
            hash,
        })
    }

    pub fn construct_cons_named<CS: ConstraintSystem<F>>(
        mut cs: CS,
        g: &GlobalAllocations<F>,
        car: &AllocatedPtr<F>,
        cdr: &AllocatedPtr<F>,
        name: ConsName,
        allocated_hash_witness: &AllocatedHashWitness<F>,
        not_dummy: &Boolean,
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        let expect_dummy = !(not_dummy.get_value().unwrap_or(false));
        let (allocated_car, allocated_cdr, allocated_digest) =
            allocated_hash_witness.get_cons(name, expect_dummy);

        let real_car = car.alloc_equal(&mut cs.namespace(|| "real_car"), allocated_car)?;
        let real_cdr = cdr.alloc_equal(&mut cs.namespace(|| "real_cdr"), allocated_cdr)?;
        let cons_is_real = and!(cs, &real_car, &real_cdr)?;

        enforce_implication(
            &mut cs.namespace(|| "not_dummy implies real cons"),
            not_dummy,
            &cons_is_real,
        )?;

        if not_dummy.get_value().unwrap_or(false) && !cons_is_real.get_value().unwrap_or(true) {
            dbg!(name);
            panic!("uh oh!");
        }

        Ok(AllocatedPtr {
            tag: g.cons_tag.clone(),
            hash: allocated_digest.clone(),
        })
    }

    pub fn construct_commitment<CS: ConstraintSystem<F>>(
        mut cs: CS,
        g: &GlobalAllocations<F>,
        store: &Store<F>,
        secret: &AllocatedNum<F>,
        expr: &AllocatedPtr<F>,
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        let preimage = vec![secret.clone(), expr.tag().clone(), expr.hash().clone()];

        let hash = hash_poseidon(
            cs.namespace(|| "Commitment hash"),
            preimage,
            store.poseidon_constants().c3(),
        )?;

        Ok(AllocatedPtr {
            tag: g.comm_tag.clone(),
            hash,
        })
    }

    pub fn construct_strcons<CS: ConstraintSystem<F>>(
        mut cs: CS,
        g: &GlobalAllocations<F>,
        store: &Store<F>,
        car: &AllocatedPtr<F>,
        cdr: &AllocatedPtr<F>,
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        // This is actually binary_hash, considering creating that helper for use elsewhere.
        let preimage = vec![
            car.tag().clone(),
            car.hash().clone(),
            cdr.tag().clone(),
            cdr.hash().clone(),
        ];

        let hash = hash_poseidon(
            cs.namespace(|| "StrCons hash"),
            preimage,
            store.poseidon_constants().c4(),
        )?;

        Ok(AllocatedPtr {
            tag: g.str_tag.clone(),
            hash,
        })
    }

    pub fn construct_fun<CS: ConstraintSystem<F>>(
        mut cs: CS,
        g: &GlobalAllocations<F>,
        store: &Store<F>,
        arg: &AllocatedPtr<F>,
        body: &AllocatedPtr<F>,
        closed_env: &AllocatedPtr<F>,
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        let preimage = vec![
            arg.tag().clone(),
            arg.hash().clone(),
            body.tag().clone(),
            body.hash().clone(),
            closed_env.tag().clone(),
            closed_env.hash().clone(),
        ];

        let hash = hash_poseidon(
            cs.namespace(|| "Fun hash"),
            preimage,
            store.poseidon_constants().c6(),
        )?;

        Ok(AllocatedPtr {
            tag: g.fun_tag.clone(),
            hash,
        })
    }

    pub fn construct_list<CS: ConstraintSystem<F>>(
        mut cs: CS,
        g: &GlobalAllocations<F>,
        store: &Store<F>,
        elts: &[&AllocatedPtr<F>],
    ) -> Result<Self, SynthesisError> {
        if elts.is_empty() {
            return Ok(g.nil_ptr.clone());
        }

        let tail = Self::construct_list(&mut cs.namespace(|| "Cons tail"), g, store, &elts[1..])?;
        Self::construct_cons(&mut cs.namespace(|| "Cons"), g, store, elts[0], &tail)
    }

    pub fn construct_thunk<CS: ConstraintSystem<F>>(
        cs: CS,
        g: &GlobalAllocations<F>,
        store: &Store<F>,
        val: &AllocatedPtr<F>,
        cont: &AllocatedContPtr<F>,
    ) -> Result<Self, SynthesisError> {
        let thunk_hash = Thunk::hash_components(cs, store, val, cont)?;

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
        CS: ConstraintSystem<F>,
    {
        let tag = pick(cs.namespace(|| "tag"), condition, a.tag(), b.tag())?;
        let hash = pick(cs.namespace(|| "hash"), condition, a.hash(), b.hash())?;

        Ok(AllocatedPtr { tag, hash })
    }

    pub fn by_index(n: usize, ptr_vec: &[AllocatedNum<F>]) -> Self {
        AllocatedPtr {
            tag: ptr_vec[n * 2].clone(),
            hash: ptr_vec[1 + n * 2].clone(),
        }
    }

    pub fn bind_input<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        expr: Option<&Ptr<F>>,
        store: &Store<F>,
    ) -> Result<Self, SynthesisError> {
        let ptr = expr.and_then(|e| store.get_expr_hash(e));

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
pub struct AllocatedContPtr<F: LurkField> {
    tag: AllocatedNum<F>,
    hash: AllocatedNum<F>,
}

impl<F: LurkField> Debug for AllocatedContPtr<F> {
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

impl<F: LurkField> AllocatedContPtr<F> {
    pub fn alloc<Fo, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        value: Fo,
    ) -> Result<Self, SynthesisError>
    where
        Fo: FnOnce() -> Result<ScalarContPtr<F>, SynthesisError>,
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

    pub fn alloc_constant<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        value: ScalarContPtr<F>,
    ) -> Result<Self, SynthesisError> {
        let alloc_tag = allocate_constant(&mut cs.namespace(|| "tag"), *value.tag())?;
        let alloc_hash = allocate_constant(&mut cs.namespace(|| "hash"), *value.value())?;

        Ok(AllocatedContPtr {
            tag: alloc_tag,
            hash: alloc_hash,
        })
    }

    pub fn tag(&self) -> &AllocatedNum<F> {
        &self.tag
    }

    pub fn hash(&self) -> &AllocatedNum<F> {
        &self.hash
    }

    pub fn alloc_cont_ptr<'a, Fo, CS>(
        cs: &mut CS,
        store: &Store<F>,
        value: Fo,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
        Fo: FnOnce() -> Result<&'a ContPtr<F>, SynthesisError>,
    {
        AllocatedContPtr::alloc(cs, || {
            let ptr = value()?;
            store
                .hash_cont(ptr)
                .ok_or(SynthesisError::AssignmentMissing)
        })
    }

    pub fn alloc_constant_cont_ptr<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        store: &Store<F>,
        value: &ContPtr<F>,
    ) -> Result<Self, SynthesisError> {
        let ptr = store
            .hash_cont(value)
            .ok_or(SynthesisError::AssignmentMissing)?;
        AllocatedContPtr::alloc_constant(cs, ptr)
    }

    pub fn enforce_equal<CS: ConstraintSystem<F>>(&self, cs: &mut CS, other: &Self) {
        // debug_assert_eq!(self.tag.get_value(), other.tag.get_value());
        equal(cs, || "tags equal", &self.tag, &other.tag);
        // debug_assert_eq!(self.hash.get_value(), other.hash.get_value());
        equal(cs, || "hashes equal", &self.hash, &other.hash);
    }

    pub fn alloc_equal<CS: ConstraintSystem<F>>(
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

    pub fn get_cont(&self, store: &Store<F>) -> Option<Continuation<F>> {
        let ptr = self.get_cont_ptr(store)?;
        store.fetch_cont(&ptr)
    }

    pub fn get_cont_ptr(&self, store: &Store<F>) -> Option<ContPtr<F>> {
        let scalar_ptr = self.get_scalar_ptr_cont(store)?;
        store.fetch_scalar_cont(&scalar_ptr)
    }

    pub fn get_scalar_ptr_cont(&self, store: &Store<F>) -> Option<ScalarContPtr<F>> {
        let (tag, value) = (self.tag.get_value()?, self.hash.get_value()?);
        store.scalar_from_parts_cont(tag, value)
    }

    pub fn fetch_and_write_cont_str(&self, store: &Store<F>) -> String {
        self.get_cont_ptr(store)
            .map(|a| a.fmt_to_string(store))
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
        CS: ConstraintSystem<F>,
    {
        let tag = pick(cs.namespace(|| "tag"), condition, a.tag(), b.tag())?;
        let hash = pick(cs.namespace(|| "hash"), condition, a.hash(), b.hash())?;

        Ok(AllocatedContPtr { tag, hash })
    }

    pub fn bind_input<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        cont: Option<&ContPtr<F>>,
        store: &Store<F>,
    ) -> Result<AllocatedContPtr<F>, SynthesisError> {
        let ptr = cont.and_then(|c| store.hash_cont(c));

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

    pub fn by_index(n: usize, ptr_vec: &[AllocatedNum<F>]) -> Self {
        AllocatedContPtr {
            tag: ptr_vec[n * 2].clone(),
            hash: ptr_vec[1 + n * 2].clone(),
        }
    }

    pub fn construct<CS: ConstraintSystem<F>>(
        mut cs: CS,
        store: &Store<F>,
        cont_tag: &AllocatedNum<F>,
        components: &[&dyn AsAllocatedHashComponents<F>; 4],
    ) -> Result<Self, SynthesisError> {
        let components = components
            .iter()
            .flat_map(|c| c.as_allocated_hash_components())
            .cloned()
            .collect();

        let hash = hash_poseidon(
            cs.namespace(|| "Continuation"),
            components,
            store.poseidon_constants().c8(),
        )?;

        let cont = AllocatedContPtr {
            tag: cont_tag.clone(),
            hash,
        };
        Ok(cont)
    }

    pub fn from_parts(tag: &AllocatedNum<F>, hash: &AllocatedNum<F>) -> Self {
        Self {
            tag: tag.clone(),
            hash: hash.clone(),
        }
    }
}

pub trait AsAllocatedHashComponents<F: LurkField> {
    fn as_allocated_hash_components(&self) -> [&AllocatedNum<F>; 2];
}

impl<F: LurkField> AsAllocatedHashComponents<F> for AllocatedPtr<F> {
    fn as_allocated_hash_components(&self) -> [&AllocatedNum<F>; 2] {
        [&self.tag, &self.hash]
    }
}

impl<F: LurkField> AsAllocatedHashComponents<F> for AllocatedContPtr<F> {
    fn as_allocated_hash_components(&self) -> [&AllocatedNum<F>; 2] {
        [&self.tag, &self.hash]
    }
}

impl<F: LurkField> AsAllocatedHashComponents<F> for [&AllocatedNum<F>; 2] {
    fn as_allocated_hash_components(&self) -> [&AllocatedNum<F>; 2] {
        [self[0], self[1]]
    }
}
