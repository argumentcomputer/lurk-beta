use std::fmt::Debug;

use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;

use crate::{
    cont::Continuation,
    field::LurkField,
    ptr::{ContPtr, Ptr},
    store::Store,
    tag::{ExprTag, Tag},
    z_ptr::{ZContPtr, ZExprPtr, ZPtr},
};

use super::{
    constraints::{alloc_equal, alloc_equal_const, enforce_equal, implies_equal, pick, pick_const},
    data::{allocate_constant, hash_poseidon, GlobalAllocations},
};

/// Allocated version of `Ptr`.
#[derive(Clone)]
pub struct AllocatedPtr<F: PrimeField> {
    tag: AllocatedNum<F>,
    hash: AllocatedNum<F>,
}

impl<F: LurkField> From<AllocatedPtr<F>> for AllocatedContPtr<F> {
    fn from(other: AllocatedPtr<F>) -> Self {
        AllocatedContPtr {
            tag: other.tag,
            hash: other.hash,
        }
    }
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
    pub fn alloc<Fo, CS: ConstraintSystem<F>, T: Tag>(
        cs: &mut CS,
        value: Fo,
    ) -> Result<Self, SynthesisError>
    where
        Fo: FnOnce() -> Result<ZPtr<T, F>, SynthesisError>,
    {
        let mut hash = None;
        let alloc_tag = AllocatedNum::alloc(&mut cs.namespace(|| "tag"), || {
            let ptr = value()?;
            hash = Some(*ptr.value());
            Ok(ptr.tag_field())
        })?;

        let alloc_hash = AllocatedNum::alloc(&mut cs.namespace(|| "hash"), || {
            hash.ok_or(SynthesisError::AssignmentMissing)
        })?;

        Ok(AllocatedPtr {
            tag: alloc_tag,
            hash: alloc_hash,
        })
    }

    pub fn alloc_infallible<Fo, CS: ConstraintSystem<F>, T: Tag>(cs: &mut CS, value: Fo) -> Self
    where
        Fo: FnOnce() -> ZPtr<T, F>,
    {
        let mut hash = None;
        let alloc_tag = AllocatedNum::alloc_infallible(&mut cs.namespace(|| "tag"), || {
            let ptr = value();
            hash = Some(*ptr.value());
            ptr.tag_field()
        });

        let alloc_hash =
            AllocatedNum::alloc_infallible(&mut cs.namespace(|| "hash"), || hash.unwrap());

        AllocatedPtr {
            tag: alloc_tag,
            hash: alloc_hash,
        }
    }

    pub fn alloc_tag<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        tag: F,
        alloc_hash: AllocatedNum<F>,
    ) -> Result<Self, SynthesisError> {
        let alloc_tag = allocate_constant(&mut cs.namespace(|| "tag"), tag);

        Ok(AllocatedPtr {
            tag: alloc_tag,
            hash: alloc_hash,
        })
    }

    pub fn alloc_constant<CS: ConstraintSystem<F>, T: Tag>(
        cs: &mut CS,
        value: ZPtr<T, F>,
    ) -> Result<Self, SynthesisError> {
        let alloc_tag = allocate_constant(&mut cs.namespace(|| "tag"), value.tag_field());
        let alloc_hash = allocate_constant(&mut cs.namespace(|| "hash"), *value.value());

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
                .hash_expr(ptr)
                .ok_or(SynthesisError::AssignmentMissing)
        })
    }

    pub fn alloc_constant_ptr<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        store: &Store<F>,
        value: &Ptr<F>,
    ) -> Result<Self, SynthesisError> {
        let ptr = store
            .hash_expr(value)
            .ok_or(SynthesisError::AssignmentMissing)?;
        AllocatedPtr::alloc_constant(cs, ptr)
    }

    pub fn from_parts(tag: AllocatedNum<F>, hash: AllocatedNum<F>) -> Self {
        AllocatedPtr { tag, hash }
    }

    pub fn tag(&self) -> &AllocatedNum<F> {
        &self.tag
    }

    pub fn hash(&self) -> &AllocatedNum<F> {
        &self.hash
    }

    pub fn enforce_equal<CS: ConstraintSystem<F>>(&self, cs: &mut CS, other: &Self) {
        // debug_assert_eq!(self.tag.get_value(), other.tag.get_value());
        enforce_equal(cs, || "tags equal", &self.tag, &other.tag);
        // debug_assert_eq!(self.hash.get_value(), other.hash.get_value());
        enforce_equal(cs, || "hashes equal", &self.hash, &other.hash);
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

    pub fn alloc_tag_equal<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        tag: F,
    ) -> Result<Boolean, SynthesisError> {
        alloc_equal_const(&mut cs.namespace(|| "tags equal"), &self.tag, tag)
    }

    /// Enforce equality of two allocated pointers given an implication premise
    pub fn implies_ptr_equal<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        premise: &Boolean,
        other: &AllocatedPtr<F>,
    ) {
        implies_equal(
            &mut cs.namespace(|| "implies tag equal"),
            premise,
            self.tag(),
            other.tag(),
        );
        implies_equal(
            &mut cs.namespace(|| "implies hash equal"),
            premise,
            self.hash(),
            other.hash(),
        );
    }

    pub fn is_nil<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocations<F>,
    ) -> Result<Boolean, SynthesisError> {
        alloc_equal(cs, self.tag(), g.nil_ptr.tag())
    }
    pub fn is_cons<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        self.alloc_tag_equal(&mut cs.namespace(|| "is_cons"), ExprTag::Cons.to_field())
    }
    pub fn is_str<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        self.alloc_tag_equal(&mut cs.namespace(|| "is_str"), ExprTag::Str.to_field())
    }
    pub fn is_num<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        self.alloc_tag_equal(&mut cs.namespace(|| "is_num"), ExprTag::Num.to_field())
    }
    pub fn is_u64<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        self.alloc_tag_equal(&mut cs.namespace(|| "is_u64"), ExprTag::U64.to_field())
    }
    pub fn is_char<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        self.alloc_tag_equal(&mut cs.namespace(|| "is_char"), ExprTag::Char.to_field())
    }
    pub fn is_comm<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        self.alloc_tag_equal(&mut cs.namespace(|| "is_comm"), ExprTag::Comm.to_field())
    }
    pub fn is_sym<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        self.alloc_tag_equal(&mut cs.namespace(|| "is_sym"), ExprTag::Sym.to_field())
    }
    pub fn is_fun<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<Boolean, SynthesisError> {
        self.alloc_tag_equal(&mut cs.namespace(|| "is_fun"), ExprTag::Fun.to_field())
    }
    pub fn is_thunk<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> Result<Boolean, SynthesisError> {
        self.alloc_tag_equal(&mut cs.namespace(|| "is_thunk"), ExprTag::Thunk.to_field())
    }

    pub fn ptr(&self, store: &Store<F>) -> Option<Ptr<F>> {
        let z_ptr = self.z_ptr(store)?;
        store.fetch_z_expr_ptr(&z_ptr)
    }

    pub fn z_ptr(&self, store: &Store<F>) -> Option<ZExprPtr<F>> {
        let (tag, value) = (self.tag.get_value()?, self.hash.get_value()?);
        store.z_expr_ptr_from_parts(tag, value).ok()
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

    pub fn pick_const<CS>(
        mut cs: CS,
        condition: &Boolean,
        a: &ZExprPtr<F>,
        b: &ZExprPtr<F>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let tag = pick_const(
            cs.namespace(|| "tag"),
            condition,
            a.tag_field(),
            b.tag_field(),
        )?;
        let hash = pick_const(cs.namespace(|| "hash"), condition, *a.value(), *b.value())?;

        Ok(AllocatedPtr { tag, hash })
    }

    pub fn bind_input<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        expr: Option<&Ptr<F>>,
        store: &Store<F>,
    ) -> Result<Self, SynthesisError> {
        let ptr = expr.and_then(|e| store.hash_expr(e));

        let tag = AllocatedNum::alloc(cs.namespace(|| "tag"), || {
            ptr.as_ref()
                .map(|th| th.tag_field())
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

impl<F: LurkField> From<AllocatedContPtr<F>> for AllocatedPtr<F> {
    fn from(other: AllocatedContPtr<F>) -> Self {
        AllocatedPtr {
            tag: other.tag,
            hash: other.hash,
        }
    }
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
        Fo: FnOnce() -> Result<ZContPtr<F>, SynthesisError>,
    {
        let mut hash = None;
        let alloc_tag = AllocatedNum::alloc(&mut cs.namespace(|| "tag"), || {
            let ptr = value()?;
            hash = Some(*ptr.value());
            Ok(ptr.tag_field())
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
        value: ZContPtr<F>,
    ) -> Result<Self, SynthesisError> {
        let alloc_tag = allocate_constant(&mut cs.namespace(|| "tag"), value.tag_field());
        let alloc_hash = allocate_constant(&mut cs.namespace(|| "hash"), *value.value());

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
        enforce_equal(cs, || "tags equal", &self.tag, &other.tag);
        // debug_assert_eq!(self.hash.get_value(), other.hash.get_value());
        enforce_equal(cs, || "hashes equal", &self.hash, &other.hash);
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

    pub fn alloc_tag_equal<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        tag: F,
    ) -> Result<Boolean, SynthesisError> {
        alloc_equal_const(&mut cs.namespace(|| "tags equal"), &self.tag, tag)
    }

    pub fn get_cont(&self, store: &Store<F>) -> Option<Continuation<F>> {
        let ptr = self.get_cont_ptr(store)?;
        store.fetch_cont(&ptr)
    }

    pub fn get_cont_ptr(&self, store: &Store<F>) -> Option<ContPtr<F>> {
        let z_ptr = self.get_z_ptr_cont(store)?;
        store.fetch_z_cont_ptr(&z_ptr)
    }

    pub fn get_z_ptr_cont(&self, store: &Store<F>) -> Option<ZContPtr<F>> {
        let (tag, value) = (self.tag.get_value()?, self.hash.get_value()?);
        store.z_cont_ptr_from_parts(tag, value).ok()
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
            ptr.map(|c| c.tag_field())
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
