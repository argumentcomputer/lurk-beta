use std::fmt::Debug;

use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;

use crate::{
    field::LurkField,
    tag::{ExprTag, Tag},
    z_ptr::{ZContPtr, ZExprPtr, ZPtr},
};

use super::{
    constraints::{alloc_equal, alloc_equal_const, enforce_equal, implies_equal, pick, pick_const},
    data::allocate_constant,
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

    pub fn from_parts(tag: AllocatedNum<F>, hash: AllocatedNum<F>) -> Self {
        AllocatedPtr { tag, hash }
    }

    pub fn tag(&self) -> &AllocatedNum<F> {
        &self.tag
    }

    pub fn hash(&self) -> &AllocatedNum<F> {
        &self.hash
    }

    pub fn get_value<T: Tag>(&self) -> Option<ZPtr<T, F>> {
        self.tag.get_value().and_then(|tag| {
            self.hash
                .get_value()
                .map(|hash| ZPtr::from_parts(Tag::from_field(&tag).expect("bad tag"), hash))
        })
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
}
