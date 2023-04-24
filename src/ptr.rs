use anyhow::anyhow;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use std::{fmt, marker::PhantomData};

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;

use libipld::Cid;
use libipld::Multihash;

use crate::light_data::Encodable;
use crate::light_data::LightData;

use crate::field::{FWrap, LurkField};
use crate::tag::{ContTag, ExprTag, Tag};

use serde::Deserialize;
use serde::Serialize;
use serde::{de, ser};

use crate::hash::IntoHashComponents;

pub trait Object<F: LurkField>: fmt::Debug + Clone + PartialEq {
    type Pointer: Pointer<F>;
}

pub trait Pointer<F: LurkField + From<u64>>: fmt::Debug + Copy + Clone + PartialEq + Hash {
    type Tag: Tag;

    fn tag(&self) -> Self::Tag;
    fn tag_field(&self) -> F {
        F::from(self.tag().into() as u64)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Ptr<F: LurkField>(pub ExprTag, pub RawPtr<F>);

#[allow(clippy::derived_hash_with_manual_eq)]
impl<F: LurkField> Hash for Ptr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}

impl<F: LurkField> Ptr<F> {
    // TODO: Make these methods and the similar ones defined on expression consistent, probably including a shared trait.

    // NOTE: Although this could be a type predicate now, when NIL becomes a symbol, it won't be possible.
    pub const fn is_nil(&self) -> bool {
        matches!(self.0, ExprTag::Nil)
        // FIXME: check value also, probably
    }
    pub const fn is_cons(&self) -> bool {
        matches!(self.0, ExprTag::Cons)
    }

    pub const fn is_atom(&self) -> bool {
        !self.is_cons()
    }

    pub const fn is_list(&self) -> bool {
        matches!(self.0, ExprTag::Nil | ExprTag::Cons)
    }

    pub const fn is_opaque(&self) -> bool {
        self.1.is_opaque()
    }

    pub const fn as_cons(self) -> Option<Self> {
        if self.is_cons() {
            Some(self)
        } else {
            None
        }
    }

    pub const fn as_list(self) -> Option<Self> {
        if self.is_list() {
            Some(self)
        } else {
            None
        }
    }
}

impl<F: LurkField> From<char> for Ptr<F> {
    fn from(c: char) -> Self {
        Self(ExprTag::Char, RawPtr::new(u32::from(c) as usize))
    }
}

impl<F: LurkField> Pointer<F> for Ptr<F> {
    type Tag = ExprTag;

    fn tag(&self) -> ExprTag {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
// Note: the trait bound E: Tag is not necessary in the struct, but it makes the proptest strategy more efficient.
/// A struct representing a scalar pointer with a tag and a value.
///
/// The `SPtr` struct is used to store a tagged scalar pointer, where `E` is its tag, and `F` the field for its values.
/// It has two important aliases, `ScalarPtr` and `ScalarContPtr`, which are used respectively with `ExprTag` and `ContTag`,
/// i.e. the type of expressions and the type of continuations.
pub struct SPtr<E: Tag, F: LurkField>(
    pub E,
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(strategy = "any::<FWrap<F>>().prop_map(|x| x.0)")
    )]
    pub F,
);

impl<E: Tag + Display, F: LurkField> Display for SPtr<E, F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let tag = self.0;
        let trimmed_f = self.1.trimmed_hex_digits();
        write!(f, "(ptr->{tag}, {trimmed_f})",)
    }
}

impl<E: Tag, F: LurkField> PartialOrd for SPtr<E, F> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        (
            self.0.to_field_bytes::<F>().as_ref(),
            self.1.to_repr().as_ref(),
        )
            .partial_cmp(&(
                other.0.to_field_bytes::<F>().as_ref(),
                other.1.to_repr().as_ref(),
            ))
    }
}

impl<E: Tag, F: LurkField> Ord for SPtr<E, F> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.partial_cmp(other)
            .expect("SPtr::cmp: partial_cmp domain invariant violation")
    }
}

impl<E: Tag, F: LurkField> Encodable for SPtr<E, F> {
    fn ser(&self) -> LightData {
        let (x, y): (FWrap<F>, FWrap<F>) = (FWrap(self.0.to_field()), FWrap(self.1));
        (x, y).ser()
    }
    fn de(ld: &LightData) -> anyhow::Result<Self> {
        let (x, y): (FWrap<F>, FWrap<F>) = Encodable::de(ld)?;
        let tag_as_u16 =
            x.0.to_u16()
                .ok_or_else(|| anyhow!("invalid range for field element representing a tag"))?;
        let tag = E::try_from(tag_as_u16).map_err(|_| anyhow!("invalid tag"))?;
        Ok(SPtr(tag, y.0))
    }
}

#[allow(clippy::derived_hash_with_manual_eq)]
impl<E: Tag, F: LurkField> Hash for SPtr<E, F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_field_bytes::<F>().as_ref().hash(state);
        self.1.to_repr().as_ref().hash(state);
    }
}

impl<E: Tag, F: LurkField> SPtr<E, F> {
    pub fn from_parts(tag: E, value: F) -> Self {
        SPtr(tag, value)
    }

    pub fn tag(&self) -> E {
        self.0
    }

    pub fn tag_field(&self) -> F {
        self.0.to_field::<F>()
    }

    pub fn value(&self) -> &F {
        &self.1
    }
}

impl<E: Tag, F: LurkField> Serialize for SPtr<E, F> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use ser::Error;
        let tag = self.tag_field();
        let val = self.value();
        // magic numbers to avoid multicodec table collisons
        // this will disappear when we move from IPLD to LDON
        let codec: u64 = 0x10de << 48 | tag.to_u64_unchecked();
        let hash = Multihash::wrap(codec, &val.to_bytes())
            .map_err(|_| S::Error::custom("expected validly tagged ScalarPtr".to_string()))?;
        let cid = Cid::new_v1(codec, hash);
        cid.serialize(serializer)
    }
}

impl<'de, E: Tag, F: LurkField> Deserialize<'de> for SPtr<E, F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use de::Error;
        let cid = Cid::deserialize(deserializer)?;
        let tag = F::from_u64(cid.codec() & 0x0000_0000_ffff_ffff);
        let val = F::from_bytes(cid.hash().digest())
            .ok_or_else(|| D::Error::custom("expected ScalarContPtr value".to_string()))?;
        // TODO(fga): eliminate this round-trip through the field
        let e_tag = E::from_field(&tag).ok_or_else(|| D::Error::custom("invalid Tag"))?;
        Ok(SPtr::from_parts(e_tag, val))
    }
}

pub type ScalarPtr<F> = SPtr<ExprTag, F>;

impl<E: Tag, F: LurkField> IntoHashComponents<F> for SPtr<E, F> {
    fn into_hash_components(self) -> [F; 2] {
        [self.0.to_field::<F>(), self.1]
    }
}

pub type ScalarContPtr<F> = SPtr<ContTag, F>;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ContPtr<F: LurkField>(pub ContTag, pub RawPtr<F>);

#[allow(clippy::derived_hash_with_manual_eq)]
impl<F: LurkField> Hash for ContPtr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}

impl<F: LurkField> Pointer<F> for ContPtr<F> {
    type Tag = ContTag;

    fn tag(&self) -> Self::Tag {
        self.0
    }
}

impl<F: LurkField> ContPtr<F> {
    pub const fn new(tag: ContTag, raw_ptr: RawPtr<F>) -> Self {
        Self(tag, raw_ptr)
    }
    pub const fn is_error(&self) -> bool {
        matches!(self.0, ContTag::Error)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
// If .0 is negative, RawPtr is opaque. This lets us retain the efficiency and structure of the current implementation.
// It cuts the local store's address space in half, which is likely not an issue. This representation does not affect
// external data, so if we want to change it in the future, we can do so without a change of defined behavior.
pub struct RawPtr<F: LurkField>(pub (usize, bool), pub PhantomData<F>);

impl<F: LurkField> RawPtr<F> {
    pub fn new(p: usize) -> Self {
        RawPtr((p, false), Default::default())
    }

    pub const fn is_opaque(&self) -> bool {
        self.0 .1
    }

    pub const fn idx(&self) -> usize {
        self.0 .0
    }
}

#[allow(clippy::derived_hash_with_manual_eq)]
impl<F: LurkField> Hash for RawPtr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
