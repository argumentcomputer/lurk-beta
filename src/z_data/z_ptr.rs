use anyhow::anyhow;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
use std::fmt;
use std::fmt::{Display, Formatter};
use std::hash::Hash;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;

use libipld::Cid;
use libipld::Multihash;

use crate::z_data::Encodable;
use crate::z_data::ZData;

use crate::field::{FWrap, LurkField};
use crate::tag::{ContTag, ExprTag, Tag};

use serde::Deserialize;
use serde::Serialize;
use serde::{de, ser};

use crate::hash::IntoHashComponents;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
// Note: the trait bound E: Tag is not necessary in the struct, but it makes the proptest strategy more efficient.
/// A struct representing a scalar pointer with a tag and a value.
///
/// The `ZPtr` struct is used to store a tagged scalar pointer, where `E` is its tag, and `F` the field for its values.
/// It has two important aliases, `ZExprPtr` and `ZContPtr`, which are used respectively with `ExprTag` and `ContTag`,
/// i.e. the type of expressions and the type of continuations.
pub struct ZPtr<E: Tag, F: LurkField>(
    pub E,
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(strategy = "any::<FWrap<F>>().prop_map(|x| x.0)")
    )]
    pub F,
);

impl<E: Tag + Display, F: LurkField> Display for ZPtr<E, F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let tag = self.0;
        let trimmed_f = self.1.trimmed_hex_digits();
        write!(f, "(ptr->{tag}, {trimmed_f})",)
    }
}

impl<E: Tag, F: LurkField> PartialOrd for ZPtr<E, F> {
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

impl<E: Tag, F: LurkField> Ord for ZPtr<E, F> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.partial_cmp(other)
            .expect("ZPtr::cmp: partial_cmp domain invariant violation")
    }
}

impl<E: Tag, F: LurkField> Encodable for ZPtr<E, F> {
    fn ser(&self) -> ZData {
        let (x, y): (FWrap<F>, FWrap<F>) = (FWrap(self.0.to_field()), FWrap(self.1));
        (x, y).ser()
    }
    fn de(ld: &ZData) -> anyhow::Result<Self> {
        let (x, y): (FWrap<F>, FWrap<F>) = Encodable::de(ld)?;
        let tag_as_u16 =
            x.0.to_u16()
                .ok_or_else(|| anyhow!("invalid range for field element representing a tag"))?;
        let tag = E::try_from(tag_as_u16).map_err(|_| anyhow!("invalid tag"))?;
        Ok(ZPtr(tag, y.0))
    }
}

#[allow(clippy::derived_hash_with_manual_eq)]
impl<E: Tag, F: LurkField> Hash for ZPtr<E, F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_field_bytes::<F>().as_ref().hash(state);
        self.1.to_repr().as_ref().hash(state);
    }
}

impl<E: Tag, F: LurkField> ZPtr<E, F> {
    pub fn from_parts(tag: E, value: F) -> Self {
        ZPtr(tag, value)
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

impl<E: Tag, F: LurkField> Serialize for ZPtr<E, F> {
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
            .map_err(|_| S::Error::custom("expected validly tagged ZExprPtr".to_string()))?;
        let cid = Cid::new_v1(codec, hash);
        cid.serialize(serializer)
    }
}

impl<'de, E: Tag, F: LurkField> Deserialize<'de> for ZPtr<E, F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use de::Error;
        let cid = Cid::deserialize(deserializer)?;
        let tag = F::from_u64(cid.codec() & 0x0000_0000_ffff_ffff);
        let val = F::from_bytes(cid.hash().digest())
            .ok_or_else(|| D::Error::custom("expected ZContPtr value".to_string()))?;
        // TODO(fga): eliminate this round-trip through the field
        let e_tag = E::from_field(&tag).ok_or_else(|| D::Error::custom("invalid Tag"))?;
        Ok(ZPtr::from_parts(e_tag, val))
    }
}

pub type ZExprPtr<F> = ZPtr<ExprTag, F>;

impl<E: Tag, F: LurkField> IntoHashComponents<F> for ZPtr<E, F> {
    fn into_hash_components(self) -> [F; 2] {
        [self.0.to_field::<F>(), self.1]
    }
}

pub type ZContPtr<F> = ZPtr<ContTag, F>;
