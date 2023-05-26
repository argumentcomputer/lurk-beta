use anyhow::anyhow;
use base32ct::{Base32Unpadded, Encoding};
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::fmt::{Display, Formatter};
use std::hash::Hash;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;

use crate::field::{FWrap, LurkField};
use crate::hash::IntoHashComponents;
use crate::store::{self, Store};
use crate::tag::{ContTag, ExprTag, Tag};

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

impl<E: Tag, F: LurkField> Serialize for ZPtr<E, F> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        (FWrap(self.0.to_field::<F>()), FWrap(self.1)).serialize(serializer)
    }
}

impl<'de, E: Tag, F: LurkField> Deserialize<'de> for ZPtr<E, F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let (x, y) = <(FWrap<F>, FWrap<F>)>::deserialize(deserializer)?;
        let tag_as_u16 =
            x.0.to_u16()
                .ok_or_else(|| serde::de::Error::custom("invalid range for field element tag"))?;
        let tag = E::try_from(tag_as_u16).map_err(|_| serde::de::Error::custom("invalid tag"))?;
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

    pub fn to_base32(&self) -> String {
        let tag_b32 = Base32Unpadded::encode_string(&self.0.into().to_le_bytes());
        let val_b32 = Base32Unpadded::encode_string(self.1.to_repr().as_ref());
        format!("{}z{}", tag_b32, val_b32)
    }

    pub fn from_base32(zptr: &str) -> Result<Self, anyhow::Error> {
        let tag_bytes = Base32Unpadded::decode_vec(&zptr[0..4])
            .map_err(|_| anyhow!("Failed to decode base32"))?;
        let val_bytes = Base32Unpadded::decode_vec(&zptr[5..])
            .map_err(|_| anyhow!("Failed to decode base32"))?;
        let tag = E::try_from(u16::from_le_bytes(tag_bytes[..2].try_into().unwrap()))
            .map_err(|_| anyhow!("Failed to decode tag"))?;
        let val = F::from_bytes(&val_bytes).ok_or_else(|| anyhow!("Failed to decode field"))?;
        Ok(Self::from_parts(tag, val))
    }
}

pub type ZExprPtr<F> = ZPtr<ExprTag, F>;

// TODO: Remove this in favor of the idiomatic approach
// Only used in public_parameters::proof_key
// Parse string, intern Expr into store, then convert Ptr to ZPtr
impl<F: LurkField> TryFrom<&String> for ZExprPtr<F> {
    type Error = store::Error;

    fn try_from(value: &String) -> Result<Self, Self::Error> {
        let mut store = Store::<F>::default();
        let ptr = store
            .read(value)
            .map_err(|_| store::Error("Parse error".into()))?;
        let zptr = store
            .hash_expr(&ptr)
            .ok_or(store::Error("Invalid ptr".into()))?;
        Ok(zptr)
    }
}

impl<E: Tag, F: LurkField> IntoHashComponents<F> for ZPtr<E, F> {
    fn into_hash_components(self) -> [F; 2] {
        [self.0.to_field::<F>(), self.1]
    }
}

pub type ZContPtr<F> = ZPtr<ContTag, F>;

#[cfg(test)]
mod tests {
    use super::*;
    use pasta_curves::pallas::Scalar;

    #[test]
    fn unit_base32() {
        let zptr = ZExprPtr::from_parts(ExprTag::Nil, Scalar::zero());
        assert_eq!(zptr, ZPtr::from_base32(&zptr.to_base32()).unwrap());
    }

    proptest! {
      #[test]
      fn prop_base32(x in any::<ZExprPtr<Scalar>>()) {
        assert_eq!(x, ZPtr::from_base32(&x.to_base32()).unwrap());
      }
    }
}
