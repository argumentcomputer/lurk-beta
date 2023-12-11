use anyhow::anyhow;
use base32ct::{Base32Unpadded, Encoding};
#[cfg(not(target_arch = "wasm32"))]
use lurk_macros::serde_test;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::fmt::{Display, Formatter};
use std::hash::Hash;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;

#[cfg(not(target_arch = "wasm32"))]
use crate::field::FWrap;
use crate::field::LurkField;
use crate::tag::{ContTag, ExprTag, Tag};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(
    not(target_arch = "wasm32"),
    serde_test(
        types(ExprTag, pasta_curves::pallas::Scalar),
        types(ContTag, pasta_curves::pallas::Scalar),
        zdata(true)
    )
)]
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
        Some(self.cmp(other))
    }
}

impl<E: Tag, F: LurkField> Ord for ZPtr<E, F> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        (
            self.0.to_field_bytes::<F>().as_ref(),
            self.1.to_repr().as_ref(),
        )
            .cmp(&(
                other.0.to_field_bytes::<F>().as_ref(),
                other.1.to_repr().as_ref(),
            ))
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
    /// Creates a ZPtr from a tag and a value
    pub fn from_parts(tag: E, value: F) -> Self {
        ZPtr(tag, value)
    }

    /// Returns the tag
    pub fn tag(&self) -> &E {
        &self.0
    }

    /// Returns the tag in field representation
    pub fn tag_field(&self) -> F {
        self.0.to_field::<F>()
    }

    /// Returns the value
    pub fn value(&self) -> &F {
        &self.1
    }

    pub fn parts(&self) -> (F, F) {
        (self.tag_field(), self.1)
    }

    // TODO: Create a permanent format for ZPtr strings/ZIDs
    /// Converts the ZPtr to a base32-encoded string
    pub fn to_base32(&self) -> String {
        let tag_b32 = Base32Unpadded::encode_string(&self.0.into().to_le_bytes());
        let val_b32 = Base32Unpadded::encode_string(self.1.to_repr().as_ref());
        format!("{tag_b32}z{val_b32}")
    }

    /// Converts a base32-encoded string to a ZPtr
    pub fn from_base32(zptr: &str) -> Result<Self, anyhow::Error> {
        let tag_bytes = Base32Unpadded::decode_vec(&zptr[0..4])
            .map_err(|e| anyhow!(format!("Failed to decode base32: {}", e)))?;
        let val_bytes = Base32Unpadded::decode_vec(&zptr[5..])
            .map_err(|e| anyhow!(format!("Failed to decode base32: {}", e)))?;
        let tag = E::try_from(u16::from_le_bytes(tag_bytes[..2].try_into().unwrap()))
            .map_err(|e| anyhow!(format!("Failed to decode tag: {}", e)))?;
        let val = F::from_bytes(&val_bytes).ok_or_else(|| anyhow!("Failed to decode field"))?;
        Ok(Self::from_parts(tag, val))
    }
}

/// Alias for an expression pointer
pub type ZExprPtr<F> = ZPtr<ExprTag, F>;

/// Alias for a continuation pointer
pub type ZContPtr<F> = ZPtr<ContTag, F>;

#[cfg(test)]
mod tests {
    use super::*;
    use pasta_curves::pallas::Scalar;

    proptest! {
        #[test]
        fn prop_base32_z_expr_ptr(x in any::<ZExprPtr<Scalar>>()) {
            assert_eq!(x, ZPtr::from_base32(&x.to_base32()).unwrap());
        }
    }

    #[test]
    fn unit_base32_z_expr_ptr() {
        let zptr = ZExprPtr::from_parts(ExprTag::Nil, Scalar::zero());
        assert_eq!(zptr, ZPtr::from_base32(&zptr.to_base32()).unwrap());
    }
}
