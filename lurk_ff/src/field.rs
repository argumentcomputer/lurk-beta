use crate::tag::{ContTag, ExprTag, FieldKind, Op1Tag, Op2Tag, Tag, TagKind, Version};
use ff::{PrimeField, PrimeFieldBits};

const CURRENT_VERSION: Version = Version {
    major: 0,
    minor: 0,
    patch: 0,
};

pub trait LurkField: PrimeField + PrimeFieldBits {
    const VERSION: Version;
    const FIELD_KIND: FieldKind;

    fn from_bytes(bs: &[u8]) -> Option<Self> {
        let mut def: Self::Repr = Self::default().to_repr();
        def.as_mut().copy_from_slice(bs);
        Self::from_repr(def).into()
    }

    fn to_bytes(self) -> Vec<u8> {
        let repr = self.to_repr();
        repr.as_ref().to_vec()
    }

    fn display_string(self) -> String {
        let mut s = String::from("0x");
        let bytes = self.to_bytes();
        for b in bytes.iter().rev() {
            s.push_str(&format!("{:02x?}", b));
        }
        s
    }
    fn to_u16(&self) -> Option<u16> {
        for x in &self.to_repr().as_ref()[2..] {
            if *x != 0 {
                return None;
            }
        }
        let mut byte_array = [0u8; 2];
        byte_array.copy_from_slice(&self.to_repr().as_ref()[0..2]);
        Some(u16::from_le_bytes(byte_array))
    }
    fn to_u32(&self) -> Option<u32> {
        for x in &self.to_repr().as_ref()[4..] {
            if *x != 0 {
                return None;
            }
        }
        let mut byte_array = [0u8; 4];
        byte_array.copy_from_slice(&self.to_repr().as_ref()[0..4]);
        Some(u32::from_le_bytes(byte_array))
    }
    fn to_char(&self) -> Option<char> {
        let x = self.to_u32()?;
        char::from_u32(x)
    }
    fn to_u64(&self) -> Option<u64> {
        for x in &self.to_repr().as_ref()[8..] {
            if *x != 0 {
                return None;
            }
        }
        let mut byte_array = [0u8; 8];
        byte_array.copy_from_slice(&self.to_repr().as_ref()[0..8]);
        Some(u64::from_le_bytes(byte_array))
    }
    // Return a u64 corresponding to the first 8 little-endian bytes of this field element, discarding the remaining bytes.
    fn to_u64_unchecked(&self) -> u64 {
        let mut byte_array = [0u8; 8];
        byte_array.copy_from_slice(&self.to_repr().as_ref()[0..8]);
        u64::from_le_bytes(byte_array)
    }

    fn from_u64(x: u64) -> Self {
        x.into()
    }

    fn from_u32(x: u32) -> Self {
        (x as u64).into()
    }

    fn from_char(x: char) -> Self {
        Self::from_u32(x as u32)
    }

    fn most_negative() -> Self {
        Self::most_positive() + Self::one()
    }

    /// 0 - 1 is one minus the modulus, which must be even in a prime field.
    /// The result is the largest field element which is even when doubled.
    /// We define this to be the most positive field element.
    fn most_positive() -> Self {
        let one = Self::one();
        let two = one + one;

        let half = two.invert().unwrap();
        let modulus_minus_one = Self::zero() - one;
        half * modulus_minus_one
    }

    /// A field element is defined to be negative if it is odd after doubling.
    fn is_negative(&self) -> bool {
        self.double().is_odd().into()
    }

    /// This function does not check that the resulting version and field
    /// match the trait constants
    fn from_tag_unchecked(tag: Tag) -> Self {
        Self::from_u64(tag.into())
    }

    fn from_tag(tag: Tag) -> Option<Self> {
        if tag.version == Self::VERSION && tag.field == Self::FIELD_KIND {
            Some(Self::from_u64(tag.into()))
        } else {
            None
        }
    }

    fn from_tag_kind(tag: TagKind) -> Self {
        let tag = Tag {
            version: Self::VERSION,
            field: Self::FIELD_KIND,
            tag,
        };
        Self::from_u64(tag.into())
    }

    fn from_expr_tag(tag: ExprTag) -> Self {
        let tag = Tag {
            version: Self::VERSION,
            field: Self::FIELD_KIND,
            tag: TagKind::Expr(tag),
        };
        Self::from_u64(tag.into())
    }

    fn from_cont_tag(tag: ContTag) -> Self {
        let tag = Tag {
            version: Self::VERSION,
            field: Self::FIELD_KIND,
            tag: TagKind::Cont(tag),
        };
        Self::from_u64(tag.into())
    }

    fn from_op1_tag(tag: Op1Tag) -> Self {
        let tag = Tag {
            version: Self::VERSION,
            field: Self::FIELD_KIND,
            tag: TagKind::Op1(tag),
        };
        Self::from_u64(tag.into())
    }

    fn from_op2_tag(tag: Op2Tag) -> Self {
        let tag = Tag {
            version: Self::VERSION,
            field: Self::FIELD_KIND,
            tag: TagKind::Op2(tag),
        };
        Self::from_u64(tag.into())
    }

    fn to_tag(&self) -> Option<Tag> {
        let x = Self::to_u64(self)?;
        Tag::try_from(x).ok()
    }

    fn get_version(&self) -> Option<Version> {
        Some(Self::to_tag(self)?.version)
    }

    fn get_tag_kind(&self) -> Option<TagKind> {
        Some(Self::to_tag(self)?.tag)
    }

    fn get_field_kind(&self) -> Option<FieldKind> {
        Some(Self::to_tag(self)?.field)
    }
}

impl LurkField for blstrs::Scalar {
    const VERSION: Version = CURRENT_VERSION;
    const FIELD_KIND: FieldKind = FieldKind::BLS12_381;
}

impl LurkField for pasta_curves::Fp {
    const VERSION: Version = CURRENT_VERSION;
    const FIELD_KIND: FieldKind = FieldKind::Pallas;
}

impl LurkField for pasta_curves::Fq {
    const VERSION: Version = CURRENT_VERSION;
    const FIELD_KIND: FieldKind = FieldKind::Vesta;
}

// For working around the orphan trait impl rule
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FWrap<F: LurkField>(pub F);

#[cfg(test)]
mod tests {
    use super::*;
    use blstrs::Scalar as Fr;
    use quickcheck::{Arbitrary, Gen};

    impl<F: LurkField> Arbitrary for FWrap<F> {
        fn arbitrary(_: &mut Gen) -> Self {
            let f = F::random(rand::thread_rng());
            FWrap(f)
        }
    }

    #[quickcheck]
    fn prop_bytes_consistency(f1: FWrap<Fr>) -> bool {
        let bytes = f1.0.to_repr().as_ref().to_owned();
        let f2 = <Fr as LurkField>::from_bytes(&bytes);
        Some(f1.0) == f2
    }

    #[quickcheck]
    fn prop_tag_consistency(x: Tag) -> bool {
        let f1 = Fr::from_tag_unchecked(x);
        let tag = <Fr as LurkField>::to_tag(&f1).unwrap();
        let f2 = Fr::from_tag_unchecked(tag);
        f1 == f2 && x == tag
    }
}
