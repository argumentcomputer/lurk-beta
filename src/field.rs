use std::convert::TryFrom;
use std::hash::Hash;

use ff::{PrimeField, PrimeFieldBits};
use serde::{Deserialize, Serialize};

use crate::tag::{ContTag, ExprTag, Op1, Op2};

pub enum LanguageField {
    Pallas,
    Vesta,
    BLS12_381,
}

pub trait LurkField: PrimeField + PrimeFieldBits {
    const FIELD: LanguageField;

    fn to_bytes(self) -> Vec<u8> {
        let repr = self.to_repr();
        repr.as_ref().to_vec()
    }
    fn from_bytes(bs: &[u8]) -> Option<Self> {
        let mut def: Self::Repr = Self::default().to_repr();
        def.as_mut().copy_from_slice(bs);
        Self::from_repr(def).into()
    }

    fn hex_digits(self) -> String {
        let mut s = String::new();
        let bytes = self.to_bytes();
        for b in bytes.iter().rev() {
            s.push_str(&format!("{:02x?}", b));
        }
        s
    }

    fn vec_f_to_bytes(vec_f: Vec<Self>) -> Vec<u8> {
        let mut vec = vec![];
        for f in vec_f {
            for byte in f.to_bytes() {
                vec.push(byte)
            }
        }
        vec
    }

    fn vec_f_from_bytes(vec: &[u8]) -> Option<Vec<Self>> {
        let num_bytes: usize = (Self::NUM_BITS / 8 + 1) as usize;
        let mut vec_f: Vec<Self> = vec![];
        for chunk in vec.chunks(num_bytes) {
            let f: Self = Self::from_bytes(chunk)?;
            vec_f.push(f);
        }
        Some(vec_f)
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

    fn to_u32_unchecked(&self) -> u32 {
        let mut byte_array = [0u8; 4];
        byte_array.copy_from_slice(&self.to_repr().as_ref()[0..4]);
        u32::from_le_bytes(byte_array)
    }

    // Return a u64 corresponding to the first 8 little-endian bytes of this field
    // element, discarding the remaining bytes.
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
    fn from_u16(x: u16) -> Self {
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

    fn from_expr_tag(tag: ExprTag) -> Self {
        Self::from_u64(tag.into())
    }
    fn to_expr_tag(&self) -> Option<ExprTag> {
        let x = Self::to_u16(self)?;
        ExprTag::try_from(x).ok()
    }

    fn from_cont_tag(tag: ContTag) -> Self {
        Self::from_u64(tag.into())
    }

    fn to_cont_tag(&self) -> Option<ContTag> {
        let x = Self::to_u16(self)?;
        ContTag::try_from(x).ok()
    }
    fn from_op1(tag: Op1) -> Self {
        Self::from_u64(tag.into())
    }

    fn to_op1(&self) -> Option<Op1> {
        let x = Self::to_u16(self)?;
        Op1::try_from(x).ok()
    }
    fn from_op2(tag: Op2) -> Self {
        Self::from_u64(tag.into())
    }

    fn to_op2(&self) -> Option<Op2> {
        let x = Self::to_u16(self)?;
        Op2::try_from(x).ok()
    }

    fn get_field(&self) -> LanguageField {
        Self::FIELD
    }
}

impl LurkField for blstrs::Scalar {
    const FIELD: LanguageField = LanguageField::BLS12_381;
}

impl LurkField for pasta_curves::Fp {
    const FIELD: LanguageField = LanguageField::Pallas;
}

impl LurkField for pasta_curves::Fq {
    const FIELD: LanguageField = LanguageField::Vesta;
}

// For working around the orphan trait impl rule
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FWrap<F: LurkField>(pub F);

impl<F: LurkField> Copy for FWrap<F> {}

#[allow(clippy::derive_hash_xor_eq)]
impl<F: LurkField> Hash for FWrap<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_repr().as_ref().hash(state);
    }
}

impl<F: LurkField> PartialOrd for FWrap<F> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        (self.0.to_repr().as_ref()).partial_cmp(other.0.to_repr().as_ref())
    }
}

impl<F: LurkField> Ord for FWrap<F> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        (self.0.to_repr().as_ref()).cmp(other.0.to_repr().as_ref())
    }
}

impl<F: LurkField> Serialize for FWrap<F> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let bytes: Vec<u8> = Vec::from(self.0.to_repr().as_ref());
        bytes.serialize(serializer)
    }
}

impl<'de, F: LurkField> Deserialize<'de> for FWrap<F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::Error;
        let bytes: Vec<u8> = Vec::deserialize(deserializer)?;
        let f = F::from_bytes(&bytes).ok_or_else(|| {
            D::Error::custom(format!("expected field element as bytes, got {:?}", &bytes))
        })?;
        Ok(FWrap(f))
    }
}

#[cfg(test)]
pub mod tests {
    use blstrs::Scalar as Fr;

    use super::*;
    use quickcheck::{Arbitrary, Gen};

    impl<F: LurkField> Arbitrary for FWrap<F> {
        fn arbitrary(_: &mut Gen) -> Self {
            let f = F::random(rand::thread_rng());
            FWrap(f)
        }
    }

    // For working around the orphan trait impl rule
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct VecFWrap<F: LurkField>(pub Vec<F>);

    impl<F: LurkField> Arbitrary for VecFWrap<F> {
        fn arbitrary(g: &mut Gen) -> Self {
            let vec_f: Vec<FWrap<F>> = Arbitrary::arbitrary(g);
            VecFWrap(vec_f.into_iter().map(|f| f.0).collect())
        }
    }

    #[quickcheck]
    fn prop_blstrs_repr_bytes_consistency(f1: FWrap<Fr>) -> bool {
        let bytes = f1.0.to_repr().as_ref().to_owned();
        let f2 = <Fr as LurkField>::from_bytes(&bytes);
        Some(f1.0) == f2
    }

    #[quickcheck]
    fn prop_pallas_repr_bytes_consistency(f1: FWrap<pasta_curves::Fp>) -> bool {
        let bytes = f1.0.to_repr().as_ref().to_owned();
        let f2 = <pasta_curves::Fp as LurkField>::from_bytes(&bytes);
        Some(f1.0) == f2
    }

    #[quickcheck]
    fn prop_vesta_repr_bytes_consistency(f1: FWrap<pasta_curves::Fq>) -> bool {
        let bytes = f1.0.to_repr().as_ref().to_owned();
        let f2 = <pasta_curves::Fq as LurkField>::from_bytes(&bytes);
        Some(f1.0) == f2
    }

    // Construct canonical bytes from a field element
    fn to_le_bytes_canonical<F: LurkField>(f: F) -> Vec<u8> {
        let mut vec = vec![];
        let bits = f.to_le_bits();

        let len = bits.len();
        let len_bytes = if len % 8 != 0 { len / 8 + 1 } else { len / 8 };
        for _ in 0..len_bytes {
            vec.push(0u8)
        }
        for (n, b) in bits.into_iter().enumerate() {
            let (byte_i, bit_i) = (n / 8, n % 8);
            if b {
                vec[byte_i] += 1u8 << bit_i;
            }
        }
        vec
    }

    // Construct field element from possibly canonical bytes
    fn from_le_bytes_canonical<F: LurkField>(bs: &[u8]) -> F {
        let mut res = F::zero();
        let mut bs = bs.iter().rev().peekable();
        while let Some(b) = bs.next() {
            let b: F = (*b as u64).into();
            if bs.peek().is_none() {
                res.add_assign(b)
            } else {
                res.add_assign(b);
                res.mul_assign(F::from(256u64));
            }
        }
        res
    }

    #[quickcheck]
    fn prop_blstrs_repr_canonicity(f1: FWrap<Fr>) -> bool {
        let repr_bytes = f1.0.to_bytes();
        let canonical_bytes = to_le_bytes_canonical(f1.0);
        let f2_repr = Fr::from_bytes(&repr_bytes).unwrap();
        let f2_canonical = from_le_bytes_canonical::<Fr>(&canonical_bytes);
        repr_bytes == canonical_bytes && f2_repr == f2_canonical
    }

    #[quickcheck]
    fn prop_pallas_repr_canonicity(f1: FWrap<pasta_curves::Fp>) -> bool {
        let repr_bytes = f1.0.to_bytes();
        let canonical_bytes = to_le_bytes_canonical(f1.0);
        let f2_repr = pasta_curves::Fp::from_bytes(&repr_bytes).unwrap();
        let f2_canonical = from_le_bytes_canonical::<pasta_curves::Fp>(&canonical_bytes);
        repr_bytes == canonical_bytes && f2_repr == f2_canonical
    }

    #[quickcheck]
    fn prop_vesta_repr_canonicity(f1: FWrap<pasta_curves::Fq>) -> bool {
        let repr_bytes = f1.0.to_bytes();
        let canonical_bytes = to_le_bytes_canonical(f1.0);
        let f2_repr = pasta_curves::Fq::from_bytes(&repr_bytes).unwrap();
        let f2_canonical = from_le_bytes_canonical::<pasta_curves::Fq>(&canonical_bytes);
        repr_bytes == canonical_bytes && f2_repr == f2_canonical
    }

    #[quickcheck]
    fn prop_tag_consistency(x: ExprTag) -> bool {
        let f1 = Fr::from_expr_tag(x);
        let tag = <Fr as LurkField>::to_expr_tag(&f1).unwrap();
        let f2 = Fr::from_expr_tag(tag);
        f1 == f2 && x == tag
    }

    #[quickcheck]
    fn prop_vec_f_consistency(vec_f: VecFWrap<Fr>) -> bool {
        let bytes = Fr::vec_f_to_bytes(vec_f.0.clone());
        match Fr::vec_f_from_bytes(&bytes) {
            Some(vec_f2) => vec_f.0 == vec_f2,
            None => false,
        }
    }
}
