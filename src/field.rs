use anyhow::anyhow;
use ff::{PrimeField, PrimeFieldBits};
use serde::{Deserialize, Serialize};
use std::convert::TryFrom;
use std::hash::Hash;

use crate::light_data::Encodable;
use crate::light_data::LightData;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use rand::{rngs::StdRng, SeedableRng};

use crate::tag::{ContTag, ExprTag, Op1, Op2};

/// The type of finite fields used in the language
pub enum LanguageField {
    Pallas,
    Vesta,
    BLS12_381,
}

/// Trait implemented by finite fields used in the language
pub trait LurkField: PrimeField + PrimeFieldBits {
    const FIELD: LanguageField;

    /// Converts the field element to a byte vector
    fn to_bytes(self) -> Vec<u8> {
        let repr = self.to_repr();
        repr.as_ref().to_vec()
    }
    /// Attempts to construct a field element from a byte slice
    fn from_bytes(bs: &[u8]) -> Option<Self> {
        let mut def: Self::Repr = Self::default().to_repr();
        def.as_mut().copy_from_slice(bs);
        Self::from_repr(def).into()
    }

    /// Converts the field element to a hexadecimal string
    fn hex_digits(self) -> String {
        let bytes = self.to_bytes();
        let mut s = String::with_capacity(bytes.len() * 2);
        for b in bytes.iter().rev() {
            s.push_str(&format!("{:02x?}", b));
        }
        s
    }

    /// Converts the field to a variable-length hex string
    fn trimmed_hex_digits(self) -> String {
        let hex_digits = self.hex_digits();
        let mut res = hex_digits.trim_start_matches('0');
        if res.is_empty() {
            res = "0";
        }
        res.to_owned()
    }

    /// Attempts to convert the field element to a u16
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

    /// Attempts to convert the field element to a u32
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

    /// Attempts to convert the field element to a char
    fn to_char(&self) -> Option<char> {
        let x = self.to_u32()?;
        char::from_u32(x)
    }

    /// Attempts to convert the field element to a u64
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

    /// Converts the first 4 bytes of the field element to a u32
    fn to_u32_unchecked(&self) -> u32 {
        let mut byte_array = [0u8; 4];
        byte_array.copy_from_slice(&self.to_repr().as_ref()[0..4]);
        u32::from_le_bytes(byte_array)
    }

    /// Converts the first 8 bytes of the field element to a u64
    fn to_u64_unchecked(&self) -> u64 {
        let mut byte_array = [0u8; 8];
        byte_array.copy_from_slice(&self.to_repr().as_ref()[0..8]);
        u64::from_le_bytes(byte_array)
    }

    /// Constructs a field element from a u64
    fn from_u64(x: u64) -> Self {
        x.into()
    }

    /// Constructs a field element from a u32
    fn from_u32(x: u32) -> Self {
        (x as u64).into()
    }
    /// Constructs a field element from a u16
    fn from_u16(x: u16) -> Self {
        (x as u64).into()
    }
    /// Constructs a field element from a char
    fn from_char(x: char) -> Self {
        Self::from_u32(x as u32)
    }

    /// We define this to be the smallest negative field element
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

    /// Constructs a field element from an ExprTag
    fn from_expr_tag(tag: ExprTag) -> Self {
        Self::from_u64(tag.into())
    }
    /// Attempts to convert the field element to an ExprTag
    fn to_expr_tag(&self) -> Option<ExprTag> {
        let x = Self::to_u16(self)?;
        ExprTag::try_from(x).ok()
    }

    /// Constructs a field element from a ContTag
    fn from_cont_tag(tag: ContTag) -> Self {
        Self::from_u64(tag.into())
    }

    /// Attempts to convert the field element to a ContTag
    fn to_cont_tag(&self) -> Option<ContTag> {
        let x = Self::to_u16(self)?;
        ContTag::try_from(x).ok()
    }
    /// Constructs a field element from an Op1
    fn from_op1(tag: Op1) -> Self {
        Self::from_u64(tag.into())
    }

    /// Attempts to convert the field element to an Op1
    fn to_op1(&self) -> Option<Op1> {
        let x = Self::to_u16(self)?;
        Op1::try_from(x).ok()
    }
    /// Constructs a field element from an Op2
    fn from_op2(tag: Op2) -> Self {
        Self::from_u64(tag.into())
    }

    /// Attempts to convert the field element to an Op2
    fn to_op2(&self) -> Option<Op2> {
        let x = Self::to_u16(self)?;
        Op2::try_from(x).ok()
    }

    /// Returns the LanguageField of the field
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
/// Wrapper struct around a field element that implements additional traits
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FWrap<F: LurkField>(pub F);

impl<F: LurkField> Copy for FWrap<F> {}

#[cfg(not(target_arch = "wasm32"))]
/// Trait implementation for generating FWrap<F> instances with proptest
impl<F: LurkField> Arbitrary for FWrap<F> {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        let strategy = any::<[u8; 32]>()
            .prop_map(|seed| FWrap(F::random(StdRng::from_seed(seed))))
            .no_shrink();
        strategy.boxed()
    }
}

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

const fn bytes_size<F: LurkField>() -> usize {
    F::NUM_BITS as usize / 8 + (F::NUM_BITS % 8 != 0) as usize
}

impl<F: LurkField> Encodable for FWrap<F> {
    // Beware, this assumes a little endian encoding
    fn ser(&self) -> LightData {
        let bytes: Vec<u8> = Vec::from(self.0.to_repr().as_ref());
        let mut trimmed_bytes: Vec<_> = bytes.into_iter().rev().skip_while(|x| *x == 0u8).collect();
        trimmed_bytes.reverse();
        LightData::Atom(trimmed_bytes)
    }

    // beware, this assumes a little endian encoding
    fn de(ld: &LightData) -> anyhow::Result<Self> {
        let bytes = match ld {
            LightData::Atom(bytes) => bytes,
            _ => return Err(anyhow!("expected field element as bytes")),
        };

        if bytes.len() > bytes_size::<F>() {
            return Err(anyhow!(
                "Lurk does not support field representations beyond {} bits, received {:?}",
                F::NUM_BITS,
                bytes
            ));
        }

        // the field element expects a certain Repr length, whereas LightData trims it.
        let mut bytes_slice = F::default().to_repr();
        bytes_slice
            .as_mut()
            .iter_mut()
            .zip(bytes)
            .for_each(|(byte_slice, byte)| *byte_slice = *byte);
        let f: Option<F> = F::from_repr(bytes_slice).into();
        f.map(FWrap)
            .ok_or_else(|| anyhow!("expected field element as bytes, got {:?}", bytes))
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
    use crate::light_data::Encodable;
    use blstrs::Scalar as Fr;

    use super::*;

    fn repr_bytes_consistency<F: LurkField>(f1: FWrap<F>) {
        let bytes = f1.0.to_repr().as_ref().to_owned();
        let f2 = <F as LurkField>::from_bytes(&bytes).expect("from_bytes");
        assert_eq!(f1.0, f2)
    }

    proptest! {
      #[test]
      fn prop_bls_repr_bytes_consistency(f1 in any::<FWrap<Fr>>()) {
        repr_bytes_consistency(f1)
      }
      #[test]
      fn prop_pallas_repr_bytes_consistency(f1 in any::<FWrap<pasta_curves::Fp>>()) {
          repr_bytes_consistency(f1)
      }
      #[test]
      fn prop_vesta_repr_bytes_consistency(f1 in any::<FWrap<pasta_curves::Fq>>()) {
          repr_bytes_consistency(f1)
      }
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

    fn repr_canonicity<F: LurkField>(f1: FWrap<F>) {
        let repr_bytes = f1.0.to_bytes();
        let canonical_bytes = to_le_bytes_canonical(f1.0);
        let f2_repr = F::from_bytes(&repr_bytes).expect("from_bytes");
        let f2_canonical = from_le_bytes_canonical::<F>(&canonical_bytes);
        assert_eq!(repr_bytes, canonical_bytes);
        assert_eq!(f2_repr, f2_canonical)
    }

    proptest! {
      #[test]
      fn prop_repr_canonicity(f1 in any::<FWrap<Fr>>()) {
        repr_canonicity(f1)
      }
      #[test]
      fn prop_pallas_repr_canonicity(f1 in any::<FWrap<pasta_curves::Fp>>()) {
          repr_canonicity(f1)
      }
      #[test]
      fn prop_vesta_repr_canonicity(f1 in any::<FWrap<pasta_curves::Fq>>()) {
          repr_canonicity(f1)
      }
      #[test]
      fn prop_tag_consistency(x in any::<ExprTag>()) {
          let f1 = Fr::from_expr_tag(x);
          let tag = <Fr as LurkField>::to_expr_tag(&f1).unwrap();
          let f2 = Fr::from_expr_tag(tag);
          assert_eq!(f1, f2);
          assert_eq!(x, tag)
      }

      #[test]
      fn prop_encode_decode(x in any::<FWrap<Fr>>()) {
            let bytes = x.ser();
            let f2 = FWrap::de(&bytes).unwrap();
            assert_eq!(x, f2)
      }
    }

    // This checks that the field we're using have a representation
    // such that forall x: u64, F::from(x).to_repr() == x.to_le_bytes()
    // This enables a fast conversion for tags, and must be present for all fields
    // we use this library with.
    proptest! {
        #[test]
        fn prop_pallas_tag_roundtrip(x in any::<u64>()){
            let f1 = pasta_curves::Fp::from(x);
            let bytes = f1.to_repr().as_ref().to_vec();
            let mut bytes_from_u64 = [0u8; 32];
            bytes_from_u64[..8].copy_from_slice(&x.to_le_bytes());
            assert_eq!(bytes, bytes_from_u64);
        }

        #[test]
        fn prop_vesta_tag_roundtrip(x in any::<u64>()){
            let f1 = pasta_curves::Fq::from(x);
            let bytes = f1.to_repr().as_ref().to_vec();
            let mut bytes_from_u64 = [0u8; 32];
            bytes_from_u64[..8].copy_from_slice(&x.to_le_bytes());
            assert_eq!(bytes, bytes_from_u64);
        }

        #[test]
        fn prop_bls_tag_roundtrip(x in any::<u64>()){
            let f1 = blstrs::Scalar::from(x);
            let bytes = f1.to_repr().as_ref().to_vec();
            let mut bytes_from_u64 = [0u8; 32];
            bytes_from_u64[..8].copy_from_slice(&x.to_le_bytes());
            assert_eq!(bytes, bytes_from_u64);
        }
    }
}
