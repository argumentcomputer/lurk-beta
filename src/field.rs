use ff::{PrimeField, PrimeFieldBits};
use libipld::cid::Cid;
use serde::{Deserialize, Serialize};
use std::hash::Hash;

use multihash::Multihash;

pub enum LanguageField {
    Pallas,
    Vesta,
    BLS12_381,
}

pub trait LurkField: PrimeField + PrimeFieldBits {
    const HASH_MULTICODEC: u64;
    const LURK_MULTICODEC: u64 = 0x10de;

    fn from_bytes(bs: &[u8]) -> Option<Self> {
        let mut def: Self::Repr = Self::default().to_repr();
        def.as_mut().copy_from_slice(bs);
        Self::from_repr(def).into()
    }
    fn from_bytes2(bs: &[u8]) -> Option<(Self, Self)> {
        let l = bs.len() / 2;
        let (tag_bytes, dig_bytes) = bs.split_at(l);
        Some((Self::from_bytes(tag_bytes)?, Self::from_bytes(dig_bytes)?))
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
    fn to_char(&self) -> Option<char> {
        self.to_u32().and_then(char::from_u32)
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

    // TODO: Use commitments
    fn to_multihash(tag: Self, dig: Self) -> Multihash {
        Multihash::wrap(
            0x00,
            &[tag.to_repr().as_ref(), dig.to_repr().as_ref()].concat(),
        )
        .unwrap()
    }

    fn from_multihash(hash: Multihash) -> Option<(Self, Self)> {
        Self::from_bytes2(hash.digest())
    }

    fn to_cid(tag: Self, dig: Self) -> Option<Cid> {
        Some(Cid::new_v1(
            Self::LURK_MULTICODEC,
            Self::to_multihash(tag, dig),
        ))
    }
    fn from_cid(cid: Cid) -> Option<(Self, Self)> {
        let (tag, dig) = Self::from_multihash(*cid.hash())?;
        Some((tag, dig))
    }
}

// TODO: Use real multihash codecs here
impl LurkField for blstrs::Scalar {
    const HASH_MULTICODEC: u64 = 2;
}

impl LurkField for pasta_curves::Fq {
    const HASH_MULTICODEC: u64 = 3;
}

impl LurkField for pasta_curves::Fp {
    const HASH_MULTICODEC: u64 = 3;
}

// For working around the orphan trait impl rule
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FWrap<F: LurkField>(pub F);

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

#[allow(clippy::derive_hash_xor_eq)]
impl<F: LurkField> Hash for FWrap<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_repr().as_ref().hash(state);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    //use blstrs::Scalar as Fr;

    //use crate::store::Tag;
    use quickcheck::{Arbitrary, Gen};

    impl<F: LurkField> Arbitrary for FWrap<F> {
        fn arbitrary(_: &mut Gen) -> Self {
            let f = F::random(rand::thread_rng());
            FWrap(f)
        }
    }

    //#[quickcheck]
    //fn test_bytes_consistency(f1: FWrap<Fr>) -> bool {
    //    let bytes = f1.0.to_repr().as_ref().to_owned();
    //    let f2 = <Fr as LurkField>::from_bytes(&bytes);
    //    Some(f1.0) == f2
    //}

    //#[quickcheck]
    //fn test_tag_consistency(x: Tag) -> bool {
    //    let f1 = Fr::from(x as u64);
    //    let tag = <Fr as LurkField>::to_tag(f1).unwrap();
    //    let f2 = Fr::from(tag as u64);
    //    f1 == f2 && x as u32 == tag
    //}

    //#[quickcheck]
    //fn test_multicodec_consistency(x: Tag) -> bool {
    //    let f1 = Fr::from(x as u64);
    //    let codec = <Fr as LurkField>::to_multicodec(f1).unwrap();
    //    let f2 = <Fr as LurkField>::from_multicodec(codec);
    //    println!("x: {:?}", x);
    //    println!("f1: {}", f1);
    //    println!("codec: {:0x}", codec);
    //    println!("f2: {}", f1);
    //    Some(f1) == f2
    //}
    //#[quickcheck]
    //fn test_multihash_consistency(f1: FWrap<Fr>) -> bool {
    //    let hash = <Fr as LurkField>::to_multihash(f1.0);
    //    let f2 = <Fr as LurkField>::from_multihash(hash);
    //    Some(f1.0) == f2
    //}
    //#[quickcheck]
    //fn test_cid_consistency(args: (Tag, FWrap<Fr>)) -> bool {
    //    let (tag1, dig1) = args;
    //    let cid = <Fr as LurkField>::to_cid(Fr::from(tag1 as u64), dig1.0).unwrap();
    //    if let Some((tag2, dig2)) = <Fr as LurkField>::from_cid(cid) {
    //        Fr::from(tag1 as u64) == tag2 && dig1.0 == dig2
    //    } else {
    //        false
    //    }
    //}
}
