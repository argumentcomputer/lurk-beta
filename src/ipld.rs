use alloc::vec::Vec;
use core::convert::TryInto;
use core::num::TryFromIntError;

use num_bigint::BigUint;

use multihash::Code;
use multihash::MultihashDigest;
use multihash::MultihashGeneric;

use libipld::cbor::DagCborCodec;
use libipld::codec::Codec;
use libipld::Cid;
use libipld::Ipld;

use crate::scalar_store::ScalarExpression;
use crate::store::ContTag;
use crate::store::ScalarContPtr;
use crate::store::ScalarPtr;
use crate::store::Tag;
use ff::PrimeField;

pub const DAGCBOR: u64 = 0x71;

// In future, we want to make a cid version that can have multicodec fields
// larger than u64, so we can reserve a whole tree for future Lurk use
pub const LURK_CODEC_PREFIX: u16 = 0xc0de;

pub const NUM: u16 = 0x01;
pub const EXPR: u16 = 0x02;

// temporary hack standing in for a future extension of the `ff` trait so that
// every field `F` is entered on the `multicodec` table
pub fn dummy_ff_codec<F: PrimeField>() -> u16 {
    0xbe_ff
}

// We are assuming that our tags fit in the 32 least significant bits of the `F`
pub fn f_tag_to_u32<F: ff::PrimeField>(f: F, le: bool) -> u32 {
    let bytes: Vec<u8> = f.to_repr().as_ref().to_vec();
    if le {
        let size = bytes.len();
        let bytes: [u8; 4] = [
            bytes[size],
            bytes[size - 1],
            bytes[size - 2],
            bytes[size - 3],
        ];
        u32::from_le_bytes(bytes)
    } else {
        let bytes: [u8; 4] = [bytes[0], bytes[1], bytes[2], bytes[3]];
        u32::from_be_bytes(bytes)
    }
}

// this assumes we only use poseidon-bls12_381-a2-fc1, or multicodec 0xb401
// also assumes that F fits within a 512 bit digest
pub fn f_digest<F: ff::PrimeField>(f: F) -> MultihashGeneric<64> {
    MultihashGeneric::wrap(0xb401, f.to_repr().as_ref()).unwrap()
}

// this should be a trait method on ff, or PrimeField::Repr should be readable
// from &[u8]
pub fn ff_from_bytes_vartime<F: ff::PrimeField>(bs: &[u8]) -> Option<F> {
    if bs.is_empty() {
        return None;
    }
    let mut res = F::zero();

    let _256 = F::from(256);

    for b in bs {
        res.mul_assign(&_256);
        res.add_assign(&F::from(u64::from(*b)));
    }
    Some(res)
}

pub fn make_codec<F: PrimeField>(tag: u32) -> u64 {
    u64::from(LURK_CODEC_PREFIX) << 48 & u64::from(dummy_ff_codec::<F>()) << 32 & u64::from(tag)
}

pub trait IpldEmbed: Sized {
    fn to_ipld(&self) -> Ipld;
    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError>;
}

// assume that `F` fits within
pub fn cid(code: u64, ipld: &Ipld) -> Cid {
    Cid::new_v1(
        code,
        Code::Blake3_256.digest(DagCborCodec.encode(ipld).unwrap().as_ref()),
    )
}

#[derive(PartialEq, Debug, Clone)]
pub enum IpldError {
    Utf8(Vec<u8>, alloc::string::FromUtf8Error),
    ByteCount(Vec<u8>, u64),
    UnicodeChar(u32),
    U64(TryFromIntError),
    U32(TryFromIntError),
    Expected(String, Ipld),
}

impl IpldError {
    pub fn expected(s: &str, ipld: &Ipld) -> IpldError {
        IpldError::Expected(String::from(s), ipld.clone())
    }
}

impl IpldEmbed for Cid {
    fn to_ipld(&self) -> Ipld {
        Ipld::Link(*self)
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        match ipld {
            Ipld::Link(x) => Ok(*x),
            xs => Err(IpldError::Expected(String::from("cid"), xs.clone())),
        }
    }
}

impl IpldEmbed for bool {
    fn to_ipld(&self) -> Ipld {
        Ipld::Bool(*self)
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        match ipld {
            Ipld::Bool(x) => Ok(*x),
            xs => Err(IpldError::Expected(String::from("bool"), xs.clone())),
        }
    }
}

impl IpldEmbed for String {
    fn to_ipld(&self) -> Ipld {
        Ipld::String(self.clone())
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        match ipld {
            Ipld::String(s) => Ok(s.clone()),
            xs => Err(IpldError::Expected(String::from("String"), xs.clone())),
        }
    }
}

impl IpldEmbed for u32 {
    fn to_ipld(&self) -> Ipld {
        Ipld::Integer(*self as i128)
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        match ipld {
            Ipld::Integer(x) => {
                let x = (*x).try_into().map_err(IpldError::U32)?;
                Ok(x)
            }
            xs => Err(IpldError::expected("u32", xs)),
        }
    }
}

impl IpldEmbed for u64 {
    fn to_ipld(&self) -> Ipld {
        Ipld::Integer(*self as i128)
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        match ipld {
            Ipld::Integer(x) => {
                let x = (*x).try_into().map_err(IpldError::U64)?;
                Ok(x)
            }
            xs => Err(IpldError::expected("u64", xs)),
        }
    }
}

impl IpldEmbed for BigUint {
    fn to_ipld(&self) -> Ipld {
        Ipld::Bytes(self.to_bytes_be())
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        match ipld {
            Ipld::Bytes(bs) => Ok(BigUint::from_bytes_be(bs)),
            xs => Err(IpldError::Expected(String::from("BigUint"), xs.clone())),
        }
    }
}

// needed to avoid trait overlap with Cid
pub struct FWrap<F: PrimeField>(pub F);

impl<F: PrimeField> IpldEmbed for FWrap<F> {
    fn to_ipld(&self) -> Ipld {
        let bytes: Vec<u8> = self.0.to_repr().as_ref().to_owned();
        Ipld::Bytes(bytes)
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        match ipld {
            Ipld::Bytes(bs) => {
                let f = ff_from_bytes_vartime(&bs).ok_or(IpldError::expected(
                    "non-empty bytes",
                    &Ipld::Bytes(bs.clone()),
                ))?;
                Ok(FWrap(f))
            }
            xs => Err(IpldError::expected("PrimeField", xs)),
        }
    }
}

impl<T: IpldEmbed> IpldEmbed for Vec<T> {
    fn to_ipld(&self) -> Ipld {
        Ipld::List(self.iter().map(|x| x.to_ipld()).collect())
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        let mut ys = Vec::new();
        match ipld {
            Ipld::List(xs) => {
                for x in xs {
                    let y = T::from_ipld(x)?;
                    ys.push(y);
                }
                Ok(ys)
            }
            xs => Err(IpldError::expected("List", xs)),
        }
    }
}

impl<A: IpldEmbed, B: IpldEmbed> IpldEmbed for (A, B) {
    fn to_ipld(&self) -> Ipld {
        Ipld::List([self.0.to_ipld(), self.1.to_ipld()].into())
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        match ipld {
            Ipld::List(xs) => match xs.as_slice() {
                [a, b] => {
                    let a = A::from_ipld(a)?;
                    let b = B::from_ipld(b)?;
                    Ok((a, b))
                }
                xs => Err(IpldError::expected("Pair", &Ipld::List(xs.to_owned()))),
            },
            xs => Err(IpldError::expected("Pair", xs)),
        }
    }
}

impl<T: IpldEmbed> IpldEmbed for Option<T> {
    fn to_ipld(&self) -> Ipld {
        match self {
            Some(x) => x.to_ipld(),
            None => Ipld::Null,
        }
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        match ipld {
            Ipld::Null => Ok(None),
            x => {
                let x = T::from_ipld(x)?;
                Ok(Some(x))
            }
        }
    }
}

//
