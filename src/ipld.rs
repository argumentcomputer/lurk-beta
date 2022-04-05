use alloc::vec::Vec;
use core::convert::TryInto;
use core::num::TryFromIntError;

use num_bigint::BigUint;

use multihash::Code;
use multihash::MultihashDigest;

use libipld::cbor::DagCborCodec;
use libipld::codec::Codec;
use libipld::Cid;
use libipld::Ipld;

use crate::field::LurkField;

pub const DAGCBOR: u64 = 0x71;

pub trait IpldEmbed: Sized {
    fn to_ipld(&self) -> Ipld;
    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError>;
}

pub fn cbor_cid(code: u64, ipld: &Ipld) -> Cid {
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FWrap<F: LurkField>(pub F);

impl<F: LurkField> IpldEmbed for FWrap<F> {
    fn to_ipld(&self) -> Ipld {
        let bytes: Vec<u8> = self.0.to_repr().as_ref().to_owned();
        Ipld::Bytes(bytes)
    }

    fn from_ipld(ipld: &Ipld) -> Result<Self, IpldError> {
        match ipld {
            Ipld::Bytes(bs) => {
                let f = F::from_bytes(bs).ok_or_else(|| {
                    IpldError::expected("non-empty bytes", &Ipld::Bytes(bs.clone()))
                })?;
                Ok(FWrap(f))
            }
            xs => Err(IpldError::expected("LurkField", xs)),
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

#[cfg(test)]
mod test {
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
    fn test_fwrap_ipld_embed(x: FWrap<Fr>) -> bool {
        match FWrap::from_ipld(&x.to_ipld()) {
            Ok(y) if x == y => true,
            Ok(y) => {
                println!("x: {:?}", x);
                println!("y: {:?}", y);
                false
            }
            Err(e) => {
                println!("{:?}", x);
                println!("{:?}", e);
                false
            }
        }
    }
}
