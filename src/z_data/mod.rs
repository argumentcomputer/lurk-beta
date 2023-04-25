//#![deny(missing_docs)]
//! `ZData` is a lightweight binary data serialization format.
//!
//! A `ZData` value is a n-ary tree with two types of nodes:
//!
//! - Atom: a leaf node containing a byte sequence
//! - Cell: an interior node containing an arbitrary number of child nodes
//!
//! `ZData` values are encoded as a sequence of bytes in a compact binary format.
//!
//! This module also provides several traits that can be used to encode and decode Rust types into
//! `ZData` values.

use anyhow::Result;
use std::fmt::Display;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;

use anyhow::anyhow;
use nom::bytes::complete::take;
use nom::multi::count;
use nom::Finish;
use nom::IResult;

mod z_cont;
mod z_expr;
mod z_ptr;
mod z_store;

pub use z_cont::ZCont;
pub use z_expr::ZExpr;
pub use z_ptr::{ZContPtr, ZExprPtr, ZPtr};
pub use z_store::ZStore;

/// `ZData` is a binary tree with two types of nodes: Atom and Cell.
///
/// # Examples
///
/// ```
/// use lurk::light_data::ZData;
///
/// let data = ZData::Cell(vec![
///     ZData::Atom(vec![0x01]),
///     ZData::Atom(vec![0x02, 0x03]),
/// ]);
///
/// assert_eq!(data.to_string(), "[c:[a:01], [a:02, 03]]");
/// ```
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum ZData {
    /// An Atom contains a byte sequence.
    Atom(Vec<u8>),
    /// A Cell contains an arbitrary number of child nodes.
    Cell(Vec<ZData>),
}

impl Display for ZData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        match self {
            Self::Atom(xs) => {
                let xs_str = xs
                    .iter()
                    .map(|x| format!("{:02x?}", x))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "a:{}", xs_str)?;
            }
            Self::Cell(xs) => {
                let xs_str = xs
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "c:{}", xs_str)?;
            }
        }
        write!(f, "]")?;
        Ok(())
    }
}

#[cfg(not(target_arch = "wasm32"))]
impl Arbitrary for ZData {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        let atom = prop::collection::vec(any::<u8>(), 0..256).prop_map(ZData::Atom);
        atom.prop_recursive(16, 1024, 256, |inner| {
            prop::collection::vec(inner, 0..256).prop_map(ZData::Cell)
        })
        .boxed()
    }
}

impl ZData {
    /// Returns the number of bytes required to encode the given integer in little-endian byte order.
    pub fn byte_count(x: usize) -> u8 {
        if x == 0 {
            1
        } else {
            (x.ilog2() / 8 + 1) as u8
        }
    }

    /// Returns the little-endian byte sequence for the given integer, trimmed to the minimum number
    /// of bytes required to represent the integer.
    pub fn to_trimmed_le_bytes(x: usize) -> Vec<u8> {
        x.to_le_bytes()[..Self::byte_count(x) as usize].to_vec()
    }

    /// Returns the `usize` that's represented by a little endian byte array.
    ///
    /// On 32-bit systems, the input must not be longer than 4. On 64-bit systems,
    /// the input size limit is 8.
    pub fn read_size_bytes(xs: &[u8]) -> Option<usize> {
        let len = xs.len();
        const MAX_LEN: usize = std::mem::size_of::<usize>();
        if len > MAX_LEN {
            None
        } else {
            let mut bytes = [0u8; MAX_LEN];
            bytes[..len].copy_from_slice(xs);
            Some(usize::from_le_bytes(bytes))
        }
    }

    /// Returns the tag byte for this `ZData`.
    pub fn tag(&self) -> u8 {
        match self {
            Self::Atom(xs) if xs.is_empty() => 0b0000_0000,
            Self::Atom(xs) if xs.len() < 64 => 0b0100_0000u8 + (xs.len() as u8),
            Self::Atom(xs) if xs.len() == 64 => 0b0100_0000u8,
            Self::Atom(xs) => ZData::byte_count(xs.len()),
            Self::Cell(xs) if xs.is_empty() => 0b1000_0000,
            Self::Cell(xs) if xs.len() < 64 => 0b1100_0000u8 + (xs.len() as u8),
            Self::Cell(xs) if xs.len() == 64 => 0b1100_0000u8,
            Self::Cell(xs) => 0b1000_0000u8 + ZData::byte_count(xs.len()),
        }
    }

    /// Determines if a given tag byte represents an `Atom`.
    pub fn tag_is_atom(x: u8) -> bool {
        x & 0b1000_0000 == 0b0000_0000
    }

    /// Determines if a given tag byte represents a `Cell` with a small number of elements.
    pub fn tag_is_small(x: u8) -> bool {
        x & 0b0100_0000 == 0b0100_0000
    }

    /// Serializes this `ZData` into a `Vec<u8>`.
    pub fn ser(&self) -> Vec<u8> {
        let mut res = vec![];
        res.push(self.tag());
        match self {
            Self::Atom(xs) if xs.is_empty() => {}
            Self::Atom(xs) if xs.len() <= 64 => res.extend(xs),
            Self::Atom(xs) => {
                res.extend(ZData::to_trimmed_le_bytes(xs.len()));
                res.extend(xs);
            }
            Self::Cell(xs) if xs.is_empty() => {}
            Self::Cell(xs) if xs.len() <= 64 => {
                for x in xs {
                    res.extend(x.ser())
                }
            }
            Self::Cell(xs) => {
                res.extend(ZData::to_trimmed_le_bytes(xs.len()));
                for x in xs {
                    res.extend(x.ser())
                }
            }
        };
        res
    }

    /// Deserializes a `ZData` from a `&[u8]`.
    ///
    /// # Errors
    ///
    /// This function errors if the input bytes don't correspond to a valid serialization of ZData
    pub fn de(i: &[u8]) -> anyhow::Result<Self> {
        match Self::de_aux(i).finish() {
            Ok((_, x)) => Ok(x),
            Err(e) => Err(anyhow!("Error parsing light data: {:?}", e)),
        }
    }

    #[inline]
    fn de_aux(i: &[u8]) -> IResult<&[u8], Self> {
        let (i, tag) = take(1u8)(i)?;
        let tag = tag[0];
        let size = tag & 0b11_1111;

        let (i, size) = if Self::tag_is_small(tag) {
            match size {
                0 => (i, 64),
                _ => (i, size as usize),
            }
        } else {
            let (i, bytes) = take(size)(i)?;
            match ZData::read_size_bytes(bytes) {
                Some(size) => Ok((i, size)),
                None => Err(nom::Err::Error(nom::error::Error::new(
                    i,
                    nom::error::ErrorKind::LengthValue,
                ))),
            }?
        };

        let (i, res) = if Self::tag_is_atom(tag) {
            let (i, data) = take(size)(i)?;
            (i, ZData::Atom(data.to_vec()))
        } else {
            let (i, xs) = count(ZData::de_aux, size)(i)?;
            (i, ZData::Cell(xs.to_vec()))
        };

        Ok((i, res))
    }
}

/// A trait for types that can be serialized and deserialized using `ZData`.
pub trait Encodable {
    /// Serializes this value into a `ZData`.
    fn ser(&self) -> ZData;
    /// Deserializes a `ZData` into this value.
    fn de(ld: &ZData) -> Result<Self>
    where
        Self: Sized;
}

impl Encodable for u64 {
    fn ser(&self) -> ZData {
        ZData::Atom(u64::to_le_bytes(*self).to_vec())
    }

    fn de(ld: &ZData) -> Result<Self> {
        match ld {
            ZData::Atom(x) => match x.as_slice().try_into() {
                Ok(a) => Ok(u64::from_le_bytes(a)),
                Err(_) => anyhow::bail!("expected u64"),
            },
            ZData::Cell(_) => anyhow::bail!("expected u64"),
        }
    }
}

impl Encodable for u32 {
    fn ser(&self) -> ZData {
        ZData::Atom(u32::to_le_bytes(*self).to_vec())
    }
    fn de(ld: &ZData) -> Result<Self> {
        match ld {
            ZData::Atom(x) => match x.as_slice().try_into() {
                Ok(a) => Ok(u32::from_le_bytes(a)),
                Err(_) => anyhow::bail!("expected u32"),
            },
            ZData::Cell(_) => anyhow::bail!("expected u32"),
        }
    }
}

impl Encodable for char {
    fn ser(&self) -> ZData {
        ((*self) as u32).ser()
    }

    fn de(ld: &ZData) -> Result<Self> {
        match char::from_u32(u32::de(ld)?) {
            Some(x) => Ok(x),
            None => anyhow::bail!("expected char"),
        }
    }
}

impl<A: Encodable + Sized> Encodable for Option<A> {
    fn ser(&self) -> ZData {
        match self {
            None => ZData::Atom(vec![]),
            Some(a) => ZData::Cell(vec![a.ser()]),
        }
    }

    fn de(ld: &ZData) -> Result<Self> {
        match ld {
            ZData::Atom(x) => match x.as_slice() {
                [] => Ok(Option::None),
                _ => anyhow::bail!("expected Option"),
            },
            ZData::Cell(xs) => match xs.as_slice() {
                [a] => Ok(Option::Some(A::de(a)?)),
                _ => anyhow::bail!("expected Option"),
            },
        }
    }
}

impl<A: Encodable + Sized> Encodable for Vec<A> {
    fn ser(&self) -> ZData {
        ZData::Cell(self.iter().map(|x| x.ser()).collect())
    }

    fn de(ld: &ZData) -> Result<Self> {
        match ld {
            ZData::Cell(xs) => xs.iter().map(|x| A::de(x)).collect(),
            _ => anyhow::bail!("expected Vec"),
        }
    }
}

impl<A: Encodable + Sized, B: Encodable + Sized> Encodable for (A, B) {
    fn ser(&self) -> ZData {
        ZData::Cell(vec![self.0.ser(), self.1.ser()])
    }

    fn de(ld: &ZData) -> Result<Self> {
        match ld {
            ZData::Cell(xs) => match xs.as_slice() {
                [x, y] => Ok((A::de(x)?, B::de(y)?)),
                _ => anyhow::bail!("expected pair"),
            },
            _ => anyhow::bail!("expected pair"),
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    #[test]
    fn unit_byte_count() {
        assert_eq!(ZData::byte_count(0), 1);
        assert_eq!(ZData::byte_count(65), 1);
        assert_eq!(ZData::byte_count(256), 2);
        assert_eq!(ZData::byte_count(u16::MAX as usize), 2);
        if usize::BITS >= 32 {
            assert_eq!(ZData::byte_count(u32::MAX as usize), 4);
        }
        if usize::BITS >= 64 {
            assert_eq!(ZData::byte_count(u64::MAX as usize), 8);
        }
    }

    #[test]
    fn unit_trimmed_bytes() {
        assert_eq!(ZData::to_trimmed_le_bytes(43411), vec![147, 169]);
        assert_eq!(43411, ZData::read_size_bytes(&vec![147, 169]).unwrap());
        assert_eq!(ZData::to_trimmed_le_bytes(37801), vec![169, 147]);
        assert_eq!(37801, ZData::read_size_bytes(&vec![169, 147]).unwrap());
    }

    #[test]
    fn unit_light_data() {
        let test = |ld: ZData, xs: Vec<u8>| {
            println!("{:?}", ld.ser());
            let ser = ld.ser();
            assert_eq!(ser, xs);
            println!("{:?}", ZData::de(&ser));
            assert_eq!(ld, ZData::de(&ser).expect("valid lightdata"))
        };
        test(ZData::Atom(vec![]), vec![0b0000_0000]);
        test(ZData::Cell(vec![]), vec![0b1000_0000]);
        test(ZData::Atom(vec![0]), vec![0b0100_0001, 0]);
        test(ZData::Atom(vec![1]), vec![0b0100_0001, 1]);
        test(
            ZData::Cell(vec![ZData::Atom(vec![1])]),
            vec![0b1100_0001, 0b0100_0001, 1],
        );
        test(
            ZData::Cell(vec![ZData::Atom(vec![1]), ZData::Atom(vec![1])]),
            vec![0b1100_0010, 0b0100_0001, 1, 0b0100_0001, 1],
        );
        #[rustfmt::skip]
        test(
            ZData::Atom(vec![
                0, 0, 0, 0, 0, 0, 0, 0, 
                0, 0, 0, 0, 0, 0, 0, 0, 
                0, 0, 0, 69, 96, 43, 67, 
                4, 224, 2, 148, 222, 23, 85, 212, 
                43, 182, 14, 90, 138, 62, 151, 68, 
                207, 128, 70, 44, 70, 31, 155, 81, 
                19, 21, 219, 228, 40, 235, 21, 137, 
                238, 250, 180, 50, 118, 244, 44, 84,
                75, 185,
            ]),
            vec![0b0000_0001, 65,
                0, 0, 0, 0, 0, 0, 0, 0, 
                0, 0, 0, 0, 0, 0, 0, 0, 
                0, 0, 0, 69, 96, 43, 67, 
                4, 224, 2, 148, 222, 23, 85, 212, 
                43, 182, 14, 90, 138, 62, 151, 68, 
                207, 128, 70, 44, 70, 31, 155, 81, 
                19, 21, 219, 228, 40, 235, 21, 137, 
                238, 250, 180, 50, 118, 244, 44, 84,
                75, 185,
            ],
        );
    }

    proptest! {
        #[test]
        fn prop_z_data(x in any::<ZData>()) {
            let ser = x.ser();
            let de  = ZData::de(&ser).expect("read ZData");
            eprintln!("x {}", x);
            eprintln!("ser {:?}", ser);
            assert_eq!(x, de)
        }
    }
}
