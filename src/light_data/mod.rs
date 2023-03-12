#![deny(missing_docs)]
//! `LightData` is a lightweight binary data serialization format.
//!
//! A `LightData` value is a n-ary tree with two types of nodes:
//!
//! - Atom: a leaf node containing a byte sequence
//! - Cell: an interior node containing an arbitrary number of child nodes
//!
//! `LightData` values are encoded as a sequence of bytes in a compact binary format.
//!
//! This module also provides several traits that can be used to encode and decode Rust types into
//! `LightData` values.

use anyhow::Result;
use std::fmt::Display;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;

use anyhow::anyhow;
use nom::bytes::complete::take;
use nom::multi::count;
use nom::Finish;
use nom::IResult;

mod light_store;
pub use light_store::{LightExpr, LightStore};

/// `LightData` is a binary tree with two types of nodes: Atom and Cell.
///
/// # Examples
///
/// ```
/// use lurk::light_data::LightData;
///
/// let data = LightData::Cell(vec![
///     LightData::Atom(vec![0x01]),
///     LightData::Atom(vec![0x02, 0x03]),
/// ]);
///
/// assert_eq!(data.to_string(), "[c:[a:01], [a:02, 03]]");
/// ```
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum LightData {
    /// An Atom contains a byte sequence.
    Atom(Vec<u8>),
    /// A Cell contains an arbitrary number of child nodes.
    Cell(Vec<LightData>),
}

impl Display for LightData {
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
impl Arbitrary for LightData {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        let atom = prop::collection::vec(any::<u8>(), 0..256).prop_map(LightData::Atom);
        atom.prop_recursive(16, 1024, 256, |inner| {
            prop::collection::vec(inner, 0..256).prop_map(LightData::Cell)
        })
        .boxed()
    }
}

impl LightData {
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

    /// Returns the tag byte for this `LightData`.
    pub fn tag(&self) -> u8 {
        match self {
            Self::Atom(xs) if xs.is_empty() => 0b0000_0000,
            Self::Atom(xs) if xs.len() < 64 => 0b0100_0000u8 + (xs.len() as u8),
            Self::Atom(xs) if xs.len() == 64 => 0b0100_0000u8,
            Self::Atom(xs) => LightData::byte_count(xs.len()),
            Self::Cell(xs) if xs.is_empty() => 0b1000_0000,
            Self::Cell(xs) if xs.len() < 64 => 0b1100_0000u8 + (xs.len() as u8),
            Self::Cell(xs) if xs.len() == 64 => 0b1100_0000u8,
            Self::Cell(xs) => 0b1000_0000u8 + LightData::byte_count(xs.len()),
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

    /// Serializes this `LightData` into a `Vec<u8>`.
    pub fn ser(&self) -> Vec<u8> {
        let mut res = vec![];
        res.push(self.tag());
        match self {
            Self::Atom(xs) if xs.is_empty() => {}
            Self::Atom(xs) if xs.len() <= 64 => res.extend(xs),
            Self::Atom(xs) => {
                res.extend(LightData::to_trimmed_le_bytes(xs.len()));
                res.extend(xs);
            }
            Self::Cell(xs) if xs.is_empty() => {}
            Self::Cell(xs) if xs.len() <= 64 => {
                for x in xs {
                    res.extend(x.ser())
                }
            }
            Self::Cell(xs) => {
                res.extend(LightData::to_trimmed_le_bytes(xs.len()));
                for x in xs {
                    res.extend(x.ser())
                }
            }
        };
        res
    }

    /// Deserializes a `LightData` from a `&[u8]`.
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
            let (i, size) = take(size)(i)?;
            let size = size.iter().fold(0, |acc, &x| (acc * 256) + x as usize);
            (i, size)
        };

        let (i, res) = if Self::tag_is_atom(tag) {
            let (i, data) = take(size)(i)?;
            (i, LightData::Atom(data.to_vec()))
        } else {
            let (i, xs) = count(LightData::de_aux, size)(i)?;
            (i, LightData::Cell(xs.to_vec()))
        };

        Ok((i, res))
    }
}

/// A trait for types that can be serialized and deserialized using `LightData`.
pub trait Encodable {
    /// Serializes this value into a `LightData`.
    fn ser(&self) -> LightData;
    /// Deserializes a `LightData` into this value.
    fn de(ld: &LightData) -> Result<Self>
    where
        Self: Sized;
}

impl<A: Encodable + Sized> Encodable for Option<A> {
    fn ser(&self) -> LightData {
        match self {
            None => LightData::Atom(vec![]),
            Some(a) => LightData::Cell(vec![a.ser()]),
        }
    }

    fn de(ld: &LightData) -> Result<Self> {
        match ld {
            LightData::Atom(x) => match x.as_slice() {
                [] => Ok(Option::None),
                _ => anyhow::bail!("expected Option"),
            },
            LightData::Cell(xs) => match xs.as_slice() {
                [a] => Ok(Option::Some(A::de(a)?)),
                _ => anyhow::bail!("expected Option"),
            },
        }
    }
}

impl<A: Encodable + Sized> Encodable for Vec<A> {
    fn ser(&self) -> LightData {
        LightData::Cell(self.iter().map(|x| x.ser()).collect())
    }

    fn de(ld: &LightData) -> Result<Self> {
        match ld {
            LightData::Cell(xs) => xs.iter().map(|x| A::de(x)).collect(),
            _ => anyhow::bail!("expected Vec"),
        }
    }
}

impl<A: Encodable + Sized, B: Encodable + Sized> Encodable for (A, B) {
    fn ser(&self) -> LightData {
        LightData::Cell(vec![self.0.ser(), self.1.ser()])
    }

    fn de(ld: &LightData) -> Result<Self> {
        match ld {
            LightData::Cell(xs) => match xs.as_slice() {
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
        assert_eq!(LightData::byte_count(0), 1);
        assert_eq!(LightData::byte_count(65), 1);
        assert_eq!(LightData::byte_count(256), 2);
        assert_eq!(LightData::byte_count(u16::MAX as usize), 2);
        if usize::BITS >= 32 {
            assert_eq!(LightData::byte_count(u32::MAX as usize), 4);
        }
        if usize::BITS >= 64 {
            assert_eq!(LightData::byte_count(u64::MAX as usize), 8);
        }
    }

    #[test]
    fn unit_light_data() {
        let test = |ld: LightData, xs: Vec<u8>| {
            println!("{:?}", ld.ser());
            let ser = ld.ser();
            assert_eq!(ser, xs);
            println!("{:?}", LightData::de(&ser));
            assert_eq!(ld, LightData::de(&ser).expect("valid lightdata"))
        };
        test(LightData::Atom(vec![]), vec![0b0000_0000]);
        test(LightData::Cell(vec![]), vec![0b1000_0000]);
        test(LightData::Atom(vec![0]), vec![0b0100_0001, 0]);
        test(LightData::Atom(vec![1]), vec![0b0100_0001, 1]);
        test(
            LightData::Cell(vec![LightData::Atom(vec![1])]),
            vec![0b1100_0001, 0b0100_0001, 1],
        );
        test(
            LightData::Cell(vec![LightData::Atom(vec![1]), LightData::Atom(vec![1])]),
            vec![0b1100_0010, 0b0100_0001, 1, 0b0100_0001, 1],
        );
        #[rustfmt::skip]
        test(
            LightData::Atom(vec![
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
        fn prop_light_data(x in any::<LightData>()) {
            let ser = x.ser();
            let de  = LightData::de(&ser).expect("read LightData");
            eprintln!("x {}", x);
            eprintln!("ser {:?}", ser);
            assert_eq!(x, de)
        }
    }
}
