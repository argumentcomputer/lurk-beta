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
use std::collections::BTreeMap;
use std::fmt::Display;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;

use anyhow::anyhow;
use nom::bytes::complete::take;
use nom::multi::count;
use nom::Finish;
use nom::IResult;

/// `ZData` is a binary tree with two types of nodes: Atom and Cell.
///
/// # Examples
///
/// ```
/// use lurk::z_data::ZData;
///
/// let data = ZData::Cell(vec![
///     ZData::Atom(vec![0x01]),
///     ZData::Atom(vec![0x02, 0x03]),
/// ]);
///
/// assert_eq!(data.to_string(), "[c:[a:01], [a:02, 03]]");
/// ```
// Why is above better than       [c:[a:[01], a:[02, 03]]] ?
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

impl<A: Encodable + Sized + Ord, B: Encodable + Sized> Encodable for BTreeMap<A, B> {
    fn ser(&self) -> ZData {
        let mut res = Vec::new();
        for (k, v) in self {
            res.push(ZData::Cell(vec![k.ser(), v.ser()]))
        }
        ZData::Cell(res)
    }

    fn de(ld: &ZData) -> Result<Self> {
        let xs: Vec<(A, B)> = Encodable::de(ld)?;
        Ok(xs.into_iter().collect())
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

use serde::ser;
use thiserror::Error;

// Serialize ZData to bytes
// Wrapper function for testing
pub fn to_bytes(zd: ZData) -> Vec<u8> {
    zd.ser()
}

#[derive(Error, Debug)]
pub enum SerdeError {
    #[error("Type error")]
    UnsupportedType(String),
}

impl serde::ser::Error for SerdeError {
    fn custom<T: core::fmt::Display>(msg: T) -> Self {
        Self::UnsupportedType(msg.to_string())
    }
}

// Maybe should be atom and cell
pub struct SerializeCell {
    cell: Vec<ZData>,
}

//impl ser::Serialize for ZData {
//    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
//    where
//        S: ser::Serializer,
//    {
//        match &self {
//            Self::Atom(v) => serializer.serialize_bytes(v),
//            Self::Cell(z) => serializer.serialize_seq(Some(z.len())),
//        }
//    }
//}

pub struct Serializer;

pub fn to_z_data<T>(value: T) -> Result<ZData, SerdeError>
where
    T: ser::Serialize,
{
    value.serialize(Serializer)
}

// Ignored these and just use the serializer
// If this way is faster, use an override of some kind
// Should this be a pub fn from_z_expr instead?
impl<F: LurkField> From<ZExpr<F>> for ZData {
  fn from(value: &ZExpr<F>) -> Self {
        match value {
            ZExpr::Nil => ZData::Cell(vec![ZData::Atom(vec![0u8])]),
            ZExpr::Cons(x, y) => ZData::Cell(vec![ZData::Atom(vec![1u8]), x.ser(), y.ser()]),
            ZExpr::Comm(f, x) => {
                ZData::Cell(vec![ZData::Atom(vec![2u8]), FWrap(*f).ser(), x.ser()])
            }
            ZExpr::SymNil => ZData::Cell(vec![ZData::Atom(vec![3u8])]),
            ZExpr::SymCons(x, y) => ZData::Cell(vec![ZData::Atom(vec![4u8]), x.ser(), y.ser()]),
            ZExpr::Key(x) => ZData::Cell(vec![ZData::Atom(vec![5u8]), x.ser()]),
            ZExpr::Fun {
                arg,
                body,
                closed_env,
            } => ZData::Cell(vec![
                ZData::Atom(vec![6u8]),
                arg.ser(),
                body.ser(),
                closed_env.ser(),
            ]),
            ZExpr::Num(f) => ZData::Cell(vec![ZData::Atom(vec![7u8]), FWrap(*f).ser()]),
            ZExpr::StrNil => ZData::Cell(vec![ZData::Atom(vec![8u8])]),
            ZExpr::StrCons(x, y) => ZData::Cell(vec![ZData::Atom(vec![9u8]), x.ser(), y.ser()]),
            ZExpr::Thunk(x, y) => ZData::Cell(vec![ZData::Atom(vec![10u8]), x.ser(), y.ser()]),
            ZExpr::Char(x) => ZData::Cell(vec![ZData::Atom(vec![11u8]), (*x).ser()]),
            ZExpr::Uint(x) => ZData::Cell(vec![ZData::Atom(vec![12u8]), x.ser()]),
        }
}

impl<F: LurkField> From<ZPtr<F>> for ZData {
  fn from(value: &ZPtr<F>) -> Self {
    let (x, y): (FWrap<F>, FWrap<F>) = (FWrap(value.0.to_field()), FWrap(value.1));
    Self::from((x,y))
  }
}

impl<F: LurkField> From<FWrap<F>> for ZData {
  // Beware, this assumes a little endian encoding
  fn from(value: &FWrap<F>) -> Self {
    let bytes: Vec<u8> = Vec::from(value.0.to_repr().as_ref());
    let mut trimmed_bytes: Vec<_> = bytes.into_iter().rev().skip_while(|x| *x == 0u8).collect();
    trimmed_bytes.reverse();
    ZData::Atom(trimmed_bytes)
  }
}

impl<F: LurkField> From<ZStore<F>> for ZData {
  fn from(value: &ZStore<F>) -> Self {
    Self::from(self.expr_map.clone(), self.cont_map.clone())
  }
}

impl<F: LurkField> From<ZCont<F>> for ZData {
  fn from(value: &ZCont<F>) -> Self {
        match self {
            ZCont::Outermost => ZData::Cell(vec![ZData::Atom(vec![0u8])]),
            ZCont::Call0 {
                saved_env,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![1u8]),
                saved_env.ser(),
                continuation.ser(),
            ]),
            ZCont::Call {
                unevaled_arg,
                saved_env,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![2u8]),
                unevaled_arg.ser(),
                saved_env.ser(),
                continuation.ser(),
            ]),
            ZCont::Call2 {
                function,
                saved_env,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![3u8]),
                function.ser(),
                saved_env.ser(),
                continuation.ser(),
            ]),
            ZCont::Tail {
                saved_env,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![4u8]),
                saved_env.ser(),
                continuation.ser(),
            ]),
            ZCont::Error => ZData::Cell(vec![ZData::Atom(vec![5u8])]),
            ZCont::Lookup {
                saved_env,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![6u8]),
                saved_env.ser(),
                continuation.ser(),
            ]),

            ZCont::Unop {
                operator,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![7u8]),
                operator.ser(),
                continuation.ser(),
            ]),
            ZCont::Binop {
                operator,
                saved_env,
                unevaled_args,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![8u8]),
                operator.ser(),
                saved_env.ser(),
                unevaled_args.ser(),
                continuation.ser(),
            ]),
            ZCont::Binop2 {
                operator,
                evaled_arg,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![9u8]),
                operator.ser(),
                evaled_arg.ser(),
                continuation.ser(),
            ]),
            ZCont::If {
                unevaled_args,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![10u8]),
                unevaled_args.ser(),
                continuation.ser(),
            ]),
            ZCont::Let {
                var,
                body,
                saved_env,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![11u8]),
                var.ser(),
                body.ser(),
                saved_env.ser(),
                continuation.ser(),
            ]),
            ZCont::LetRec {
                var,
                body,
                saved_env,
                continuation,
            } => ZData::Cell(vec![
                ZData::Atom(vec![12u8]),
                var.ser(),
                body.ser(),
                saved_env.ser(),
                continuation.ser(),
            ]),
            ZCont::Emit { continuation } => {
                ZData::Cell(vec![ZData::Atom(vec![13u8]), continuation.ser()])
            }
            ZCont::Dummy => ZData::Cell(vec![ZData::Atom(vec![14u8])]),
            ZCont::Terminal => ZData::Cell(vec![ZData::Atom(vec![15u8])]),
        }
  }
}

impl ser::Serializer for Serializer {
    type Ok = ZData;

    type Error = SerdeError;

    type SerializeSeq = SerializeCell;
    type SerializeTuple = SerializeCell; 
    type SerializeTupleStruct = SerializeCell;
    type SerializeTupleVariant = SerializeCell;
    type SerializeMap = SerializeCell;
    type SerializeStruct = SerializeCell;
    type SerializeStructVariant = SerializeCell;

    #[inline]
    fn serialize_bool(self, value: bool) -> Result<Self::Ok, Self::Error> {
        self.serialize_u32(value.into())
    }

    #[inline]
    fn serialize_i8(self, _value: i8) -> Result<Self::Ok, Self::Error> {
        Err(SerdeError::UnsupportedType(
            "Unsigned integers not supported".into(),
        ))
    }

    #[inline]
    fn serialize_i16(self, _value: i16) -> Result<Self::Ok, Self::Error> {
        Err(SerdeError::UnsupportedType(
            "Unsigned integers not supported".into(),
        ))
    }

    #[inline]
    fn serialize_i32(self, _value: i32) -> Result<Self::Ok, Self::Error> {
        Err(SerdeError::UnsupportedType(
            "Unsigned integers not supported".into(),
        ))
    }

    #[inline]
    fn serialize_i64(self, _value: i64) -> Result<Self::Ok, Self::Error> {
        Err(SerdeError::UnsupportedType(
            "Unsigned integers not supported".into(),
        ))
    }

    #[inline]
    fn serialize_u8(self, value: u8) -> Result<Self::Ok, Self::Error> {
        self.serialize_u32(value.into())
    }

    #[inline]
    fn serialize_u16(self, value: u16) -> Result<Self::Ok, Self::Error> {
        self.serialize_u32(value.into())
    }

    #[inline]
    fn serialize_u32(self, value: u32) -> Result<Self::Ok, Self::Error> {
        Ok(ZData::Atom(u32::to_le_bytes(value).to_vec()))
    }

    #[inline]
    fn serialize_u64(self, value: u64) -> Result<Self::Ok, Self::Error> {
        Ok(ZData::Atom(u64::to_le_bytes(value).to_vec()))
    }

    #[inline]
    fn serialize_f32(self, _value: f32) -> Result<Self::Ok, Self::Error> {
        Err(SerdeError::UnsupportedType("Floats not supported".into()))
    }

    #[inline]
    fn serialize_f64(self, _value: f64) -> Result<Self::Ok, Self::Error> {
        Err(SerdeError::UnsupportedType("Floats not supported".into()))
    }

    #[inline]
    fn serialize_char(self, value: char) -> Result<Self::Ok, Self::Error> {
        self.serialize_u32(value as u32)
    }

    #[inline]
    fn serialize_str(self, value: &str) -> Result<Self::Ok, Self::Error> {
      self.serialize_bytes(value.as_bytes())
    }

    fn serialize_bytes(self, value: &[u8]) -> Result<Self::Ok, Self::Error> {
        Ok(ZData::Atom(value.to_vec()))
    }

    #[inline]
    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
      self.serialize_none()
    }

    #[inline]
    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
      self.serialize_none()
    }

    #[inline]
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
      self.serialize_u32(variant_index)
    }

    #[inline]
    fn serialize_newtype_struct<T: ?Sized>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ser::Serialize,
    {
      value.serialize(self)
    }

    fn serialize_newtype_variant<T: ?Sized>(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ser::Serialize,
    {
        Err(SerdeError::UnsupportedType(
            "Newtype variant not supported".into(),
        ))
    }

    #[inline]
    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        Ok(ZData::Atom(vec![]))
    }

    #[inline]
    fn serialize_some<T: ?Sized>(self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: ser::Serialize,
    {
        Ok(ZData::Cell(vec![value.serialize(self)?]))
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Ok(SerializeCell {
            cell: Vec::with_capacity(len.unwrap_or(0)),
        })
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        self.serialize_tuple(len)
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        todo!()
    }

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        self.serialize_seq(len.map(|l| l * 2))
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        //self.serialize_map(Some(len))
        todo!()
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        todo!()
    }
}

impl ser::SerializeSeq for SerializeCell {
    type Ok = ZData;
    type Error = SerdeError;

    fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ser::Serialize,
    {
        self.cell.push(value.serialize(Serializer)?);
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(ZData::Cell(self.cell))
    }
}

impl ser::SerializeTuple for SerializeCell {
    type Ok = ZData;
    type Error = SerdeError;

    fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ser::Serialize,
    {
        ser::SerializeSeq::serialize_element(self, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        ser::SerializeSeq::end(self)
    }
}

impl ser::SerializeTupleStruct for SerializeCell {
    type Ok = ZData;
    type Error = SerdeError;

    fn serialize_field<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ser::Serialize,
    {
        ser::SerializeSeq::serialize_element(self, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        ser::SerializeSeq::end(self)
    }
}

impl ser::SerializeTupleVariant for SerializeCell {
    type Ok = ZData;
    type Error = SerdeError;

    fn serialize_field<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ser::Serialize,
    {
        ser::SerializeSeq::serialize_element(self, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        ser::SerializeSeq::end(self)
    }
}

impl ser::SerializeMap for SerializeCell {
    type Ok = ZData;
    type Error = SerdeError;

    fn serialize_key<T: ?Sized>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: ser::Serialize,
    {
        cell.push(key.serialize(self))
    }

    fn serialize_value<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ser::Serialize,
    {
        cell.push(value.serialize(self))
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(ZData::Cell(self.cell))
    }
}

impl ser::SerializeStruct for SerializeCell {
    type Ok = ZData;
    type Error = SerdeError;

    fn serialize_field<T: ?Sized>(
        &mut self,
        _key: &'static str,
        _value: &T,
    ) -> Result<(), Self::Error>
    where
        T: ser::Serialize,
    {
        todo!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        serde::ser::SerializeMap::end(self)
    }
}

impl ser::SerializeStructVariant for SerializeCell {
    type Ok = ZData;
    type Error = SerdeError;

    fn serialize_field<T: ?Sized>(
        &mut self,
        _key: &'static str,
        _value: &T,
    ) -> Result<(), Self::Error>
    where
        T: ser::Serialize,
    {
        todo!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        serde::ser::SerializeMap::end(self)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::z_expr::ZExpr;
    use pasta_curves::pallas::Scalar;

    #[test]
    fn unit_serde_encodable_zdata() {
        let ze: ZExpr<Scalar> = ZExpr::Nil;
        let zd = to_z_data(ze);
        println!("ZData: {:?}", zd);
    }

    //#[test]
    //fn unit_serde_encodable_bytes() {
    //    let test = |zd: ZData, xs: Vec<u8>| {
    //        println!("{:?}", zd.ser());
    //        let enc = zd.ser();
    //        assert_eq!(enc, xs);
    //        let ser = to_z_data(xs);
    //        assert_eq!(ser, xs);
    //    };

    //    test(ZData::Atom(vec![]), vec![0b0000_0000]);
    //    test(ZData::Cell(vec![]), vec![0b1000_0000]);
    //    test(ZData::Atom(vec![0]), vec![0b0100_0001, 0]);
    //    test(ZData::Atom(vec![1]), vec![0b0100_0001, 1]);
    //    test(
    //        ZData::Cell(vec![ZData::Atom(vec![1])]),
    //        vec![0b1100_0001, 0b0100_0001, 1],
    //    );
    //    test(
    //        ZData::Cell(vec![ZData::Atom(vec![1]), ZData::Atom(vec![1])]),
    //        vec![0b1100_0010, 0b0100_0001, 1, 0b0100_0001, 1],
    //    );
    //    #[rustfmt::skip]
    //    test(
    //        ZData::Atom(vec![
    //            0, 0, 0, 0, 0, 0, 0, 0,
    //            0, 0, 0, 0, 0, 0, 0, 0,
    //            0, 0, 0, 69, 96, 43, 67,
    //            4, 224, 2, 148, 222, 23, 85, 212,
    //            43, 182, 14, 90, 138, 62, 151, 68,
    //            207, 128, 70, 44, 70, 31, 155, 81,
    //            19, 21, 219, 228, 40, 235, 21, 137,
    //            238, 250, 180, 50, 118, 244, 44, 84,
    //            75, 185,
    //        ]),
    //        vec![0b0000_0001, 65,
    //            0, 0, 0, 0, 0, 0, 0, 0,
    //            0, 0, 0, 0, 0, 0, 0, 0,
    //            0, 0, 0, 69, 96, 43, 67,
    //            4, 224, 2, 148, 222, 23, 85, 212,
    //            43, 182, 14, 90, 138, 62, 151, 68,
    //            207, 128, 70, 44, 70, 31, 155, 81,
    //            19, 21, 219, 228, 40, 235, 21, 137,
    //            238, 250, 180, 50, 118, 244, 44, 84,
    //            75, 185,
    //        ],
    //    );
    //}

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
    fn unit_z_data() {
        let test = |zd: ZData, xs: Vec<u8>| {
            println!("{:?}", zd.ser());
            let ser = zd.ser();
            assert_eq!(ser, xs);
            println!("{:?}", ZData::de(&ser));
            assert_eq!(zd, ZData::de(&ser).expect("valid zdata"))
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
