use std::{borrow::ToOwned, string::String, vec::Vec};

use crate::field::LurkField;
use base_x;
use nom::{
    branch::alt,
    bytes::complete::{tag, take_till},
    character::complete::satisfy,
    combinator::value,
    error::context,
    IResult, InputTakeAtPosition,
};

use crate::parser::{
    error::{map_parse_err, ParseError, ParseErrorKind},
    Span,
};

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum LitBase {
    Bin,
    Oct,
    Dec,
    Hex,
}

impl Default for LitBase {
    fn default() -> Self {
        Self::Hex
    }
}

impl LitBase {
    pub fn parse_code<F: LurkField>(i: Span) -> IResult<Span, Self, ParseError<Span, F>> {
        alt((
            value(Self::Bin, tag("b")),
            value(Self::Oct, tag("o")),
            value(Self::Dec, tag("d")),
            value(Self::Hex, tag("x")),
        ))(i)
    }

    /// Get the code corresponding to the base algorithm.
    pub fn code(&self) -> char {
        match self {
            Self::Bin => 'b',
            Self::Oct => 'o',
            Self::Dec => 'd',
            Self::Hex => 'x',
        }
    }

    pub fn base_digits(&self) -> &str {
        match self {
            Self::Bin => "01",
            Self::Oct => "01234567",
            Self::Dec => "0123456789",
            Self::Hex => "0123456789abcdef",
        }
    }

    pub fn radix(&self) -> u32 {
        match self {
            Self::Bin => 2,
            Self::Oct => 8,
            Self::Dec => 10,
            Self::Hex => 16,
        }
    }

    pub fn is_digit(&self, x: char) -> bool {
        self.base_digits()
            .chars()
            .any(|y| x.to_ascii_lowercase() == y)
    }

    pub fn encode<I: AsRef<[u8]>>(&self, input: I) -> String {
        base_x::encode(self.base_digits(), input.as_ref())
    }

    pub fn decode<'a, F: LurkField>(
        &self,
        input: Span<'a>,
    ) -> IResult<Span<'a>, Vec<u8>, ParseError<Span<'a>, F>> {
        let (i, o) = input.split_at_position_complete(|x| !self.is_digit(x))?;
        match base_x::decode(self.base_digits(), o.fragment()) {
            Ok(bytes) => Ok((i, bytes)),
            Err(_) => Err(nom::Err::Error(ParseError::new(
                i,
                ParseErrorKind::InvalidBaseEncoding(*self),
            ))),
        }
    }

    pub fn decode1<'a, F: LurkField>(
        &self,
        input: Span<'a>,
    ) -> IResult<Span<'a>, Vec<u8>, ParseError<Span<'a>, F>> {
        let (i, o) = input
            .split_at_position1_complete(|x| !self.is_digit(x), nom::error::ErrorKind::Digit)?;
        match base_x::decode(self.base_digits(), o.fragment()) {
            Ok(bytes) => Ok((i, bytes)),
            Err(_) => Err(nom::Err::Error(ParseError::new(
                i,
                ParseErrorKind::InvalidBaseEncoding(*self),
            ))),
        }
    }
}

pub fn parse_bin_digits<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, String, ParseError<Span, F>> {
    move |from: Span| {
        let (i, d) = context("binary digit", satisfy(|x| LitBase::Bin.is_digit(x)))(from)?;
        let (i, ds) = context(
            "binary digits",
            take_till(|x| !(LitBase::Bin.is_digit(x) || x == '_')),
        )(i)?;
        let ds: String = core::iter::once(d)
            .chain((*ds.fragment()).to_owned().chars())
            .filter(|x| *x != '_')
            .collect();
        Ok((i, ds))
    }
}

pub fn parse_oct_digits<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, String, ParseError<Span, F>> {
    move |from: Span| {
        let (i, d) = context("octal digit", satisfy(|x| LitBase::Oct.is_digit(x)))(from)?;
        let (i, ds) = context(
            "octal digits",
            take_till(|x| !(LitBase::Oct.is_digit(x) || x == '_')),
        )(i)?;
        let ds: String = core::iter::once(d)
            .chain((*ds.fragment()).to_owned().chars())
            .filter(|x| *x != '_')
            .collect();
        Ok((i, ds))
    }
}

pub fn parse_dec_digits<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, String, ParseError<Span, F>> {
    move |from: Span| {
        let (i, d) = context("decimal digit", satisfy(|x| LitBase::Dec.is_digit(x)))(from)?;
        let (i, ds) = context(
            "decimal digits",
            take_till(|x| !(LitBase::Dec.is_digit(x) || x == '_')),
        )(i)?;
        let ds: String = core::iter::once(d)
            .chain((*ds.fragment()).to_owned().chars())
            .filter(|x| *x != '_')
            .collect();
        Ok((i, ds))
    }
}

pub fn parse_hex_digits<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, String, ParseError<Span, F>> {
    move |from: Span| {
        let (i, d) = context("hexadecimal digit", satisfy(|x| LitBase::Hex.is_digit(x)))(from)?;
        let (i, ds) = context(
            "hexadecimal digits",
            take_till(|x| !(LitBase::Hex.is_digit(x) || x == '_')),
        )(i)?;
        let ds: String = core::iter::once(d)
            .chain((*ds.fragment()).to_owned().chars())
            .filter(|x| *x != '_')
            .map(|x| x.to_ascii_lowercase())
            .collect();
        Ok((i, ds))
    }
}

pub fn parse_litbase_code<F: LurkField>(
) -> impl Fn(Span) -> IResult<Span, LitBase, ParseError<Span, F>> {
    move |from: Span| {
        map_parse_err(
            alt((
                value(LitBase::Bin, tag("b")),
                value(LitBase::Oct, tag("o")),
                value(LitBase::Dec, tag("d")),
                value(LitBase::Hex, tag("x")),
            ))(from),
            |_| ParseError::new(from, ParseErrorKind::UnknownBaseCode),
        )
    }
}
// pub fn parse_litbase_bits_code() -> impl Fn(Span) -> IResult<Span, LitBase,
// ParseError<Span>> {    move |from: Span| {
//        throw_err(
//            alt((value(LitBase::Bin, tag("b")), value(LitBase::Hex,
// tag("x"))))(from),            |_| ParseError::new(from,
// ParseErrorKind::UnknownBaseCode),        )
//    }
//}

#[allow(clippy::type_complexity)]
pub fn parse_litbase_digits<F: LurkField>(
    base: LitBase,
) -> Box<dyn Fn(Span) -> IResult<Span, String, ParseError<Span, F>>> {
    Box::new(move |from: Span| match base {
        LitBase::Bin => parse_bin_digits()(from),
        LitBase::Oct => parse_oct_digits()(from),
        LitBase::Dec => parse_dec_digits()(from),
        LitBase::Hex => parse_hex_digits()(from),
    })
}

pub fn parse_litbase_be_bytes<F: LurkField>(
    base: LitBase,
) -> impl Fn(Span) -> IResult<Span, Vec<u8>, ParseError<Span, F>> {
    move |from: Span| {
        let (i, o): (Span, String) = parse_litbase_digits(base)(from)?;
        match base_x::decode(base.base_digits(), &o) {
            Ok(bytes) => Ok((i, bytes)),
            Err(_) => Err(nom::Err::Error(ParseError::new(
                i,
                ParseErrorKind::InvalidBaseEncoding(base),
            ))),
        }
    }
}

pub fn parse_litbase_le_bytes<F: LurkField>(
    base: LitBase,
) -> impl Fn(Span) -> IResult<Span, Vec<u8>, ParseError<Span, F>> {
    move |from: Span| {
        let (i, bytes) = parse_litbase_be_bytes(base)(from)?;
        Ok((i, bytes.into_iter().rev().collect()))
    }
}

#[cfg(test)]
pub mod tests {
    use blstrs::Scalar as Fr;
    use nom::Parser;

    use super::*;

    fn test_parse<'a, P>(mut p: P, i: &'a str, expected: Option<Vec<u8>>)
    where
        P: Parser<Span<'a>, Vec<u8>, ParseError<Span<'a>, Fr>>,
    {
        match (expected, p.parse(Span::new(i))) {
            (Some(expected), Ok((_i, x))) if x == expected => (),
            (Some(expected), Ok((i, x))) => {
                println!("input: {:?}", i);
                println!("expected: {:?}", expected);
                println!("detected: {:?}", x);
                assert!(false)
            }
            (Some(..), Err(e)) => {
                println!("{}", e);
                assert!(false)
            }
            (None, Ok((i, x))) => {
                println!("input: {:?}", i);
                println!("expected parse error");
                println!("detected: {:?}", x);
                assert!(false)
            }
            (None, Err(_e)) => (),
        }
    }

    #[test]
    fn unit_parse_litbase_bytes_endianesss() {
        test_parse(
            parse_litbase_le_bytes::<Fr>(LitBase::Hex),
            "1234567890",
            Some(vec![0x90, 0x78, 0x56, 0x34, 0x12]),
        );
        test_parse(
            parse_litbase_be_bytes::<Fr>(LitBase::Hex),
            "1234567890",
            Some(vec![0x12, 0x34, 0x56, 0x78, 0x90]),
        )
    }
}
