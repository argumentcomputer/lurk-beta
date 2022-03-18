use crate::parser::error::{throw_err, ParseError, ParseErrorKind};
use crate::parser::Span;

use multibase::Base;

use nom::{
    branch::alt,
    bytes::complete::{tag, take_till, take_till1},
    character::complete::satisfy,
    combinator::value,
    error::context,
    IResult, InputTakeAtPosition,
};

use alloc::string::String;
use alloc::{borrow::ToOwned, boxed::Box, vec::Vec};

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
    pub fn parse_code(i: Span) -> IResult<Span, Self, ParseError<Span>> {
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

    pub fn decode<'a>(&self, input: Span<'a>) -> IResult<Span<'a>, Vec<u8>, ParseError<Span<'a>>> {
        let (i, o) = input.split_at_position_complete(|x| !self.is_digit(x))?;
        match base_x::decode(self.base_digits(), o.fragment()) {
            Ok(bytes) => Ok((i, bytes)),
            Err(_) => Err(nom::Err::Error(ParseError::new(
                i,
                ParseErrorKind::InvalidBaseEncoding(*self),
            ))),
        }
    }

    pub fn decode1<'a>(&self, input: Span<'a>) -> IResult<Span<'a>, Vec<u8>, ParseError<Span<'a>>> {
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

pub fn parse_bin_digits() -> impl Fn(Span) -> IResult<Span, String, ParseError<Span>> {
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

pub fn parse_oct_digits() -> impl Fn(Span) -> IResult<Span, String, ParseError<Span>> {
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

pub fn parse_dec_digits() -> impl Fn(Span) -> IResult<Span, String, ParseError<Span>> {
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

pub fn parse_hex_digits() -> impl Fn(Span) -> IResult<Span, String, ParseError<Span>> {
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

pub fn parse_litbase_code() -> impl Fn(Span) -> IResult<Span, LitBase, ParseError<Span>> {
    move |from: Span| {
        throw_err(
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
pub fn parse_litbase_bits_code() -> impl Fn(Span) -> IResult<Span, LitBase, ParseError<Span>> {
    move |from: Span| {
        throw_err(
            alt((value(LitBase::Bin, tag("b")), value(LitBase::Hex, tag("x"))))(from),
            |_| ParseError::new(from, ParseErrorKind::UnknownBaseCode),
        )
    }
}

pub fn parse_litbase_digits(
    base: LitBase,
) -> Box<dyn Fn(Span) -> IResult<Span, String, ParseError<Span>>> {
    Box::new(move |from: Span| match base {
        LitBase::Bin => parse_bin_digits()(from),
        LitBase::Oct => parse_oct_digits()(from),
        LitBase::Dec => parse_dec_digits()(from),
        LitBase::Hex => parse_hex_digits()(from),
    })
}

pub fn parse_litbase_bytes(
    base: LitBase,
) -> impl Fn(Span) -> IResult<Span, Vec<u8>, ParseError<Span>> {
    move |from: Span| {
        let (i, o) = parse_litbase_digits(base)(from)?;
        match base_x::decode(base.base_digits(), &o) {
            Ok(bytes) => Ok((i, bytes)),
            Err(_) => Err(nom::Err::Error(ParseError::new(
                i,
                ParseErrorKind::InvalidBaseEncoding(base),
            ))),
        }
    }
}

pub const MULTIBASE_DIGITS: &str =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/-_";

pub fn is_multibase_digit(x: char) -> bool {
    MULTIBASE_DIGITS.chars().any(|y| x == y)
}

pub fn parse_multibase_digits() -> impl Fn(Span) -> IResult<Span, Span, ParseError<Span>> {
    move |from: Span| context("multibase digits", take_till1(|x| !is_multibase_digit(x)))(from)
}

pub fn parse_multibase() -> impl Fn(Span) -> IResult<Span, (Base, Vec<u8>), ParseError<Span>> {
    move |from: Span| {
        let (i, o) = parse_multibase_digits()(from)?;
        match multibase::decode(o.fragment()) {
            Ok((base, bytes)) => Ok((i, (base, bytes))),
            Err(e) => Err(nom::Err::Error(ParseError::new(
                i,
                ParseErrorKind::MultibaseError(e),
            ))),
        }
    }
}
