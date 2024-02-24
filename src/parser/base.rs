use std::{borrow::ToOwned, string::String, vec::Vec};

use crate::field::LurkField;
use base_x;
use nom::{
    branch::alt,
    bytes::complete::{tag, take_till},
    character::complete::satisfy,
    combinator::value,
    error::context,
    InputTakeAtPosition,
};

use crate::parser::{
    error::{map_parse_err, ParseError, ParseErrorKind},
    ParseResult, Span,
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
    pub fn parse_code<F: LurkField>(i: Span<'_>) -> ParseResult<'_, F, Self> {
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
        let x = x.to_ascii_lowercase();
        self.base_digits().chars().any(|y| x == y)
    }

    pub fn encode<I: AsRef<[u8]>>(&self, input: I) -> String {
        base_x::encode(self.base_digits(), input.as_ref())
    }

    pub fn decode<'a, F: LurkField>(&self, input: Span<'a>) -> ParseResult<'a, F, Vec<u8>> {
        let (i, o) = input.split_at_position_complete(|x| !self.is_digit(x))?;
        match base_x::decode(self.base_digits(), o.fragment()) {
            Ok(bytes) => Ok((i, bytes)),
            Err(_) => Err(nom::Err::Error(ParseError::new(
                i,
                ParseErrorKind::InvalidBaseEncoding(*self),
            ))),
        }
    }
}

macro_rules! define_parse_digits {
    ($name:ident, $base:ident, $digit_str:expr, $digits_str:expr, $map_fn:expr) => {
        pub fn $name<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, String> {
            move |from: Span<'_>| {
                let (i, d) = context($digit_str, satisfy(|x| LitBase::$base.is_digit(x)))(from)?;
                let (i, ds) = context(
                    $digits_str,
                    take_till(|x| !(LitBase::$base.is_digit(x) || x == '_')),
                )(i)?;
                let ds: String = core::iter::once(d)
                    .chain((*ds.fragment()).to_owned().chars())
                    .filter(|x| *x != '_')
                    .map($map_fn)
                    .collect();
                Ok((i, ds))
            }
        }
    };
}

define_parse_digits!(
    parse_bin_digits,
    Bin,
    "binary digit",
    "binary digits",
    |x| x
);
define_parse_digits!(parse_oct_digits, Oct, "octal digit", "octal digits", |x| x);
define_parse_digits!(
    parse_dec_digits,
    Dec,
    "decimal digit",
    "decimal digits",
    |x| x
);
define_parse_digits!(
    parse_hex_digits,
    Hex,
    "hexadecimal digit",
    "hexadecimal digits",
    |x| x.to_ascii_lowercase()
);

pub fn parse_litbase_code<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, LitBase> {
    move |from: Span<'_>| {
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

#[allow(clippy::type_complexity)]
pub fn parse_litbase_digits<F: LurkField>(
    base: LitBase,
) -> Box<dyn Fn(Span<'_>) -> ParseResult<'_, F, String>> {
    Box::new(move |from: Span<'_>| match base {
        LitBase::Bin => parse_bin_digits()(from),
        LitBase::Oct => parse_oct_digits()(from),
        LitBase::Dec => parse_dec_digits()(from),
        LitBase::Hex => parse_hex_digits()(from),
    })
}
