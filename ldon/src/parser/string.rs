////! Adapted from the examples in the nom repository
////! https://github.com/Geal/nom/blob/master/examples/string.rs
////! which licensed under the following MIT license:
////! https://github.com/Geal/nom/blob/master/LICENSE

use lurk_ff::field::LurkField;
use nom::{
  branch::alt,
  bytes::streaming::{
    is_not,
    take_while_m_n,
  },
  character::streaming::{
    char,
    multispace1,
  },
  combinator::{
    map,
    value,
    verify,
  },
  multi::fold_many0,
  sequence::{
    delimited,
    preceded,
  },
  IResult,
};

use crate::parser::{
  error::{
    ParseError,
    ParseErrorKind,
  },
  Span,
};

/// Parse a unicode sequence, of the form u{XXXX}, where XXXX is 1 to 6
/// hexadecimal numerals. We will combine this later with parse_escaped_char
/// to parse sequences like \u{00AC}.
pub fn parse_unicode<'a, F: LurkField>(
) -> impl Fn(Span<'a>) -> IResult<Span<'a>, char, ParseError<Span<'a>, F>> {
  move |from: Span| {
    let (i, hex) = preceded(
      char('u'),
      delimited(
        char('{'),
        take_while_m_n(1, 6, |c: char| c.is_ascii_hexdigit()),
        char('}'),
      ),
    )(from)?;
    let hex: String = hex.fragment().to_string();
    let (i, x) = ParseError::res(u32::from_str_radix(&hex, 16), i, |x| {
      ParseErrorKind::InvalidBase16EscapeSequence(hex.clone(), Some(x))
    })?;
    let (i, x) = ParseError::opt(char::from_u32(x), i, {
      ParseErrorKind::InvalidBase16EscapeSequence(hex.clone(), None)
    })?;
    Ok((i, x))
  }
}

/// Parse an escaped character: \n, \t, \r, \u{00AC}, etc.
pub fn parse_escaped_char<'a, F: LurkField>(
) -> impl Fn(Span<'a>) -> IResult<Span<'a>, char, ParseError<Span<'a>, F>> {
  move |from: Span| {
    let (i, _) = char('\\')(from)?;
    let (i, esc) = alt((
      parse_unicode(),
      value('\n', char('n')),
      value('\r', char('r')),
      value('\t', char('t')),
      value('\u{08}', char('b')),
      value('\u{0C}', char('f')),
      value('\\', char('\\')),
      value('/', char('/')),
      value('"', char('"')),
    ))(i)?;
    Ok((i, esc))
  }
}

/// Parse a backslash, followed by any amount of whitespace. This is used
/// later to discard any escaped whitespace.
pub fn parse_escaped_whitespace<'a, F: LurkField>(
) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Span<'a>, ParseError<Span<'a>, F>> {
  move |from: Span| preceded(char('\\'), multispace1)(from)
}

///// Parse a non-empty block of text that doesn't include \ or "
pub fn parse_literal<'a, F: LurkField>(
  delim: char,
) -> impl Fn(Span<'a>) -> IResult<Span<'a>, Span<'a>, ParseError<Span<'a>, F>> {
  move |from: Span| {
    let mut s = String::from(delim);
    s.push('\\');
    let x = verify(is_not(&*s), |s: &Span<'a>| !s.fragment().is_empty())(from);
    x
  }
}

/// A string fragment contains a fragment of a string being parsed: either
/// a non-empty Literal (a series of non-escaped characters), a single
/// parsed escaped character, or a block of escaped whitespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StringFragment<'a> {
  Literal(Span<'a>),
  EscapedChar(char),
  EscapedWS,
}

/// Combine parse_literal, parse_escaped_whitespace, and parse_escaped_char
/// into a StringFragment.
pub fn parse_fragment<'a, F: LurkField>(
  delim: char,
) -> impl Fn(
  Span<'a>,
) -> IResult<Span<'a>, StringFragment<'a>, ParseError<Span<'a>, F>> {
  move |from: Span| {
    alt((
      map(parse_literal(delim), StringFragment::Literal),
      map(parse_escaped_char(), StringFragment::EscapedChar),
      value(StringFragment::EscapedWS, parse_escaped_whitespace()),
    ))(from)
  }
}

/// Parse a string. Use a loop of parse_fragment and push all of the fragments
/// into an output string.
pub fn parse_string<'a, F: LurkField>(
  delim: char,
) -> impl Fn(Span<'a>) -> IResult<Span<'a>, String, ParseError<Span<'a>, F>> {
  move |from: Span| {
    let build_string =
      fold_many0(parse_fragment(delim), String::new, |mut string, fragment| {
        match fragment {
          StringFragment::Literal(s) => string.push_str(s.fragment()),
          StringFragment::EscapedChar(c) => string.push(c),
          StringFragment::EscapedWS => {},
        }
        string
      });
    delimited(char(delim), build_string, char(delim))(from)
  }
}
