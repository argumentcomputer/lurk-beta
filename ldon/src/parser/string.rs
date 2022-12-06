////! Adapted from the examples in the nom repository
////! https://github.com/Geal/nom/blob/master/examples/string.rs
////! which licensed under the following MIT license:
////! https://github.com/Geal/nom/blob/master/LICENSE

//! This example shows an example of how to parse an escaped string. The
//! rules for the string are similar to JSON and rust. A string is:
//!
//! - Enclosed by double quotes
//! - Can contain any raw unescaped code point besides \ and "
//! - Matches the following escape sequences: \b, \f, \n, \r, \t, \", \\, \/
//! - Matches code points like Rust: \u{XXXX}, where XXXX can be up to 6 hex
//!   characters
//! - an escape followed by whitespace consumes all whitespace between the
//!   escape and the next non-whitespace character

#![cfg(feature = "alloc")]

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
    map_opt,
    map_res,
    value,
    verify,
  },
  error::{
    FromExternalError,
    ParseError,
  },
  multi::fold_many0,
  sequence::{
    delimited,
    preceded,
  },
  IResult,
};

/// Parse a unicode sequence, of the form u{XXXX}, where XXXX is 1 to 6
/// hexadecimal numerals. We will combine this later with parse_escaped_char
/// to parse sequences like \u{00AC}.
fn parse_unicode<'a>(
  input: Span<'a>,
) -> IResult<Span<'a>, char, ParseError<Span<'a>>> {
  move |from: Span| {
    let (i, hex) = preceded(
      char('u'),
      delimited(
        char('{'),
        take_while_m_n(1, 6, |c: char| c.is_ascii_hexdigit()),
        char('}'),
      ),
    )(from)?;

    let x = u32::from_str_radix(hex, 16);
    Ok(char::from_u32(value))
  }
}

/// Parse an escaped character: \n, \t, \r, \u{00AC}, etc.
fn parse_escaped_char<'a, E>(input: &'a str) -> IResult<&'a str, char, E>
where E: ParseError<&'a str> + FromExternalError<&'a str, std::num::ParseIntError>
{
  preceded(
    char('\\'),
    alt((
      parse_unicode,
      value('\n', char('n')),
      value('\r', char('r')),
      value('\t', char('t')),
      value('\u{08}', char('b')),
      value('\u{0C}', char('f')),
      value('\\', char('\\')),
      value('/', char('/')),
      value('"', char('"')),
    )),
  )(input)
}

/// Parse a backslash, followed by any amount of whitespace. This is used later
/// to discard any escaped whitespace.
fn parse_escaped_whitespace<'a, E: ParseError<&'a str>>(
  input: &'a str,
) -> IResult<&'a str, &'a str, E> {
  preceded(char('\\'), multispace1)(input)
}

/// Parse a non-empty block of text that doesn't include \ or "
fn parse_literal<'a, E: ParseError<&'a str>>(
  input: &'a str,
) -> IResult<&'a str, &'a str, E> {
  let not_quote_slash = is_not("\"\\");
  verify(not_quote_slash, |s: &str| !s.is_empty())(input)
}

/// A string fragment contains a fragment of a string being parsed: either
/// a non-empty Literal (a series of non-escaped characters), a single
/// parsed escaped character, or a block of escaped whitespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StringFragment<'a> {
  Literal(&'a str),
  EscapedChar(char),
  EscapedWS,
}

/// Combine parse_literal, parse_escaped_whitespace, and parse_escaped_char
/// into a StringFragment.
fn parse_fragment<'a, E>(
  input: &'a str,
) -> IResult<&'a str, StringFragment<'a>, E>
where E: ParseError<&'a str> + FromExternalError<&'a str, std::num::ParseIntError>
{
  alt((
    map(parse_literal, StringFragment::Literal),
    map(parse_escaped_char, StringFragment::EscapedChar),
    value(StringFragment::EscapedWS, parse_escaped_whitespace),
  ))(input)
}

/// Parse a string. Use a loop of parse_fragment and push all of the fragments
/// into an output string.
fn parse_string<'a, E>(input: &'a str) -> IResult<&'a str, String, E>
where E: ParseError<&'a str> + FromExternalError<&'a str, std::num::ParseIntError>
{
  let build_string =
    fold_many0(parse_fragment, String::new, |mut string, fragment| {
      match fragment {
        StringFragment::Literal(s) => string.push_str(s),
        StringFragment::EscapedChar(c) => string.push(c),
        StringFragment::EscapedWS => {},
      }
      string
    });
  delimited(char('"'), build_string, char('"'))(input)
}
