////! Adapted from the examples in the nom repository
////! https://github.com/Geal/nom/blob/master/examples/string.rs
////! which licensed under the following MIT license:
////! https://github.com/Geal/nom/blob/master/LICENSE

use crate::field::LurkField;
use nom::{
    branch::alt,
    bytes::complete::{is_not, take_while_m_n},
    character::complete::{char, multispace1, one_of},
    combinator::{map, value, verify},
    multi::fold_many0,
    multi::fold_many1,
    sequence::{delimited, preceded},
};

use crate::parser::{
    error::{ParseError, ParseErrorKind},
    ParseResult, Span,
};

/// Parse a unicode sequence, of the form u{XXXX}, where XXXX is 1 to 6
/// hexadecimal numerals. We will combine this later with parse_escaped_char
/// to parse sequences like \u{00AC}.
pub fn parse_unicode<'a, F: LurkField>() -> impl Fn(Span<'a>) -> ParseResult<'a, F, char> {
    move |from: Span<'a>| {
        let (i, hex) = preceded(
            char('u'),
            delimited(
                char('{'),
                take_while_m_n(1, 6, |c: char| c.is_ascii_hexdigit()),
                char('}'),
            ),
        )(from)?;
        let hex: String = (*hex.fragment()).to_string();
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
    delim: char,
    must_escape: &'static str,
) -> impl Fn(Span<'a>) -> ParseResult<'a, F, char> {
    move |from: Span<'a>| {
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
            value('\'', char('\'')),
            value(delim, char(delim)),
            one_of(must_escape),
        ))(i)?;
        Ok((i, esc))
    }
}

/// Parse a backslash, followed by any amount of whitespace. This is used
/// later to discard any escaped whitespace.
pub fn parse_escaped_whitespace<'a, F: LurkField>(
) -> impl Fn(Span<'a>) -> ParseResult<'a, F, Span<'a>> {
    move |from: Span<'a>| preceded(char('\\'), multispace1)(from)
}

///// Parse a non-empty block of text that doesn't include \ or delim
pub fn parse_literal<'a, F: LurkField>(
    delim: char,
    whitespace: bool,
    must_escape: &'static str,
) -> impl Fn(Span<'a>) -> ParseResult<'a, F, Span<'a>> {
    move |from: Span<'a>| {
        let mut s = String::from(must_escape);
        s.push(delim);
        s.push('\\');
        if !whitespace {
            for c in crate::parser::LURK_WHITESPACE {
                s.push(c);
            }
        }
        let mut p = verify(is_not(&*s), |s: &Span<'a>| !s.fragment().is_empty());
        p(from)
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
    whitespace: bool,
    must_escape: &'static str,
) -> impl Fn(Span<'a>) -> ParseResult<'a, F, StringFragment<'a>> {
    move |from: Span<'a>| {
        if whitespace {
            alt((
                map(
                    parse_literal(delim, whitespace, must_escape),
                    StringFragment::Literal,
                ),
                map(
                    parse_escaped_char(delim, must_escape),
                    StringFragment::EscapedChar,
                ),
                value(StringFragment::EscapedWS, parse_escaped_whitespace()),
            ))(from)
        } else {
            alt((
                map(
                    parse_literal(delim, whitespace, must_escape),
                    StringFragment::Literal,
                ),
                map(
                    parse_escaped_char(delim, must_escape),
                    StringFragment::EscapedChar,
                ),
            ))(from)
        }
    }
}

/// Parse a non-empty string. Use a loop of parse_fragment and push all of the fragments
/// into an output string.
pub fn parse_string_inner1<'a, F: LurkField>(
    delim: char,
    whitespace: bool,
    must_escape: &'static str,
) -> impl Fn(Span<'a>) -> ParseResult<'a, F, String> {
    move |from: Span<'a>| {
        fold_many1(
            parse_fragment(delim, whitespace, must_escape),
            String::new,
            |mut string, fragment| {
                match fragment {
                    StringFragment::Literal(s) => string.push_str(s.fragment()),
                    StringFragment::EscapedChar(c) => string.push(c),
                    StringFragment::EscapedWS => {}
                }
                string
            },
        )(from)
    }
}

/// Parse a string. Use a loop of parse_fragment and push all of the fragments
/// into an output string.
pub fn parse_string_inner<'a, F: LurkField>(
    delim: char,
    whitespace: bool,
    must_escape: &'static str,
) -> impl Fn(Span<'a>) -> ParseResult<'a, F, String> {
    move |from: Span<'a>| {
        fold_many0(
            parse_fragment(delim, whitespace, must_escape),
            String::new,
            |mut string, fragment| {
                match fragment {
                    StringFragment::Literal(s) => string.push_str(s.fragment()),
                    StringFragment::EscapedChar(c) => string.push(c),
                    StringFragment::EscapedWS => {}
                }
                string
            },
        )(from)
    }
}

/// Parse a string with the outer delimiter characters
pub fn parse_string<'a, F: LurkField>(
    delim: char,
) -> impl Fn(Span<'a>) -> ParseResult<'a, F, String> {
    move |from: Span<'a>| {
        delimited(
            char(delim),
            parse_string_inner(delim, true, ""),
            char(delim),
        )(from)
    }
}
#[cfg(test)]
pub mod tests {
    use blstrs::Scalar as Fr;
    use nom::Parser;

    use super::*;

    fn test_parse<'a, P>(mut p: P, i: &'a str, expected: Option<String>)
    where
        P: Parser<Span<'a>, String, ParseError<Span<'a>, Fr>>,
    {
        match (expected, p.parse(Span::new(i))) {
            (Some(expected), Ok((_i, x))) if x == expected => (),
            (Some(expected), Ok((i, x))) => {
                println!("input: {:?}", i);
                println!("expected: {:?}", expected);
                println!("detected: {:?}", x);
                unreachable!("unexpected parse result")
            }
            (Some(..), Err(e)) => {
                println!("{}", e);
                unreachable!("unexpected parse result")
            }
            (None, Ok((i, x))) => {
                println!("input: {:?}", i);
                println!("expected parse error");
                println!("detected: {:?}", x);
                unreachable!("unexpected parse result")
            }
            (None, Err(_e)) => (),
        }
    }

    #[test]
    fn unit_parse_string() {
        test_parse(parse_string('"'), "\"foo\"", Some(String::from("foo")));
        test_parse(parse_string('"'), "\"\"", Some(String::from("")));
        test_parse(
            parse_string_inner('"', true, ""),
            "",
            Some(String::from("")),
        );
        test_parse(
            parse_string_inner('"', true, ""),
            " ",
            Some(String::from(" ")),
        );
        test_parse(
            parse_string_inner('"', false, ""),
            " ",
            Some(String::from("")),
        );
        test_parse(
            parse_string_inner('"', false, ""),
            "a",
            Some(String::from("a")),
        );
        test_parse(
            parse_string_inner('"', false, ""),
            "a ",
            Some(String::from("a")),
        );
        test_parse(
            parse_string_inner('"', true, ""),
            "a ",
            Some(String::from("a ")),
        );
        test_parse(
            parse_string_inner('.', false, ")"),
            "b)",
            Some(String::from("b")),
        );
    }
}
