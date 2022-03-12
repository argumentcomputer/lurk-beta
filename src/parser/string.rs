////! Adapted from the examples in the nom repository
////! https://github.com/Geal/nom/blob/master/examples/string.rs
////! which licensed under the following MIT license:
////! https://github.com/Geal/nom/blob/master/LICENSE

use crate::parser::{error::ParseError, error::ParseErrorKind, Span};

use nom::{
    branch::alt,
    bytes::complete::{take_till1, take_while_m_n},
    character::complete::{char, multispace1},
    combinator::{map, value, verify},
    error::context,
    multi::fold_many0,
    sequence::preceded,
    Err, IResult,
};

use alloc::{borrow::ToOwned, string::String};

pub fn parse_codepoint(from: Span) -> IResult<Span, char, ParseError<Span>> {
    let (i, _) = context("the character 'u' to begin a unicode codepoint", char('u'))(from)?;
    let (i, _) = context("the open brace '{' of a unicode codepoint", char('{'))(i)?;
    let (i, s) = context(
        "between 1 to 6 hexadecimal digits to indicate a unicode codepoint",
        take_while_m_n(1, 6, |c: char| c.is_ascii_hexdigit()),
    )(i)?;
    let (i, _) = context("the close brace '}' of a unicode codepoint", char('}'))(i)?;
    let s = s.fragment();
    match u32::from_str_radix(s, 16) {
        Ok(x) => match char::from_u32(x) {
            Some(c) => Ok((i, c)),
            _ => Err(Err::Error(ParseError::new(
                i,
                ParseErrorKind::InvalidBase16EscapeSequence(String::from(s.to_owned())),
            ))),
        },
        Err(e) => Err(Err::Error(ParseError::new(
            i,
            ParseErrorKind::ParseIntErr(e),
        ))),
    }
}
pub fn parse_escape(i: Span) -> IResult<Span, char, ParseError<Span>> {
    let (i, _) = context(
        "the backslash '\\' to begin a string escape sequence",
        char('\\'),
    )(i)?;
    alt((
        parse_codepoint,
        value('\n', char('n')),
        value('\r', char('r')),
        value('\t', char('t')),
        value('\u{08}', char('b')),
        value('\u{0C}', char('f')),
        value('\\', char('\\')),
        value('"', char('"')),
        value('\'', char('\'')),
    ))(i)
}

fn parse_escaped_whitespace(from: Span) -> IResult<Span, Span, ParseError<Span>> {
    preceded(
        context(
            "the backslash '\\' to begin string escaped whitespace",
            char('\\'),
        ),
        multispace1,
    )(from)
}

fn parse_literal(halt: &'static str) -> impl Fn(Span) -> IResult<Span, Span, ParseError<Span>> {
    move |from: Span| {
        let p = |c| halt.chars().any(|x| (x == c) | (c == '\\'));
        verify(take_till1(p), |s: &Span| !s.fragment().is_empty())(from)
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StringFragment<'a> {
    Literal(Span<'a>),
    EscapedChar(char),
    EscapedWS,
}

fn parse_fragment<'a>(
    halt: &'static str,
) -> impl Fn(Span<'a>) -> IResult<Span<'a>, StringFragment<'a>, ParseError<Span<'a>>> {
    move |from: Span<'a>| {
        alt((
            map(
                context("string literal", parse_literal(halt)),
                StringFragment::Literal,
            ),
            map(
                context("string escape", parse_escape),
                StringFragment::EscapedChar,
            ),
            value(
                StringFragment::EscapedWS,
                context(
                    "escaped whitespace within a string",
                    parse_escaped_whitespace,
                ),
            ),
        ))(from)
    }
}

pub fn parse_string<'a>(
    halt: &'static str,
) -> impl Fn(Span<'a>) -> IResult<Span<'a>, String, ParseError<Span<'a>>> {
    move |from: Span<'a>| {
        fold_many0(
            parse_fragment(halt),
            || String::new(),
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
