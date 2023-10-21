use std::{cell::RefCell, rc::Rc};

use nom::{
    branch::alt,
    bytes::complete::{tag, take_till},
    character::complete::{anychar, char, multispace0, multispace1, none_of},
    combinator::{opt, peek, success, value},
    error::context,
    multi::{many0, many_till, separated_list1},
    sequence::{delimited, preceded, terminated},
};
use nom_locate::LocatedSpan;

use crate::{
    field::LurkField,
    num::Num,
    package::SymbolRef,
    parser::{
        base,
        error::{ParseError, ParseErrorKind},
        position::Pos,
        string, ParseResult, Span,
    },
    state::{meta_package_symbol, State},
    symbol,
    syntax::Syntax,
    uint::UInt,
};

pub fn parse_line_comment<F: LurkField>(i: Span<'_>) -> ParseResult<'_, F, Span<'_>> {
    let (i, _) = tag(";")(i)?;
    let (i, com) = take_till(|c| c == '\n')(i)?;
    Ok((i, com))
}
pub fn parse_space<F: LurkField>(i: Span<'_>) -> ParseResult<'_, F, Vec<Span<'_>>> {
    let (i, _) = multispace0(i)?;
    let (i, com) = many0(terminated(parse_line_comment, multispace1))(i)?;
    Ok((i, com))
}

pub fn parse_space1<F: LurkField>(i: Span<'_>) -> ParseResult<'_, F, Vec<Span<'_>>> {
    let (i, _) = multispace1(i)?;
    let (i, com) = many0(terminated(parse_line_comment, multispace1))(i)?;
    Ok((i, com))
}

pub fn parse_symbol_limb<F: LurkField>(
    escape: &'static str,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, String> {
    move |from: Span<'_>| {
        let (i, s) = alt((
            string::parse_string_inner1(symbol::SYM_SEPARATOR, false, escape),
            delimited(
                tag("|"),
                string::parse_string_inner1('|', true, "|"),
                tag("|"),
            ),
            value(String::from(""), peek(tag("."))),
        ))(from)?;
        Ok((i, s))
    }
}

pub fn parse_symbol_limb_raw<F: LurkField>(
    escape: &'static str,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, String> {
    move |from: Span<'_>| {
        let (i, s) = alt((
            string::parse_string_inner1(' ', false, escape),
            delimited(
                tag("|"),
                string::parse_string_inner1('|', true, "|"),
                tag("|"),
            ),
            value(String::from(""), peek(tag("."))),
        ))(from)?;
        Ok((i, s))
    }
}

pub fn parse_symbol_limbs<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, Vec<String>> {
    move |from: Span<'_>| {
        let (i, path) = separated_list1(
            char(symbol::SYM_SEPARATOR),
            parse_symbol_limb(symbol::ESCAPE_CHARS),
        )(from)?;
        let (upto, _) = opt(tag("."))(i)?;
        Ok((upto, path))
    }
}

fn intern_path<'a, F: LurkField>(
    state: Rc<RefCell<State>>,
    upto: LocatedSpan<&'a str>,
    path: &[String],
    keyword: Option<bool>,
    create_unknown_packages: bool,
) -> ParseResult<'a, F, SymbolRef> {
    use nom::Err::Failure;
    match keyword {
        Some(keyword) => state
            .borrow_mut()
            .intern_path(path, keyword, create_unknown_packages),
        None => state
            .borrow_mut()
            .intern_relative_path(path, create_unknown_packages),
    }
    .map(|symbol| (upto, symbol))
    .map_err(|e| {
        Failure(ParseError::new(
            upto,
            ParseErrorKind::InterningError(format!("{e}")),
        ))
    })
}

pub fn parse_absolute_symbol<F: LurkField>(
    state: Rc<RefCell<State>>,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, SymbolRef> {
    move |from: Span<'_>| {
        let (i, is_key) = alt((
            value(false, char(symbol::SYM_MARKER)),
            value(true, char(symbol::KEYWORD_MARKER)),
        ))(from)?;
        let (upto, path) = parse_symbol_limbs()(i)?;
        intern_path(
            state.clone(),
            upto,
            &path,
            Some(is_key),
            create_unknown_packages,
        )
    }
}

pub fn parse_relative_symbol<F: LurkField>(
    state: Rc<RefCell<State>>,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, SymbolRef> {
    move |from: Span<'_>| {
        let (i, _) = peek(none_of(",~#(){}[]1234567890."))(from)?;
        let (upto, path) = parse_symbol_limbs()(i)?;
        intern_path(state.clone(), upto, &path, None, create_unknown_packages)
    }
}

pub fn parse_raw_symbol<F: LurkField>(
    state: Rc<RefCell<State>>,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, SymbolRef> {
    move |from: Span<'_>| {
        let (i, _) = tag("~(")(from)?;
        let (i, mut path) = many0(preceded(parse_space, parse_symbol_limb_raw("|()")))(i)?;
        let (upto, _) = many_till(parse_space, tag(")"))(i)?;
        path.reverse();
        intern_path(
            state.clone(),
            upto,
            &path,
            Some(false),
            create_unknown_packages,
        )
    }
}

pub fn parse_raw_keyword<F: LurkField>(
    state: Rc<RefCell<State>>,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, SymbolRef> {
    move |from: Span<'_>| {
        let (i, _) = tag("~:(")(from)?;
        let (i, mut path) = many0(preceded(parse_space, parse_symbol_limb_raw("|()")))(i)?;
        let (upto, _) = many_till(parse_space, tag(")"))(i)?;
        path.reverse();
        intern_path(
            state.clone(),
            upto,
            &path,
            Some(true),
            create_unknown_packages,
        )
    }
}

/// relative: foo.bar
/// absolute: .foo.bar.baz, :foo.bar (escaped limbs: .|foo|.|bar|.|baz|)
/// raw: ~(foo bar baz) = .baz.bar.foo
/// raw keyword: ~:(foo bar) = :bar.foo
pub fn parse_symbol<F: LurkField>(
    state: Rc<RefCell<State>>,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    move |from: Span<'_>| {
        let (upto, sym) = alt((
            parse_relative_symbol(state.clone(), create_unknown_packages),
            parse_absolute_symbol(state.clone(), create_unknown_packages),
            parse_raw_symbol(state.clone(), create_unknown_packages),
            parse_raw_keyword(state.clone(), create_unknown_packages),
        ))(from)?;
        Ok((upto, Syntax::Symbol(Pos::from_upto(from, upto), sym)))
    }
}

pub fn parse_uint<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, base) = alt((
            preceded(tag("0"), base::parse_litbase_code()),
            success(base::LitBase::Dec),
        ))(from)?;
        let (i, digits) = base::parse_litbase_digits(base)(i)?;
        // when more uint types are supported we can do:
        // alt((tag("u8"), tag("u16"), tag("u32"), tag("u64"), tag("u128")))
        let (upto, suffix) = tag("u64")(i)?;
        match *suffix.fragment() {
            "u64" => {
                let (_, x) =
                    ParseError::res(u64::from_str_radix(&digits, base.radix()), from, |e| {
                        ParseErrorKind::ParseIntErr(e)
                    })?;
                let pos = Pos::from_upto(from, upto);
                Ok((upto, Syntax::UInt(pos, UInt::U64(x))))
            }
            _ => unreachable!("implementation error in parse_nat"),
        }
    }
}

fn f_from_le_bytes<F: LurkField>(bs: &[u8]) -> F {
    let mut res = F::ZERO;
    let mut bs = bs.iter().rev().peekable();
    while let Some(b) = bs.next() {
        let b: F = u64::from(*b).into();
        if bs.peek().is_none() {
            res.add_assign(b)
        } else {
            res.add_assign(b);
            res.mul_assign(F::from(256u64));
        }
    }
    res
}

pub fn parse_num_inner<F: LurkField>(
    base: base::LitBase,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, Num<F>> {
    move |from: Span<'_>| {
        let (upto, bytes): (Span<'_>, Vec<u8>) = base::parse_litbase_le_bytes(base)(from)?;
        let max_bytes = (F::ZERO - F::ONE).to_bytes();
        let max_uint = num_bigint::BigUint::from_bytes_le(&max_bytes);
        if num_bigint::BigUint::from_bytes_le(&bytes) > max_uint {
            ParseError::throw(
                from,
                ParseErrorKind::NumLiteralTooBig(F::most_positive(), max_uint),
            )
        } else {
            let f = f_from_le_bytes::<F>(&bytes);
            if let Some(x) = f.to_u64() {
                Ok((upto, Num::U64(x)))
            } else {
                Ok((upto, Num::Scalar(f)))
            }
        }
    }
}

pub fn parse_num<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, neg) = opt(tag("-"))(from)?;
        let (i, base) = alt((
            preceded(tag("0"), base::parse_litbase_code()),
            success(base::LitBase::Dec),
        ))(i)?;
        let (i, num) = parse_num_inner(base)(i)?;
        let (upto, denom) = opt(preceded(tag("/"), parse_num_inner(base)))(i)?;
        let pos = Pos::from_upto(from, upto);
        let mut tmp = Num::<F>::U64(0);
        if neg.is_some() {
            tmp -= num;
        } else {
            tmp = num;
        }
        if let Some(denom) = denom {
            tmp /= denom;
        }
        Ok((upto, Syntax::Num(pos, tmp)))
    }
}

pub fn parse_string<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    move |from: Span<'_>| {
        let (upto, s) = string::parse_string('"')(from)?;
        let pos = Pos::from_upto(from, upto);
        Ok((upto, Syntax::String(pos, s)))
    }
}

// hash syntax for chars
pub fn parse_hash_char<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    |from: Span<'_>| {
        let (i, _) = tag("#\\")(from)?;
        let (upto, c) = alt((string::parse_unicode(), anychar))(i)?;
        let pos = Pos::from_upto(from, upto);
        Ok((upto, Syntax::Char(pos, c)))
    }
}

pub fn parse_char<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, _) = tag("'")(from)?;
        let (i, s) = string::parse_string_inner1('\'', true, "()'")(i)?;
        let (upto, _) = tag("'")(i)?;
        let mut chars: Vec<char> = s.chars().collect();
        if chars.len() == 1 {
            let c = chars.pop().unwrap();
            let pos = Pos::from_upto(from, upto);
            Ok((upto, Syntax::Char(pos, c)))
        } else {
            ParseError::throw(from, ParseErrorKind::InvalidChar(s))
        }
    }
}

pub fn parse_list<F: LurkField>(
    state: Rc<RefCell<State>>,
    meta: bool,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, _) = tag("(")(from)?;
        let (i, xs) = if meta {
            // parse the head symbol in the meta package
            let saved_package = state.borrow().get_current_package_name().clone();
            state
                .borrow_mut()
                .set_current_package(meta_package_symbol().into())
                .expect("meta package is available");
            let (i, h) = preceded(
                parse_space,
                parse_symbol(state.clone(), create_unknown_packages),
            )(i)?;
            // then recover the previous package
            state
                .borrow_mut()
                .set_current_package(saved_package)
                .expect("previous package is available");
            let (i, t) = many0(preceded(
                parse_space,
                parse_syntax(state.clone(), false, create_unknown_packages),
            ))(i)?;
            let mut xs = vec![h];
            xs.extend(t);
            (i, xs)
        } else {
            many0(preceded(
                parse_space,
                parse_syntax(state.clone(), false, create_unknown_packages),
            ))(i)?
        };
        let (i, end) = opt(preceded(
            preceded(parse_space, tag(".")),
            preceded(
                parse_space,
                parse_syntax(state.clone(), false, create_unknown_packages),
            ),
        ))(i)?;
        let (i, _) = parse_space(i)?;
        let (upto, _) = tag(")")(i)?;
        let pos = Pos::from_upto(from, upto);
        if let Some(end) = end {
            Ok((upto, Syntax::Improper(pos, xs, Box::new(end))))
        } else {
            Ok((upto, Syntax::List(pos, xs)))
        }
    }
}

pub fn parse_quote<F: LurkField>(
    state: Rc<RefCell<State>>,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, c) = opt(parse_char())(from)?;
        if let Some(c) = c {
            Ok((i, c))
        } else {
            let (i, _) = tag("'")(from)?;
            let (upto, s) = parse_syntax(state.clone(), false, create_unknown_packages)(i)?;
            let pos = Pos::from_upto(from, upto);
            Ok((upto, Syntax::Quote(pos, Box::new(s))))
        }
    }
}

// top-level syntax parser
pub fn parse_syntax<F: LurkField>(
    state: Rc<RefCell<State>>,
    meta: bool,
    // this parameter triggers a less strict mode for testing purposes
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    move |from: Span<'_>| {
        alt((
            context(
                "list",
                parse_list(state.clone(), meta, create_unknown_packages),
            ),
            parse_uint(),
            parse_num(),
            context(
                "symbol",
                parse_symbol(state.clone(), create_unknown_packages),
            ),
            parse_string(),
            context("quote", parse_quote(state.clone(), create_unknown_packages)),
            parse_hash_char(),
        ))(from)
    }
}

pub fn parse_maybe_meta<F: LurkField>(
    state: Rc<RefCell<State>>,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, Option<(bool, Syntax<F>)>> {
    move |from: Span<'_>| {
        let (_, is_eof) = opt(nom::combinator::eof)(from)?;
        if is_eof.is_some() {
            return Ok((from, None));
        }
        let (next, meta) = opt(char('!'))(from)?;
        let meta = meta.is_some();
        let (end, syntax) = parse_syntax(state.clone(), meta, create_unknown_packages)(next)?;
        Ok((end, Some((meta, syntax))))
    }
}

#[cfg(test)]
pub mod tests {
    use nom::Parser;
    use pasta_curves::pallas::Scalar;
    #[cfg(not(target_arch = "wasm32"))]
    use proptest::prelude::*;

    use super::*;
    use crate::{char, keyword, list, num, str, symbol, uint};

    fn test<'a, P, R>(mut p: P, i: &'a str, expected: Option<R>) -> bool
    where
        P: Parser<Span<'a>, R, ParseError<Span<'a>, Scalar>>,
        R: std::fmt::Display + std::fmt::Debug + Clone + Eq,
    {
        match (expected, p.parse(Span::<'a>::new(i))) {
            (Some(expected), Ok((_, x))) if x == expected => true,
            (Some(_) | None, Ok(..)) | (Some(..), Err(_)) => {
                // println!("input: {:?}", i);
                // println!("expected parse error");
                // println!("detected: {:?}", x);
                false
            }
            (None, Err(_e)) => true,
        }
    }

    #[test]
    fn unit_parse_string() {
        assert!(test(parse_string(), "\"foo\"", Some(str!("foo"))));
        assert!(test(parse_string(), "\"fo\\no\"", Some(str!("fo\no"))));
        assert!(test(
            parse_string(),
            "\"fo\\u{00}o\"",
            Some(str!("fo\u{00}o"))
        ));
        assert!(test(parse_string(), "\"foo\\   \"", Some(str!("foo"))));
    }

    #[test]
    fn unit_parse_symbol() {
        let state_ = State::default().rccell();
        let state = || state_.clone();
        assert!(test(parse_raw_symbol(state(), true), "", None));
        assert!(test(parse_absolute_symbol(state(), true), "", None));
        assert!(test(parse_relative_symbol(state(), true), "", None));
        assert!(test(parse_relative_symbol(state(), true), "", None));
        assert!(test(parse_symbol(state(), true), "", None));
        assert!(test(parse_symbol(state(), true), "~()", Some(symbol!([]))));
        assert!(test(parse_symbol(state(), true), ".", None));
        assert!(test(parse_symbol(state(), true), "..", Some(symbol!([""]))));
        assert!(test(
            parse_symbol(state(), true),
            "foo",
            Some(symbol!(["foo"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            "|foo|",
            Some(symbol!(["foo"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            "|Hi, bye|",
            Some(symbol!(["Hi, bye"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            "|foo|.|bar|",
            Some(symbol!(["foo", "bar"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ".|foo|.|bar|",
            Some(symbol!(["foo", "bar"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ".foo",
            Some(symbol!(["foo"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            "..foo",
            Some(symbol!(["", "foo"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            "foo.",
            Some(symbol!(["foo"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            "foo..",
            Some(symbol!(["foo", ""]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ".foo..",
            Some(symbol!(["foo", ""]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ".foo..",
            Some(symbol!(["foo", ""]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ".foo.bar",
            Some(symbol!(["foo", "bar"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ".foo?.bar?",
            Some(symbol!(["foo?", "bar?"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ".fooλ.barλ",
            Some(symbol!(["fooλ", "barλ"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ".foo\\n.bar\\n",
            Some(symbol!(["foo\n", "bar\n"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ".foo\\u{00}.bar\\u{00}",
            Some(symbol!(["foo\u{00}", "bar\u{00}"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ".foo\\.bar",
            Some(symbol!(["foo.bar"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            "~(asdf )",
            Some(symbol!(["asdf"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            "~( asdf )",
            Some(symbol!(["asdf"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            "~( asdf)",
            Some(symbol!(["asdf"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            "~(asdf.fdsa)",
            Some(symbol!(["asdf.fdsa"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            "~(asdf.fdsa arst)",
            Some(symbol!(["arst", "asdf.fdsa"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            "~(asdf.fdsa arst |wfp qwf|)",
            Some(symbol!(["wfp qwf", "arst", "asdf.fdsa"]))
        ));
    }

    #[test]
    fn unit_parse_keyword() {
        let state_ = State::default().rccell();
        let state = || state_.clone();
        assert!(test(parse_symbol(state(), true), "", None));
        assert!(test(parse_symbol(state(), true), ":", None));
        assert!(test(
            parse_symbol(state(), true),
            "~:()",
            Some(keyword!([]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ":.",
            Some(keyword!([""]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ":foo",
            Some(keyword!(["foo"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ":foo.",
            Some(keyword!(["foo"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ":foo..",
            Some(keyword!(["foo", ""]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ":foo.bar",
            Some(keyword!(["foo", "bar"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ":foo?.bar?",
            Some(keyword!(["foo?", "bar?"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ":fooλ.barλ",
            Some(keyword!(["fooλ", "barλ"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ":foo\\n.bar\\n",
            Some(keyword!(["foo\n", "bar\n"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ":foo\\u{00}.bar\\u{00}",
            Some(keyword!(["foo\u{00}", "bar\u{00}"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            ":foo\\.bar",
            Some(keyword!(["foo.bar"]))
        ));
        assert!(test(
            parse_symbol(state(), true),
            "~:(x y z)",
            Some(keyword!(["z", "y", "x"]))
        ));
    }

    #[test]
    fn unit_parse_list() {
        let state_ = State::default().rccell();
        let state = || state_.clone();
        assert!(test(
            parse_list(state(), false, true),
            "()",
            Some(list!([]))
        ));
        assert!(test(
            parse_list(state(), false, true),
            "(1 2)",
            Some(list!([num!(1), num!(2)])),
        ));
        assert!(test(
            parse_list(state(), false, true),
            "(1)",
            Some(list!([num!(1)])),
        ));
        assert!(test(
            parse_list(state(), false, true),
            "(a)",
            Some(list!([symbol!(["a"])])),
        ));
        assert!(test(
            parse_list(state(), false, true),
            "(a b)",
            Some(list!([symbol!(["a"]), symbol!(["b"])])),
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "(.a .b)",
            Some(list!([symbol!(["a"]), symbol!(["b"])])),
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "(.foo.bar .foo.bar)",
            Some(list!([symbol!(["foo", "bar"]), symbol!(["foo", "bar"])])),
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "(a . b)",
            Some(list!([symbol!(["a"])], symbol!(["b"]))),
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "(.a . .b)",
            Some(list!([symbol!(["a"])], symbol!(["b"]))),
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "(a b . c)",
            Some(list!([symbol!(["a"]), symbol!(["b"])], symbol!(["c"]))),
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "(a . (b . c))",
            Some(list!(
                [symbol!(["a"])],
                list!([symbol!(["b"])], symbol!(["c"]))
            ))
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "(a b c)",
            Some(list!([symbol!(["a"]), symbol!(["b"]), symbol!(["c"])])),
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "('a' 'b' 'c')",
            Some(list!([char!('a'), char!('b'), char!('c')])),
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "(a. b. c.)",
            Some(list!([symbol!(["a"]), symbol!(["b"]), symbol!(["c"])])),
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "(a.. b.. c..)",
            Some(list!([
                symbol!(["a", ""]),
                symbol!(["b", ""]),
                symbol!(["c", ""])
            ])),
        ));
    }

    #[test]
    fn unit_parse_char() {
        assert!(test(parse_char(), "'a'", Some(char!('a'))));
        assert!(test(parse_char(), "'b'", Some(char!('b'))));
        assert!(test(parse_char(), "'\\u{8f}'", Some(char!('\u{8f}'))));
        assert!(test(parse_char(), "'\\t'", Some(char!('\t'))));
        assert!(test(parse_char(), "'('", None));
        assert!(test(parse_char(), "'\\('", Some(char!('('))));
    }

    #[test]
    fn unit_parse_hash_char() {
        let state_ = State::default().rccell();
        let state = || state_.clone();
        assert!(test(parse_hash_char(), "#\\a", Some(char!('a'))));
        assert!(test(parse_hash_char(), "#\\b", Some(char!('b'))));
        assert!(test(parse_hash_char(), r"#\b", Some(char!('b'))));
        assert!(test(parse_hash_char(), "#\\u{8f}", Some(char!('\u{8f}'))));
        assert!(test(
            parse_syntax(state(), false, false),
            "#\\a",
            Some(char!('a'))
        ));
        assert!(test(
            parse_syntax(state(), false, false),
            "#\\b",
            Some(char!('b'))
        ));
        assert!(test(
            parse_syntax(state(), false, false),
            r"#\b",
            Some(char!('b'))
        ));
        assert!(test(
            parse_syntax(state(), false, false),
            r"#\u{8f}",
            Some(char!('\u{8f}'))
        ));
    }

    #[test]
    fn unit_parse_quote() {
        let state_ = State::default().rccell();
        let state = || state_.clone();
        assert!(test(
            parse_quote(state(), true),
            "'.a",
            Some(Syntax::Quote(Pos::No, Box::new(symbol!(["a"]))))
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "':a",
            Some(Syntax::Quote(Pos::No, Box::new(keyword!(["a"]))))
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "'a",
            Some(Syntax::Quote(Pos::No, Box::new(symbol!(["a"]))))
        ));
        assert!(test(parse_quote(state(), true), "'a'", Some(char!('a'))));
        assert!(test(parse_quote(state(), true), "'a'", Some(char!('a'))));
        assert!(test(
            parse_syntax(state(), false, true),
            "'(a b)",
            Some(Syntax::Quote(
                Pos::No,
                Box::new(list!([symbol!(["a"]), symbol!(["b"])]))
            ))
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "('a)",
            Some(list!([Syntax::Quote(Pos::No, Box::new(symbol!(['a'])))]))
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "('a' 'b' 'c')",
            Some(list!([char!('a'), char!('b'), char!('c')])),
        ));
    }

    #[test]
    fn unit_parse_num() {
        assert!(test(parse_num(), "0", Some(num!(0))));
        assert!(test(parse_num(), "00", Some(num!(0))));
        assert!(test(parse_num(), "001", Some(num!(1))));
        assert!(test(parse_num(), "0b0", Some(num!(0))));
        assert!(test(parse_num(), "0o0", Some(num!(0))));
        assert!(test(parse_num(), "0d0", Some(num!(0))));
        assert!(test(parse_num(), "0x0", Some(num!(0))));
        assert!(test(parse_num(), "0xf", Some(num!(15))));
        assert!(test(parse_num(), "0x0f", Some(num!(15))));
        assert!(test(
            parse_num(),
            "0xffff_ffff_ffff_ffff",
            Some(num!(0xffff_ffff_ffff_ffff))
        ));
        assert!(test(
            parse_num(),
            "0x1234_5678_9abc_def0",
            Some(num!(0x1234_5678_9abc_def0))
        ));
        assert!(test(
            parse_num(),
            &format!("0x{}", Scalar::most_positive().hex_digits()),
            Some(num!(Num::Scalar(Scalar::most_positive())))
        ));
        assert!(test(
            parse_num(),
            "0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000000",
            Some(Syntax::Num(
                Pos::No,
                Num::Scalar(<Scalar as ff::Field>::ZERO - Scalar::from(1u64))
            )),
        ));
        assert!(test(
            parse_num(),
            "0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001",
            None,
        ));
        assert!(test(parse_num(), "-0", Some(num!(0))));
        let mut tmp = Num::U64(1u64);
        tmp /= Num::U64(2u64);
        assert!(test(parse_num(), "1/2", Some(Syntax::Num(Pos::No, tmp))));
        let mut tmp = Num::U64(0u64);
        tmp -= Num::U64(1u64);
        tmp /= Num::U64(2u64);
        assert!(test(parse_num(), "-1/2", Some(Syntax::Num(Pos::No, tmp))));
    }

    #[test]
    fn unit_parse_syntax_misc() {
        let vec: Vec<u8> = vec![
            0x3e, 0x2e, 0x50, 0x55, 0xdc, 0xf6, 0x14, 0x86, 0xb0, 0x3b, 0xb8, 0x0e, 0xd2, 0xb3,
            0xf1, 0xa3, 0x5c, 0x30, 0xe1, 0x22, 0xde, 0xfe, 0xba, 0xe8, 0x24, 0xfa, 0xe4, 0xed,
            0x32, 0x40, 0x8e, 0x87,
        ]
        .into_iter()
        .rev()
        .collect();
        let state_ = State::default().rccell();
        let state = || state_.clone();

        assert!(test(
            parse_syntax(state(), false, true),
            ".a ;arst",
            Some(symbol!(["a"])),
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "(0x3e2e5055dcf61486b03bb80ed2b3f1a35c30e122defebae824fae4ed32408e87)",
            Some(list!([num!(Num::Scalar(f_from_le_bytes(&vec)))])),
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            ".\\.",
            Some(symbol!(["."]))
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            ".\\'",
            Some(symbol!(["'"]))
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            ".\\'\\u{8e}\\u{fffc}\\u{201b}",
            Some(symbol!(["'\u{8e}\u{fffc}\u{201b}"])),
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "(lambda (🚀) 🚀)",
            Some(list!([
                symbol!(["lambda"]),
                list!([symbol!(["🚀"])]),
                symbol!(["🚀"])
            ])),
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "11242421860377074631u64",
            Some(uint!(11242421860377074631))
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            ":\u{ae}\u{60500}\u{87}..)",
            Some(keyword!(["®\u{60500}\u{87}", ""]))
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "(~:() 11242421860377074631u64 . :\u{ae}\u{60500}\u{87}..)",
            Some(list!(
                [keyword!([]), uint!(11242421860377074631)],
                keyword!(["®\u{60500}\u{87}", ""])
            ))
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "((\"\"))",
            Some(list!([list!([Syntax::String(Pos::No, "".to_string())])]))
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "((=))",
            Some(list!([list!([symbol!(["="])])]))
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "('.. . a)",
            Some(list!(
                [Syntax::Quote(Pos::No, Box::new(symbol!([""])))],
                symbol!(["a"])
            ))
        ));
        assert_eq!(
            "(.. . .a)",
            format!("{}", list!(Scalar, [symbol!([""])], symbol!(["a"])))
        );
        assert_eq!(
            "('.. . .a)",
            format!(
                "{}",
                list!(
                    Scalar,
                    [Syntax::Quote(Pos::No, Box::new(symbol!([""])))],
                    symbol!(["a"])
                )
            )
        );
        assert!(test(
            parse_syntax(state(), false, true),
            "'\\('",
            Some(char!('('))
        ));
        assert_eq!("'\\('", format!("{}", char!(Scalar, '(')));
        assert_eq!(
            "(' ' . .a)",
            format!("{}", list!(Scalar, [char!(' ')], symbol!(["a"])))
        );
        assert!(test(
            parse_syntax(state(), false, true),
            "(' ' . a)",
            Some(list!([char!(' ')], symbol!(["a"])))
        ));
        assert!(test(
            parse_syntax(state(), false, true),
            "(cons # \"\")",
            None
        ));
        assert!(test(parse_syntax(state(), false, true), "#", None));
    }

    #[test]
    fn test_minus_zero_symbol() {
        let x: Syntax<Scalar> = symbol!(["-0"]);
        let text = format!("{x}");
        let (_, res) = parse_syntax(State::default().rccell(), false, true)(Span::new(&text))
            .expect("valid parse");
        assert_eq!(x, res)
    }

    proptest! {
        #[test]
        fn prop_syntax(x in any::<Syntax<Scalar>>()) {
            let text = format!("{}", x);
            let (_, res) = parse_syntax(State::default().rccell(), false, true)(Span::new(&text)).expect("valid parse");
            assert_eq!(x, res)
        }
    }
}
