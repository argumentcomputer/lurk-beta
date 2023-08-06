use crate::field::LurkField;
use nom::{
    branch::alt,
    bytes::complete::{tag, take_till},
    character::complete::{anychar, char, multispace0, multispace1, none_of},
    combinator::{opt, peek, success, value},
    error::context,
    multi::{many0, many_till, separated_list1},
    sequence::{delimited, preceded, terminated},
};

use crate::{
    num::Num,
    parser::{
        base,
        error::{ParseError, ParseErrorKind},
        position::Pos,
        string, ParseResult, Span,
    },
    symbol,
    syntax::Syntax,
    uint::UInt,
};

pub fn parse_line_comment<F: LurkField>(i: Span<'_>) -> ParseResult<'_, F, Span<'_>> {
    let (i, _) = tag(";;")(i)?;
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

pub fn parse_path_component<F: LurkField>(
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

pub fn parse_path_component_raw<F: LurkField>(
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

pub fn parse_path_components<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, Vec<String>>
{
    move |from: Span<'_>| {
        let (i, path) = separated_list1(
            char(symbol::SYM_SEPARATOR),
            parse_path_component(symbol::ESCAPE_CHARS),
        )(from)?;
        let (upto, _) = opt(tag("."))(i)?;
        Ok((upto, path))
    }
}

pub fn parse_absolute_path<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, is_key) = alt((
            value(false, char(symbol::SYM_MARKER)),
            value(true, char(symbol::KEYWORD_MARKER)),
        ))(from)?;
        let (upto, path) = parse_path_components()(i)?;
        Ok((upto, Syntax::Path(Pos::from_upto(from, upto), path, is_key)))
    }
}

pub fn parse_relative_path<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, _) = peek(none_of(",~#(){}[]1234567890."))(from)?;
        let (upto, path) = parse_path_components()(i)?;
        Ok((upto, Syntax::RelPath(Pos::from_upto(from, upto), path)))
    }
}

pub fn parse_raw_path<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, _) = tag("~(")(from)?;
        let (i, mut path) = many0(preceded(parse_space, parse_path_component_raw("|()")))(i)?;
        let (upto, _) = many_till(parse_space, tag(")"))(i)?;
        path.reverse();
        Ok((upto, Syntax::Path(Pos::from_upto(from, upto), path, false)))
    }
}

pub fn parse_raw_keyword_path<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>>
{
    move |from: Span<'_>| {
        let (i, _) = tag("~:(")(from)?;
        let (i, mut path) = many0(preceded(parse_space, parse_path_component_raw("|()")))(i)?;
        let (upto, _) = many_till(parse_space, tag(")"))(i)?;
        path.reverse();
        Ok((upto, Syntax::Path(Pos::from_upto(from, upto), path, true)))
    }
}

/// relative: foo.bar
/// absolute: .foo.bar.baz, :foo.bar (escaped limbs: .|foo|.|bar|.|baz|)
/// raw: ~(foo bar baz) = .baz.bar.foo
/// raw keyword: ~:(foo bar) = :bar.foo
pub fn parse_path<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    move |from: Span<'_>| {
        alt((
            parse_relative_path(),
            parse_absolute_path(),
            parse_raw_path(),
            parse_raw_keyword_path(),
        ))(from)
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
        let b: F = (*b as u64).into();
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

pub fn parse_list<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, _) = tag("(")(from)?;
        //let (i, _) = parse_space(i)?;
        let (i, xs) = many0(preceded(parse_space, parse_syntax()))(i)?;
        let (i, end) = opt(preceded(
            preceded(parse_space, tag(".")),
            preceded(parse_space, parse_syntax()),
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

pub fn parse_quote<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, c) = opt(parse_char())(from)?;
        if let Some(c) = c {
            Ok((i, c))
        } else {
            let (i, _) = tag("'")(from)?;
            let (upto, s) = parse_syntax()(i)?;
            let pos = Pos::from_upto(from, upto);
            Ok((upto, Syntax::Quote(pos, Box::new(s))))
        }
    }
}

// top-level syntax parser
pub fn parse_syntax<F: LurkField>() -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax<F>> {
    move |from: Span<'_>| {
        alt((
            context("list", parse_list()),
            parse_uint(),
            parse_num(),
            context("path", parse_path()),
            parse_string(),
            context("quote", parse_quote()),
            parse_hash_char(),
        ))(from)
    }
}

pub fn parse_maybe_meta<F: LurkField>(
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, Option<(bool, Syntax<F>)>> {
    move |from: Span<'_>| {
        let (_, is_eof) = opt(nom::combinator::eof)(from)?;
        if is_eof.is_some() {
            return Ok((from, None));
        }
        let (next, meta) = opt(char('!'))(from)?;
        if meta.is_some() {
            let (end, syntax) = parse_syntax()(next)?;
            Ok((end, Some((true, syntax))))
        } else {
            let (end, syntax) = parse_syntax()(from)?;
            Ok((end, Some((false, syntax))))
        }
    }
}

#[cfg(test)]
pub mod tests {
    use blstrs::Scalar;
    use nom::Parser;
    #[cfg(not(target_arch = "wasm32"))]
    use proptest::prelude::*;

    use super::*;
    #[allow(unused_imports)]
    use crate::{char, key_path, list, num, rel_path, str, sym_path, uint};

    fn test<'a, P, R>(mut p: P, i: &'a str, expected: Option<R>) -> bool
    where
        P: Parser<Span<'a>, R, ParseError<Span<'a>, Scalar>>,
        R: std::fmt::Display + std::fmt::Debug + Clone + Eq,
    {
        match (expected, p.parse(Span::<'a>::new(i))) {
            (Some(expected), Ok((_, x))) if x == expected => true,
            (Some(_), Ok(..)) => {
                // println!("input: {:?}", i);
                // println!("expected: {} {:?}", expected.clone(), expected);
                // println!("detected: {} {:?}", x.clone(), x);
                false
            }
            (Some(..), Err(_)) => {
                // println!("{}", e);
                false
            }
            (None, Ok(..)) => {
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
    fn unit_parse_path() {
        assert!(test(parse_raw_path(), "", None));
        assert!(test(parse_absolute_path(), "", None));
        assert!(test(parse_relative_path(), "", None));
        assert!(test(parse_path(), "", None));
        assert!(test(parse_path(), "~()", Some(sym_path!([]))));
        assert!(test(parse_path(), ".", None));
        assert!(test(parse_path(), "..", Some(sym_path!([""]))));
        assert!(test(parse_path(), "foo", Some(rel_path!(["foo"]))));
        assert!(test(parse_path(), "|foo|", Some(rel_path!(["foo"]))));
        assert!(test(
            parse_path(),
            "|Hi, bye|",
            Some(rel_path!(["Hi, bye"]))
        ));
        assert!(test(
            parse_path(),
            "|foo|.|bar|",
            Some(rel_path!(["foo", "bar"]))
        ));
        assert!(test(
            parse_path(),
            ".|foo|.|bar|",
            Some(sym_path!(["foo", "bar"]))
        ));
        assert!(test(parse_path(), ".foo", Some(sym_path!(["foo"]))));
        assert!(test(parse_path(), "..foo", Some(sym_path!(["", "foo"]))));
        assert!(test(parse_path(), "foo.", Some(rel_path!(["foo"]))));
        assert!(test(parse_path(), "foo..", Some(rel_path!(["foo", ""]))));
        assert!(test(parse_path(), ".foo..", Some(sym_path!(["foo", ""]))));
        assert!(test(parse_path(), ".foo..", Some(sym_path!(["foo", ""]))));
        assert!(test(
            parse_path(),
            ".foo.bar",
            Some(sym_path!(["foo", "bar"]))
        ));
        assert!(test(
            parse_path(),
            ".foo?.bar?",
            Some(sym_path!(["foo?", "bar?"]))
        ));
        assert!(test(
            parse_path(),
            ".fooλ.barλ",
            Some(sym_path!(["fooλ", "barλ"]))
        ));
        assert!(test(
            parse_path(),
            ".foo\\n.bar\\n",
            Some(sym_path!(["foo\n", "bar\n"]))
        ));
        assert!(test(
            parse_path(),
            ".foo\\u{00}.bar\\u{00}",
            Some(sym_path!(["foo\u{00}", "bar\u{00}"]))
        ));
        assert!(test(
            parse_path(),
            ".foo\\.bar",
            Some(sym_path!(["foo.bar"]))
        ));
        assert!(test(parse_path(), "~(asdf )", Some(sym_path!(["asdf"]))));
        assert!(test(parse_path(), "~( asdf )", Some(sym_path!(["asdf"]))));
        assert!(test(parse_path(), "~( asdf)", Some(sym_path!(["asdf"]))));
        assert!(test(
            parse_path(),
            "~(asdf.fdsa)",
            Some(sym_path!(["asdf.fdsa"]))
        ));
        assert!(test(
            parse_path(),
            "~(asdf.fdsa arst)",
            Some(sym_path!(["arst", "asdf.fdsa"]))
        ));
        assert!(test(
            parse_path(),
            "~(asdf.fdsa arst |wfp qwf|)",
            Some(sym_path!(["wfp qwf", "arst", "asdf.fdsa"]))
        ));
    }

    #[test]
    fn unit_parse_keyword() {
        assert!(test(parse_path(), "", None));
        assert!(test(parse_path(), ":", None));
        assert!(test(parse_path(), "~:()", Some(key_path!([]))));
        assert!(test(parse_path(), ":.", Some(key_path!([""]))));
        assert!(test(parse_path(), ":foo", Some(key_path!(["foo"]))));
        assert!(test(parse_path(), ":foo.", Some(key_path!(["foo"]))));
        assert!(test(parse_path(), ":foo..", Some(key_path!(["foo", ""]))));
        assert!(test(
            parse_path(),
            ":foo.bar",
            Some(key_path!(["foo", "bar"]))
        ));
        assert!(test(
            parse_path(),
            ":foo?.bar?",
            Some(key_path!(["foo?", "bar?"]))
        ));
        assert!(test(
            parse_path(),
            ":fooλ.barλ",
            Some(key_path!(["fooλ", "barλ"]))
        ));
        assert!(test(
            parse_path(),
            ":foo\\n.bar\\n",
            Some(key_path!(["foo\n", "bar\n"]))
        ));
        assert!(test(
            parse_path(),
            ":foo\\u{00}.bar\\u{00}",
            Some(key_path!(["foo\u{00}", "bar\u{00}"]))
        ));
        assert!(test(
            parse_path(),
            ":foo\\.bar",
            Some(key_path!(["foo.bar"]))
        ));
        assert!(test(
            parse_path(),
            "~:(x y z)",
            Some(key_path!(["z", "y", "x"]))
        ));
    }

    #[test]
    fn unit_parse_list() {
        assert!(test(parse_list(), "()", Some(list!([]))));
        assert!(test(parse_list(), "(1 2)", Some(list!([num!(1), num!(2)])),));
        assert!(test(parse_list(), "(1)", Some(list!([num!(1)])),));
        assert!(test(parse_list(), "(a)", Some(list!([rel_path!(["a"])])),));
        assert!(test(
            parse_list(),
            "(a b)",
            Some(list!([rel_path!(["a"]), rel_path!(["b"])])),
        ));
        assert!(test(
            parse_syntax(),
            "(.a .b)",
            Some(list!([sym_path!(["a"]), sym_path!(["b"])])),
        ));
        assert!(test(
            parse_syntax(),
            "(.foo.bar .foo.bar)",
            Some(list!([
                sym_path!(["foo", "bar"]),
                sym_path!(["foo", "bar"])
            ])),
        ));
        assert!(test(
            parse_syntax(),
            "(a . b)",
            Some(list!([rel_path!(["a"])], rel_path!(["b"]))),
        ));
        assert!(test(
            parse_syntax(),
            "(.a . .b)",
            Some(list!([sym_path!(["a"])], sym_path!(["b"]))),
        ));
        assert!(test(
            parse_syntax(),
            "(a b . c)",
            Some(list!(
                [rel_path!(["a"]), rel_path!(["b"])],
                rel_path!(["c"])
            )),
        ));
        assert!(test(
            parse_syntax(),
            "(a . (b . c))",
            Some(list!(
                [rel_path!(["a"])],
                list!([rel_path!(["b"])], rel_path!(["c"]))
            ))
        ));
        assert!(test(
            parse_syntax(),
            "(a b c)",
            Some(list!([
                rel_path!(["a"]),
                rel_path!(["b"]),
                rel_path!(["c"])
            ])),
        ));
        assert!(test(
            parse_syntax(),
            "('a' 'b' 'c')",
            Some(list!([char!('a'), char!('b'), char!('c')])),
        ));

        assert!(test(
            parse_syntax(),
            "(a. b. c.)",
            Some(list!([
                rel_path!(["a"]),
                rel_path!(["b"]),
                rel_path!(["c"])
            ])),
        ));
        assert!(test(
            parse_syntax(),
            "(a.. b.. c..)",
            Some(list!([
                rel_path!(["a", ""]),
                rel_path!(["b", ""]),
                rel_path!(["c", ""])
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
        assert!(test(parse_hash_char(), "#\\a", Some(char!('a'))));
        assert!(test(parse_hash_char(), "#\\b", Some(char!('b'))));
        assert!(test(parse_hash_char(), r"#\b", Some(char!('b'))));
        assert!(test(parse_hash_char(), "#\\u{8f}", Some(char!('\u{8f}'))));
        assert!(test(parse_syntax(), "#\\a", Some(char!('a'))));
        assert!(test(parse_syntax(), "#\\b", Some(char!('b'))));
        assert!(test(parse_syntax(), r"#\b", Some(char!('b'))));
        assert!(test(parse_syntax(), r"#\u{8f}", Some(char!('\u{8f}'))));
    }

    #[test]
    fn unit_parse_quote() {
        assert!(test(
            parse_quote(),
            "'.a",
            Some(Syntax::Quote(Pos::No, Box::new(sym_path!(["a"]))))
        ));
        assert!(test(
            parse_syntax(),
            "':a",
            Some(Syntax::Quote(Pos::No, Box::new(key_path!(["a"]))))
        ));
        assert!(test(
            parse_syntax(),
            "'a",
            Some(Syntax::Quote(Pos::No, Box::new(rel_path!(["a"]))))
        ));
        assert!(test(parse_quote(), "'a'", Some(char!('a'))));
        assert!(test(parse_quote(), "'a'", Some(char!('a'))));
        assert!(test(
            parse_syntax(),
            "'(a b)",
            Some(Syntax::Quote(
                Pos::No,
                Box::new(list!([rel_path!(["a"]), rel_path!(["b"])]))
            ))
        ));
        assert!(test(
            parse_syntax(),
            "('a)",
            Some(list!([Syntax::Quote(Pos::No, Box::new(rel_path!(['a'])))]))
        ));

        assert!(test(
            parse_syntax(),
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
            "0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000",
            Some(Syntax::Num(
                Pos::No,
                Num::Scalar(<Scalar as ff::Field>::ZERO - Scalar::from(1u64))
            )),
        ));
        assert!(test(
            parse_num(),
            "0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001",
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
            0x6e, 0x2e, 0x50, 0x55, 0xdc, 0xf6, 0x14, 0x86, 0xb0, 0x3b, 0xb8, 0x0e, 0xd2, 0xb3,
            0xf1, 0xa3, 0x5c, 0x30, 0xe1, 0x22, 0xde, 0xfe, 0xba, 0xe8, 0x24, 0xfa, 0xe4, 0xed,
            0x32, 0x40, 0x8e, 0x87,
        ]
        .into_iter()
        .rev()
        .collect();
        assert!(test(
            parse_syntax(),
            "(0x6e2e5055dcf61486b03bb80ed2b3f1a35c30e122defebae824fae4ed32408e87)",
            Some(list!([num!(Num::Scalar(f_from_le_bytes(&vec)))])),
        ));

        assert!(test(parse_syntax(), ".\\.", Some(sym_path!(["."]))));
        assert!(test(parse_syntax(), ".\\'", Some(sym_path!(["'"]))));
        assert!(test(
            parse_syntax(),
            ".\\'\\u{8e}\\u{fffc}\\u{201b}",
            Some(sym_path!(["'\u{8e}\u{fffc}\u{201b}"])),
        ));
        assert!(test(
            parse_syntax(),
            "(lambda (🚀) 🚀)",
            Some(list!([
                rel_path!(["lambda"]),
                list!([rel_path!(["🚀"])]),
                rel_path!(["🚀"])
            ])),
        ));
        assert!(test(
            parse_syntax(),
            "11242421860377074631u64",
            Some(uint!(11242421860377074631))
        ));

        assert!(test(
            parse_syntax(),
            ":\u{ae}\u{60500}\u{87}..)",
            Some(key_path!(["®\u{60500}\u{87}", ""]))
        ));
        assert!(test(
            parse_syntax(),
            "(~:() 11242421860377074631u64 . :\u{ae}\u{60500}\u{87}..)",
            Some(list!(
                [key_path!([]), uint!(11242421860377074631)],
                key_path!(["®\u{60500}\u{87}", ""])
            ))
        ));
        assert!(test(
            parse_syntax(),
            "((\"\"))",
            Some(list!([list!([Syntax::String(Pos::No, "".to_string())])]))
        ));

        assert!(test(
            parse_syntax(),
            "((=))",
            Some(list!([list!([rel_path!(["="])])]))
        ));
        assert!(test(
            parse_syntax(),
            "('.. . a)",
            Some(list!(
                [Syntax::Quote(Pos::No, Box::new(sym_path!([""])))],
                rel_path!(["a"])
            ))
        ));
        assert_eq!(
            "(.. . a)",
            format!("{}", list!(Scalar, [sym_path!([""])], rel_path!(["a"])))
        );
        assert_eq!(
            "('.. . a)",
            format!(
                "{}",
                list!(
                    Scalar,
                    [Syntax::Quote(Pos::No, Box::new(sym_path!([""])))],
                    rel_path!(["a"])
                )
            )
        );
        assert!(test(parse_syntax(), "'\\('", Some(char!('('))));
        assert_eq!("'\\('", format!("{}", char!(Scalar, '(')));
        assert_eq!(
            "(' ' . a)",
            format!("{}", list!(Scalar, [char!(' ')], rel_path!(["a"])))
        );
        assert!(test(
            parse_syntax(),
            "(' ' . a)",
            Some(list!([char!(' ')], rel_path!(["a"])))
        ));
        assert!(test(parse_syntax(), "(cons # \"\")", None));
        assert!(test(parse_syntax(), "#", None));
    }

    #[test]
    fn test_minus_zero_symbol() {
        let x: Syntax<Scalar> = sym_path!(["-0"]);
        let text = format!("{}", x);
        let (_, res) = parse_syntax()(Span::new(&text)).expect("valid parse");
        // eprintln!("------------------");
        // eprintln!("{}", text);
        // eprintln!("{} {:?}", x, x);
        // eprintln!("{} {:?}", res, res);
        assert_eq!(x, res)
    }

    proptest! {
        #[test]
        fn prop_syntax(x in any::<Syntax<Scalar>>()) {
            let text = format!("{}", x);
            let (_, res) = parse_syntax()(Span::new(&text)).expect("valid parse");
            // eprintln!("------------------");
            // eprintln!("x {} {:?}", x, x);
            // eprintln!("res {} {:?}", res, res);
            assert_eq!(x, res)
        }
    }
}
