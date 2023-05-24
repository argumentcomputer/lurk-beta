use crate::field::LurkField;
use nom::{
    branch::alt,
    bytes::complete::{tag, take_till},
    character::complete::{anychar, char, multispace0, multispace1, none_of},
    combinator::{opt, peek, success, value},
    error::context,
    multi::{many0, separated_list1},
    sequence::{delimited, preceded, terminated},
    IResult,
};

use crate::{
    num::Num,
    parser::{
        base,
        error::{ParseError, ParseErrorKind},
        position::Pos,
        string, Span,
    },
    symbol,
    symbol::Symbol,
    syntax::Syntax,
    uint::UInt,
};

pub fn parse_line_comment<F: LurkField>(
    i: Span<'_>,
) -> IResult<Span<'_>, Span<'_>, ParseError<Span<'_>, F>> {
    let (i, _) = tag(";;")(i)?;
    let (i, com) = take_till(|c| c == '\n')(i)?;
    Ok((i, com))
}
pub fn parse_space<F: LurkField>(
    i: Span<'_>,
) -> IResult<Span<'_>, Vec<Span<'_>>, ParseError<Span<'_>, F>> {
    let (i, _) = multispace0(i)?;
    let (i, com) = many0(terminated(parse_line_comment, multispace1))(i)?;
    Ok((i, com))
}
pub fn parse_space1<F: LurkField>(
    i: Span<'_>,
) -> IResult<Span<'_>, Vec<Span<'_>>, ParseError<Span<'_>, F>> {
    let (i, _) = multispace1(i)?;
    let (i, com) = many0(terminated(parse_line_comment, multispace1))(i)?;
    Ok((i, com))
}

pub fn parse_symbol_limb<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, String, ParseError<Span<'_>, F>> {
    move |from: Span<'_>| {
        let (i, s) = alt((
            delimited(
                tag("|"),
                string::parse_string_inner1('|', true, "|"),
                tag("|"),
            ),
            string::parse_string_inner1(symbol::SYM_SEPARATOR, false, symbol::ESCAPE_CHARS),
            string::parse_string_inner1(symbol::SYM_SEPARATOR, false, symbol::ESCAPE_CHARS),
            value(String::from(""), peek(tag("."))),
        ))(from)?;
        Ok((i, s))
    }
}

pub fn parse_symbol_inner<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Symbol, ParseError<Span<'_>, F>> {
    move |from: Span<'_>| {
        let key_mark = symbol::KEYWORD_MARKER;
        let sym_mark = symbol::SYM_MARKER;
        let sym_sep = symbol::SYM_SEPARATOR;
        let (i, (is_root, mark)) = alt((
            value((true, key_mark), tag("~:()")),
            value((true, sym_mark), tag("~()")),
            // .foo
            value((false, sym_mark), char(sym_mark)),
            // :foo
            value((false, key_mark), char(key_mark)),
            // foo
            value((false, sym_mark), peek(none_of("',~#(){}[]1234567890"))),
        ))(from)?;
        if is_root && mark == key_mark {
            Ok((i, Symbol::Key(vec![])))
        } else if is_root && mark == sym_mark {
            Ok((i, Symbol::Sym(vec![])))
        } else {
            let (i, path) = separated_list1(char(sym_sep), parse_symbol_limb())(i)?;
            let (upto, _) = opt(tag("."))(i)?;
            if mark == key_mark {
                Ok((upto, Symbol::Key(path)))
            } else {
                Ok((upto, Symbol::Sym(path)))
            }
        }
    }
}

pub fn parse_symbol<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
    move |from: Span<'_>| {
        let (upto, sym) = parse_symbol_inner()(from)?;
        let pos = Pos::from_upto(from, upto);
        if let Some(val) = Symbol::lurk_syms().get(&Symbol::lurk_sym(&format!("{}", sym))) {
            Ok((upto, Syntax::LurkSym(pos, *val)))
        } else {
            Ok((upto, Syntax::Symbol(pos, sym)))
        }
    }
}

pub fn parse_uint<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
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
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Num<F>, ParseError<Span<'_>, F>> {
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

pub fn parse_num<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
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

pub fn parse_string<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
    move |from: Span<'_>| {
        let (upto, s) = string::parse_string('"')(from)?;
        let pos = Pos::from_upto(from, upto);
        Ok((upto, Syntax::String(pos, s)))
    }
}

// hash syntax for chars
pub fn parse_hash_char<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
    |from: Span<'_>| {
        let (i, _) = tag("#\\")(from)?;
        let (upto, c) = alt((string::parse_unicode(), anychar))(i)?;
        let pos = Pos::from_upto(from, upto);
        Ok((upto, Syntax::Char(pos, c)))
    }
}

pub fn parse_char<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
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
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
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

pub fn parse_quote<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
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
pub fn parse_syntax<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
    move |from: Span<'_>| {
        alt((
            parse_hash_char(),
            parse_uint(),
            parse_num(),
            context("symbol", parse_symbol()),
            parse_string(),
            context("quote", parse_quote()),
            context("list", parse_list()),
        ))(from)
    }
}

pub fn parse_maybe_meta<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Option<(bool, Syntax<F>)>, ParseError<Span<'_>, F>> {
    move |from: Span<'_>| {
        let (_, is_eof) = opt(nom::combinator::eof)(from)?;
        if is_eof.is_some() {
            return Ok((from, None))
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
    use crate::symbol::LurkSym;
    use blstrs::Scalar;
    use nom::Parser;
    #[cfg(not(target_arch = "wasm32"))]
    use proptest::prelude::*;

    use super::*;
    #[allow(unused_imports)]
    use crate::{char, keyword, list, num, str, symbol, uint};

    fn test<'a, P>(mut p: P, i: &'a str, expected: Option<Syntax<Scalar>>) -> bool
    where
        P: Parser<Span<'a>, Syntax<Scalar>, ParseError<Span<'a>, Scalar>>,
    {
        match (expected, p.parse(Span::<'a>::new(i))) {
            (Some(expected), Ok((_i, x))) if x == expected => true,
            (Some(expected), Ok((_i, x))) => {
                println!("input: {:?}", i);
                println!("expected: {} {:?}", expected.clone(), expected);
                println!("detected: {} {:?}", x.clone(), x);
                false
            }
            (Some(..), Err(e)) => {
                println!("{}", e);
                false
            }
            (None, Ok((i, x))) => {
                println!("input: {:?}", i);
                println!("expected parse error");
                println!("detected: {:?}", x);
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
        assert!(test(parse_symbol(), "", None));
        assert!(test(parse_symbol(), "~()", Some(symbol!([]))));
        assert!(test(parse_symbol(), ".", None));
        assert!(test(parse_symbol(), "..", Some(symbol!([""]))));
        assert!(test(parse_symbol(), "foo", Some(symbol!(["foo"]))));
        assert!(test(parse_symbol(), "|foo|", Some(symbol!(["foo"]))));
        assert!(test(
            parse_symbol(),
            "|foo|.|bar|",
            Some(symbol!(["foo", "bar"]))
        ));
        assert!(test(
            parse_symbol(),
            ".|foo|.|bar|",
            Some(symbol!(["foo", "bar"]))
        ));
        assert!(test(parse_symbol(), ".foo", Some(symbol!(["foo"]))));
        assert!(test(parse_symbol(), "..foo", Some(symbol!(["", "foo"]))));
        assert!(test(parse_symbol(), "foo.", Some(symbol!(["foo"]))));
        assert!(test(parse_symbol(), "foo..", Some(symbol!(["foo", ""]))));
        assert!(test(parse_symbol(), ".foo..", Some(symbol!(["foo", ""]))));
        assert!(test(parse_symbol(), ".foo..", Some(symbol!(["foo", ""]))));
        assert!(test(
            parse_symbol(),
            ".foo.bar",
            Some(symbol!(["foo", "bar"]))
        ));
        assert!(test(
            parse_symbol(),
            ".foo?.bar?",
            Some(symbol!(["foo?", "bar?"]))
        ));
        assert!(test(
            parse_symbol(),
            ".fooλ.barλ",
            Some(symbol!(["fooλ", "barλ"]))
        ));
        assert!(test(
            parse_symbol(),
            ".foo\\n.bar\\n",
            Some(symbol!(["foo\n", "bar\n"]))
        ));
        assert!(test(
            parse_symbol(),
            ".foo\\u{00}.bar\\u{00}",
            Some(symbol!(["foo\u{00}", "bar\u{00}"]))
        ));
        assert!(test(
            parse_symbol(),
            ".foo\\.bar",
            Some(symbol!(["foo.bar"]))
        ));
        assert!(test(
            parse_symbol(),
            "nil",
            Some(Syntax::LurkSym(Pos::No, LurkSym::Nil))
        ));
    }

    #[test]
    fn unit_parse_keyword() {
        assert!(test(parse_symbol(), "", None));
        assert!(test(parse_symbol(), "~:()", Some(keyword!([]))));
        assert!(test(parse_symbol(), ":", None));
        assert!(test(parse_symbol(), ":.", Some(keyword!([""]))));
        assert!(test(parse_symbol(), ":foo", Some(keyword!(["foo"]))));
        assert!(test(parse_symbol(), ":.foo", Some(keyword!(["", "foo"]))));
        assert!(test(parse_symbol(), ":foo.", Some(keyword!(["foo"]))));
        assert!(test(parse_symbol(), ":foo..", Some(keyword!(["foo", ""]))));
        assert!(test(
            parse_symbol(),
            ":foo.bar",
            Some(keyword!(["foo", "bar"]))
        ));
        assert!(test(
            parse_symbol(),
            ":foo?.bar?",
            Some(keyword!(["foo?", "bar?"]))
        ));
        assert!(test(
            parse_symbol(),
            ":fooλ.barλ",
            Some(keyword!(["fooλ", "barλ"]))
        ));
        assert!(test(
            parse_symbol(),
            ":foo\\n.bar\\n",
            Some(keyword!(["foo\n", "bar\n"]))
        ));
        assert!(test(
            parse_symbol(),
            ":foo\\u{00}.bar\\u{00}",
            Some(keyword!(["foo\u{00}", "bar\u{00}"]))
        ));
        assert!(test(
            parse_symbol(),
            ":foo\\.bar",
            Some(keyword!(["foo.bar"]))
        ));
    }
    #[test]
    fn unit_parse_list() {
        assert!(test(parse_list(), "()", Some(list!([]))));
        assert!(test(parse_list(), "(1 2)", Some(list!([num!(1), num!(2)])),));
        assert!(test(parse_list(), "(1)", Some(list!([num!(1)])),));
        assert!(test(parse_list(), "(a)", Some(list!([symbol!(["a"])])),));
        assert!(test(
            parse_list(),
            "(a b)",
            Some(list!([symbol!(["a"]), symbol!(["b"])])),
        ));
        assert!(test(
            parse_syntax(),
            "(.a .b)",
            Some(list!([symbol!(["a"]), symbol!(["b"])])),
        ));
        assert!(test(
            parse_syntax(),
            "(.foo.bar .foo.bar)",
            Some(list!([symbol!(["foo", "bar"]), symbol!(["foo", "bar"])])),
        ));
        assert!(test(
            parse_syntax(),
            "(a . b)",
            Some(list!([symbol!(["a"])], symbol!(["b"]))),
        ));
        assert!(test(
            parse_syntax(),
            "(.a . .b)",
            Some(list!([symbol!(["a"])], symbol!(["b"]))),
        ));
        assert!(test(
            parse_syntax(),
            "(a b . c)",
            Some(list!([symbol!(["a"]), symbol!(["b"])], symbol!(["c"]))),
        ));
        assert!(test(
            parse_syntax(),
            "(a . (b . c))",
            Some(list!(
                [symbol!(["a"])],
                list!([symbol!(["b"])], symbol!(["c"]))
            ))
        ));
        assert!(test(
            parse_syntax(),
            "(a b c)",
            Some(list!([symbol!(["a"]), symbol!(["b"]), symbol!(["c"])])),
        ));
        assert!(test(
            parse_syntax(),
            "('a' 'b' 'c')",
            Some(list!([char!('a'), char!('b'), char!('c')])),
        ));

        assert!(test(
            parse_syntax(),
            "(a. b. c.)",
            Some(list!([symbol!(["a"]), symbol!(["b"]), symbol!(["c"])])),
        ));
        assert!(test(
            parse_syntax(),
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
        assert!(test(parse_char(), "'('", None));
        assert!(test(parse_char(), "'\\('", Some(char!('('))));
    }
    #[test]
    fn unit_parse_hash_char() {
        assert!(test(parse_hash_char(), "#\\a", Some(char!('a'))));
        assert!(test(parse_hash_char(), "#\\b", Some(char!('b'))));
        assert!(test(parse_hash_char(), r#"#\b"#, Some(char!('b'))));
        assert!(test(parse_hash_char(), "#\\u{8f}", Some(char!('\u{8f}'))));
        assert!(test(parse_syntax(), "#\\a", Some(char!('a'))));
        assert!(test(parse_syntax(), "#\\b", Some(char!('b'))));
        assert!(test(parse_syntax(), r#"#\b"#, Some(char!('b'))));
        assert!(test(parse_syntax(), r#"#\u{8f}"#, Some(char!('\u{8f}'))));
    }

    #[test]
    fn unit_parse_quote() {
        assert!(test(
            parse_quote(),
            "'a",
            Some(Syntax::Quote(Pos::No, Box::new(symbol!(["a"]))))
        ));
        assert!(test(
            parse_syntax(),
            "'a",
            Some(Syntax::Quote(Pos::No, Box::new(symbol!(["a"]))))
        ));
        assert!(test(parse_quote(), "'a'", Some(char!('a'))));
        assert!(test(parse_quote(), "'a'", Some(char!('a'))));
        assert!(test(
            parse_syntax(),
            "'(a b)",
            Some(Syntax::Quote(
                Pos::No,
                Box::new(list!([symbol!(["a"]), symbol!(["b"])]))
            ))
        ));
        assert!(test(
            parse_syntax(),
            "('a)",
            Some(list!([Syntax::Quote(Pos::No, Box::new(symbol!(['a'])))]))
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
        assert!(test(parse_num(), "0b0", Some(num!(0))));
        assert!(test(parse_num(), "0o0", Some(num!(0))));
        assert!(test(parse_num(), "0d0", Some(num!(0))));
        assert!(test(parse_num(), "0x0", Some(num!(0))));
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
        //assert!(test(
        //    parse_num(),
        //    "1/2",
        //    Some(num!(
        //        0x39f6d3a994cebea4199cec0404d0ec02a9ded2017fff2dff7fffffff80000001
        //    ))
        //));
        //assert!(test(parse_num(), "-1/2", Some(num!(0))));
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

        assert!(test(parse_syntax(), ".\\.", Some(symbol!(["."]))));
        assert!(test(parse_syntax(), ".\\'", Some(symbol!(["'"]))));
        assert!(test(
            parse_syntax(),
            ".\\'\\u{8e}\\u{fffc}\\u{201b}",
            Some(symbol!(["'\u{8e}\u{fffc}\u{201b}"])),
        ));
        assert!(test(
            parse_syntax(),
            "(lambda (🚀) 🚀)",
            Some(list!([
                Syntax::LurkSym(Pos::No, LurkSym::Lambda),
                list!([symbol!(["🚀"])]),
                symbol!(["🚀"])
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
            Some(keyword!(["®\u{60500}\u{87}", ""]))
        ));
        assert!(test(
            parse_syntax(),
            "(~:() 11242421860377074631u64 . :\u{ae}\u{60500}\u{87}..)",
            Some(list!(
                [keyword!([]), uint!(11242421860377074631)],
                keyword!(["®\u{60500}\u{87}", ""])
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
            Some(list!([list!([Syntax::LurkSym(Pos::No, LurkSym::OpEql)])]))
        ));
        assert!(test(
            parse_syntax(),
            "('.. . a)",
            Some(list!(
                [Syntax::Quote(Pos::No, Box::new(symbol!([""])))],
                symbol!(["a"])
            ))
        ));
        assert_eq!(
            "(.. . a)",
            format!("{}", list!(Scalar, [symbol!([""])], symbol!(["a"])))
        );
        assert_eq!(
            "('.. . a)",
            format!(
                "{}",
                list!(
                    Scalar,
                    [Syntax::Quote(Pos::No, Box::new(symbol!([""])))],
                    symbol!(["a"])
                )
            )
        );
        assert!(test(parse_syntax(), "'\\('", Some(char!('('))));
        assert_eq!("'\\('", format!("{}", char!(Scalar, '(')));
        assert_eq!(
            "(' ' . a)",
            format!("{}", list!(Scalar, [char!(' ')], symbol!(["a"])))
        );
        assert!(test(
            parse_syntax(),
            "(' ' . a)",
            Some(list!([char!(' ')], symbol!(["a"])))
        ));
    }

    proptest! {
        #[test]
        fn prop_syntax(x in any::<Syntax<Scalar>>()) {
            let text = format!("{}", x);
            let (_, res)  = parse_syntax()(Span::new(&text)).expect("valid parse");
            eprintln!("------------------");
            eprintln!("x {} {:?}", x, x);
            eprintln!("res {} {:?}", res, res);
            assert_eq!(x, res)
        }
    }
}
