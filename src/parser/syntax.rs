use crate::field::LurkField;
use nom::{
    branch::alt,
    bytes::complete::{tag, take_till},
    character::complete::{char, multispace0, multispace1, none_of},
    combinator::{opt, peek, success, value},
    multi::{many0, separated_list0, separated_list1},
    sequence::{preceded, terminated},
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
    symbol::LurkSym,
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

pub fn parse_symbol_root<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
    move |from: Span<'_>| {
        let (upto, s) = alt((
            value(Symbol::Key(vec![]), tag("_:")),
            value(Symbol::Sym(vec![]), tag("_.")),
        ))(from)?;
        let pos = Pos::from_upto(from, upto);
        Ok((upto, Syntax::Symbol(pos, s)))
    }
}

pub fn parse_symbol_inner<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
    move |from: Span<'_>| {
        let (i, is_key) = alt((
            // :foo
            value(true, char(symbol::KEYWORD_MARKER)),
            // .foo
            value(false, char(symbol::SYM_MARKER)),
            // foo
            value(false, peek(none_of("'()"))),
        ))(from)?;
        let (upto, path) = separated_list1(
            char(symbol::SYM_SEPARATOR),
            string::parse_string_inner(symbol::SYM_SEPARATOR, false, symbol::ESCAPE_CHARS),
        )(i)?;
        let pos = Pos::from_upto(from, upto);
        if is_key {
            Ok((i, Syntax::Symbol(pos, Symbol::Key(path))))
        } else {
            Ok((i, Syntax::Symbol(pos, Symbol::Sym(path))))
        }
    }
}

pub fn parse_symbol<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
    move |from: Span<'_>| {
        let (i, sym) = alt((parse_symbol_root(), parse_lurksym(), parse_symbol_inner()))(from)?;
        Ok((i, sym))
    }
}

pub fn parse_lurksym<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
    move |from: Span<'_>| {
        let (i, _) = opt(char(symbol::SYM_MARKER))(from)?;
        let (upto, lurksym) = alt((
            value(LurkSym::Atom, tag("atom")),
            value(LurkSym::Begin, tag("begin")),
            value(LurkSym::Car, tag("car")),
            value(LurkSym::Cdr, tag("cdr")),
            value(LurkSym::Char, tag("char")),
            value(LurkSym::Comm, tag("comm")),
            value(LurkSym::Commit, tag("commit")),
            value(LurkSym::Cons, tag("cons")),
            value(LurkSym::CurrentEnv, tag("current-env")),
            value(LurkSym::Emit, tag("emit")),
            value(LurkSym::Eval, tag("eval")),
            value(LurkSym::Eq, tag("eq")),
            value(LurkSym::Hide, tag("hide")),
            value(LurkSym::If, tag("if")),
            value(LurkSym::Lambda, tag("lambda")),
            value(LurkSym::Let, tag("let")),
            value(LurkSym::Letrec, tag("letrec")),
            value(LurkSym::Nil, tag("nil")),
            value(LurkSym::Num, tag("num")),
            value(LurkSym::U64, tag("u64")),
            alt((
                value(LurkSym::Open, tag("open")),
                value(LurkSym::Quote, tag("quote")),
                value(LurkSym::Secret, tag("secret")),
                value(LurkSym::Strcons, tag("strcons")),
                value(LurkSym::T, tag("t")),
                value(LurkSym::OpAdd, tag("+")),
                value(LurkSym::OpSub, tag("-")),
                value(LurkSym::OpMul, tag("*")),
                value(LurkSym::OpDiv, tag("/")),
                value(LurkSym::OpMod, tag("%")),
                value(LurkSym::OpEql, tag("=")),
                value(LurkSym::OpLth, tag("<")),
                value(LurkSym::OpGth, tag(">")),
                value(LurkSym::OpLte, tag("<=")),
                value(LurkSym::OpGte, tag(">=")),
                value(LurkSym::Dummy, tag("_")),
            )),
        ))(i)?;
        let pos = Pos::from_upto(from, upto);
        Ok((upto, Syntax::LurkSym(pos, lurksym)))
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

pub fn parse_num<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
    move |from: Span<'_>| {
        let (i, base) = alt((
            preceded(tag("0"), base::parse_litbase_code()),
            success(base::LitBase::Dec),
        ))(from)?;
        let (upto, bytes): (Span<'_>, Vec<u8>) = base::parse_litbase_le_bytes(base)(i)?;
        let max_bytes = (F::zero() - F::one()).to_bytes();
        let max_uint = num_bigint::BigUint::from_bytes_le(&max_bytes);
        if num_bigint::BigUint::from_bytes_le(&bytes) > max_uint {
            ParseError::throw(
                from,
                ParseErrorKind::NumLiteralTooBig(F::most_positive(), max_uint),
            )
        } else {
            let pos = Pos::from_upto(from, upto);
            let (_, f) = ParseError::opt(
                F::from_bytes(&bytes),
                from,
                ParseErrorKind::NumError(format!("can't read number")),
            )?;
            if let Some(x) = f.to_u64() {
                Ok((upto, Syntax::Num(pos, Num::U64(x))))
            } else {
                Ok((upto, Syntax::Num(pos, Num::Scalar(f))))
            }
        }
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

pub fn parse_char<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
    move |from: Span<'_>| {
        let (upto, s) = string::parse_string('\'')(from)?;
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
        let (i, _) = parse_space(i)?;
        let (i, xs) = separated_list0(parse_space1, parse_syntax())(i)?;
        let (i, is_improper) = opt(preceded(parse_space, tag(".")))(i)?;
        if is_improper.is_some() {
            let (i, end) = preceded(parse_space, parse_syntax())(i)?;
            let (upto, _) = tag(")")(i)?;
            let pos = Pos::from_upto(from, upto);
            Ok((upto, Syntax::Improper(pos, xs, Box::new(end))))
        } else {
            let (upto, _) = tag(")")(i)?;
            let pos = Pos::from_upto(from, upto);
            Ok((upto, Syntax::List(pos, xs)))
        }
    }
}

pub fn parse_quote<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
    move |from: Span<'_>| {
        let (i, _) = tag("'")(from)?;
        let (upto, s) = parse_syntax()(i)?;
        let pos = Pos::from_upto(from, upto);
        Ok((i, Syntax::Quote(pos, Box::new(s))))
    }
}

// top-level syntax parser
pub fn parse_syntax<F: LurkField>(
) -> impl Fn(Span<'_>) -> IResult<Span<'_>, Syntax<F>, ParseError<Span<'_>, F>> {
    move |from: Span<'_>| {
        alt((
            parse_num(),
            parse_uint(),
            parse_char(),
            parse_string(),
            parse_symbol(),
            parse_list(),
            parse_quote(),
        ))(from)
    }
}

//#[cfg(test)]
//pub mod tests {
//    use crate::field::FWrap;
//    use blstrs::Scalar as Fr;
//    use nom::Parser;
//
//    use super::*;
//    #[allow(unused_imports)]
//    use crate::{char, keyword, list, map, num, str, symbol, u64};
//
//    fn test<'a, P>(mut p: P, i: &'a str, expected: Option<Syn<Fr>>) -> bool
//    where
//        P: Parser<Span<'_><'a>, Syn<Fr>, ParseError<Span<'_><'a>, Fr>>,
//    {
//        match (expected, p.parse(Span<'_>::new(i))) {
//            (Some(expected), Ok((_i, x))) if x == expected => true,
//            (Some(expected), Ok((i, x))) => {
//                println!("input: {:?}", i);
//                println!("expected: {}", expected);
//                println!("detected: {}", x);
//                false
//            }
//            (Some(..), Err(e)) => {
//                println!("{}", e);
//                false
//            }
//            (None, Ok((i, x))) => {
//                println!("input: {:?}", i);
//                println!("expected parse error");
//                println!("detected: {:?}", x);
//                false
//            }
//            (None, Err(_e)) => true,
//        }
//    }
//
//    #[test]
//    fn unit_parse_string() {
//        assert!(test(parse_syn_str(), "\"foo\"", Some(str!("foo"))));
//        assert!(test(parse_syn_str(), "\"fo\\no\"", Some(str!("fo\no"))));
//        assert!(test(
//            parse_syn_str(),
//            "\"fo\\u{00}o\"",
//            Some(str!("fo\u{00}o"))
//        ));
//        assert!(test(parse_syn_str(), "\"foo\\   \"", Some(str!("foo"))));
//    }
//
//    #[test]
//    fn unit_parse_symbol() {
//        assert!(test(parse_syn_sym(), "", None));
//        assert!(test(parse_syn(), "_.", Some(symbol!([]))));
//        assert!(test(parse_syn(), ".", Some(symbol!([""]))));
//        assert!(test(parse_syn(), "..", Some(symbol!(["", ""]))));
//        assert!(test(parse_syn(), "foo", Some(symbol!(["foo"]))));
//        assert!(test(parse_syn(), ".foo", Some(symbol!(["foo"]))));
//        assert!(test(parse_syn(), "..foo", Some(symbol!(["", "foo"]))));
//        assert!(test(parse_syn(), "foo.", Some(symbol!(["foo", ""]))));
//        assert!(test(parse_syn(), ".foo.", Some(symbol!(["foo", ""]))));
//        assert!(test(parse_syn(), ".foo..", Some(symbol!(["foo", "", ""]))));
//        assert!(test(parse_syn(), ".foo.bar", Some(symbol!(["foo", "bar"]))));
//        assert!(test(
//            parse_syn(),
//            ".foo?.bar?",
//            Some(symbol!(["foo?", "bar?"]))
//        ));
//        assert!(test(
//            parse_syn(),
//            ".fooλ.barλ",
//            Some(symbol!(["fooλ", "barλ"]))
//        ));
//        assert!(test(
//            parse_syn(),
//            ".foo\\n.bar\\n",
//            Some(symbol!(["foo\n", "bar\n"]))
//        ));
//        assert!(test(
//            parse_syn(),
//            ".foo\\u{00}.bar\\u{00}",
//            Some(symbol!(["foo\u{00}", "bar\u{00}"]))
//        ));
//        assert!(test(parse_syn(), ".foo\\.bar", Some(symbol!(["foo.bar"]))));
//    }
//
//    #[test]
//    fn unit_parse_keyword() {
//        assert!(test(parse_syn_sym(), "", None));
//        assert!(test(parse_syn(), "_:", Some(keyword!([]))));
//        assert!(test(parse_syn(), ":", Some(keyword!([""]))));
//        assert!(test(parse_syn(), ":.", Some(keyword!(["", ""]))));
//        assert!(test(parse_syn(), ":foo", Some(keyword!(["foo"]))));
//        assert!(test(parse_syn(), ":.foo", Some(keyword!(["", "foo"]))));
//        assert!(test(parse_syn(), ":foo.", Some(keyword!(["foo", ""]))));
//        assert!(test(parse_syn(), ":foo..", Some(keyword!(["foo", "", ""]))));
//        assert!(test(
//            parse_syn(),
//            ":foo.bar",
//            Some(keyword!(["foo", "bar"]))
//        ));
//        assert!(test(
//            parse_syn(),
//            ":foo?.bar?",
//            Some(keyword!(["foo?", "bar?"]))
//        ));
//        assert!(test(
//            parse_syn(),
//            ":fooλ.barλ",
//            Some(keyword!(["fooλ", "barλ"]))
//        ));
//        assert!(test(
//            parse_syn(),
//            ":foo\\n.bar\\n",
//            Some(keyword!(["foo\n", "bar\n"]))
//        ));
//        assert!(test(
//            parse_syn(),
//            ":foo\\u{00}.bar\\u{00}",
//            Some(keyword!(["foo\u{00}", "bar\u{00}"]))
//        ));
//        assert!(test(parse_syn(), ":foo\\.bar", Some(keyword!(["foo.bar"]))));
//    }
//
//    #[test]
//    fn unit_parse_map() {
//        assert!(test(parse_syn(), "{}", Some(map!([]))));
//        assert!(test(
//            parse_syn(),
//            "{ 'a' = 1u64,  'b' = 2u64,  'c' = 3u64 }",
//            Some(map!([
//                (char!('a'), u64!(1)),
//                (char!('b'), u64!(2)),
//                (char!('c'), u64!(3))
//            ]))
//        ));
//        assert!(test(
//            parse_syn(),
//            "{ :a = 1u64,  :b = 2u64,  :c = 3u64 }",
//            Some(map!([
//                (keyword!(["a"]), u64!(1)),
//                (keyword!(["b"]), u64!(2)),
//                (keyword!(["c"]), u64!(3))
//            ]))
//        ));
//    }
//
//    #[test]
//    fn unit_parse_list() {
//        assert!(test(parse_syn(), "()", Some(symbol!(["lurk", "nil"]))));
//        assert!(test(
//            parse_syn(),
//            "(a b)",
//            Some(list!([symbol!(["a"]), symbol!(["b"])])),
//        ));
//        assert!(test(
//            parse_syn(),
//            "(.a .b)",
//            Some(list!([symbol!(["a"]), symbol!(["b"])])),
//        ));
//        assert!(test(
//            parse_syn(),
//            "(.LURK.LAMBDA .LURK.LAMBDA)",
//            Some(list!([
//                symbol!(["LURK", "LAMBDA"]),
//                symbol!(["LURK", "LAMBDA"])
//            ])),
//        ));
//        assert!(test(
//            parse_syn(),
//            "(a, b)",
//            Some(list!([symbol!(["a"])], symbol!(["b"]))),
//        ));
//        assert!(test(
//            parse_syn(),
//            "(.a, .b)",
//            Some(list!([symbol!(["a"])], symbol!(["b"]))),
//        ));
//        assert!(test(
//            parse_syn(),
//            "(a, b, c)",
//            Some(list!([symbol!(["a"]), symbol!(["b"])], symbol!(["c"]))),
//        ));
//        assert!(test(
//            parse_syn(),
//            "(a, (b, c))",
//            Some(list!([symbol!(["a"]), symbol!(["b"])], symbol!(["c"]))),
//        ));
//        assert!(test(
//            parse_syn(),
//            "(a b c)",
//            Some(list!([symbol!(["a"]), symbol!(["b"]), symbol!(["c"])])),
//        ));
//        assert!(test(
//            parse_syn(),
//            "('a' 'b' 'c')",
//            Some(list!([char!('a'), char!('b'), char!('c')])),
//        ));
//    }
//
//    #[test]
//    fn unit_parse_char() {
//        assert!(test(parse_syn(), "'a'", Some(char!('a'))));
//        assert!(test(parse_syn(), "'b'", Some(char!('b'))));
//        assert!(test(parse_syn(), "'\\u{8f}'", Some(char!('\u{8f}'))));
//    }
//
//    #[test]
//    fn unit_parse_num() {
//        assert!(test(parse_syn(), "0", Some(num!(0))));
//        assert!(test(parse_syn(), "0b0", Some(num!(0))));
//        assert!(test(parse_syn(), "0o0", Some(num!(0))));
//        assert!(test(parse_syn(), "0d0", Some(num!(0))));
//        assert!(test(parse_syn(), "0x0", Some(num!(0))));
//        assert!(test(
//            parse_syn(),
//            "0xffff_ffff_ffff_ffff",
//            Some(num!(0xffff_ffff_ffff_ffff))
//        ));
//        assert!(test(
//            parse_syn(),
//            "0x1234_5678_9abc_def0",
//            Some(num!(0x1234_5678_9abc_def0))
//        ));
//        assert!(test(
//            parse_syn(),
//            &format!("0x{}", Fr::most_positive().hex_digits()),
//            Some(num!(Fr::most_positive()))
//        ));
//        assert!(test(
//            parse_syn(),
//            "0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000",
//            Some(Syn::Num(
//                Pos::No,
//                <Fr as ff::Field>::zero() - Fr::from(1u64)
//            )),
//        ));
//        assert!(test(
//            parse_syn(),
//            "0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001",
//            None,
//        ));
//    }
//
//    // (1 2)
//    // Cons(Num(1), Num(2))
//    // (.1 .2)
//    // Cons(Sym(vec!["1"]), Sym(vec!["2"]))
//    #[test]
//    fn unit_parse_syn_misc() {
//        let vec: Vec<u8> = vec![
//            0x6e, 0x2e, 0x50, 0x55, 0xdc, 0xf6, 0x14, 0x86, 0xb0, 0x3b, 0xb8, 0x0e, 0xd2, 0xb3,
//            0xf1, 0xa3, 0x5c, 0x30, 0xe1, 0x22, 0xde, 0xfe, 0xba, 0xe8, 0x24, 0xfa, 0xe4, 0xed,
//            0x32, 0x40, 0x8e, 0x87,
//        ]
//        .into_iter()
//        .rev()
//        .collect();
//        assert!(test(
//            parse_syn(),
//            "(0x6e2e5055dcf61486b03bb80ed2b3f1a35c30e122defebae824fae4ed32408e87)",
//            Some(list!([num!(Fr::from_le_bytes_canonical(&vec))])),
//        ));
//
//        assert!(test(parse_syn(), ".\\.", Some(symbol!(["."]))));
//        assert!(test(parse_syn(), ".\\'", Some(symbol!(["'"]))));
//        assert!(test(
//            parse_syn(),
//            ".\\'\\u{8e}\\u{fffc}\\u{201b}",
//            Some(symbol!(["'\u{8e}\u{fffc}\u{201b}"])),
//        ));
//        assert!(test(
//            parse_syn(),
//            "(lambda (🚀) 🚀)",
//            Some(list!([
//                symbol!(["lambda"]),
//                list!([symbol!(["🚀"])]),
//                symbol!(["🚀"])
//            ])),
//        ));
//        assert!(test(
//            parse_syn(),
//            "(_:, 11242421860377074631u64, :\u{ae}\u{60500}\u{87}..)",
//            Some(list!(
//                [keyword!([]), u64!(11242421860377074631)],
//                keyword!(["®\u{60500}\u{87}", "", ""])
//            ))
//        ));
//    }
//
//    #[quickcheck]
//    fn prop_parse_num(f: FWrap<Fr>) -> bool {
//        let hex = format!("0x{}", f.0.hex_digits());
//        match parse_syn_num::<Fr>()(Span<'_>::new(&hex)) {
//            Ok((_, Syn::Num(_, f2))) => {
//                println!("f1 0x{}", f.0.hex_digits());
//                println!("f2 0x{}", f2.hex_digits());
//                f.0 == f2
//            }
//            _ => false,
//        }
//    }
//    #[quickcheck]
//    fn prop_syn_parse_print(syn: Syn<Fr>) -> bool {
//        println!("==================");
//        println!("syn1 {}", syn);
//        println!("syn1 {:?}", syn);
//        let hex = format!("{}", syn);
//        match parse_syn::<Fr>()(Span<'_>::new(&hex)) {
//            Ok((_, syn2)) => {
//                println!("syn2 {}", syn2);
//                println!("syn2 {:?}", syn2);
//                syn == syn2
//            }
//            _ => false,
//        }
//    }
//}
