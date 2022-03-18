use crate::Num;
use alloc::fmt;
use alloc::fmt::Display;
use alloc::vec::Vec;
use alloc::{boxed::Box, string::String};
use core::convert::TryInto;
use ff::PrimeField;
use num_bigint::BigUint;

// use crate::store::Expression;

use crate::parser::base;
use crate::parser::error::throw_err;
use crate::parser::error::ParseError;
use crate::parser::error::ParseErrorKind;
use crate::parser::string::parse_string;
use crate::parser::Span;

use nom::{
    branch::alt,
    bytes::complete::{tag, take_till, take_till1},
    character::complete::{digit1, multispace0, multispace1, satisfy},
    combinator::{eof, map, opt, peek, success, value},
    error::context,
    multi::{many0, many1, separated_list0, separated_list1},
    sequence::{delimited, preceded, terminated},
    Err, IResult, Parser,
};

/// A term in the front-end syntax
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term<F: PrimeField> {
    Nil,
    Cons(Box<Term<F>>, Box<Term<F>>),
    Sym(String),
    Num(Num<F>),
    Str(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Print<F: PrimeField> {
    List(Vec<Print<F>>),
    Pair(Box<Print<F>>, Box<Print<F>>),
    Sym(String),
    Num(Num<F>),
    Str(String),
}

impl<F: PrimeField> Print<F> {
    pub fn from_term(term: &Term<F>) -> Self {
        match term {
            Term::Nil => Print::List(vec![]),
            Term::Sym(x) => Print::Sym(x.clone()),
            Term::Str(x) => Print::Str(x.clone()),
            Term::Num(x) => Print::Num(x.clone()),
            Term::Cons(x, y) => match Print::from_term(y) {
                Print::List(mut xs) => {
                    xs.push(Print::from_term(x));
                    Print::List(xs)
                }
                y => Print::Pair(Box::new(Print::from_term(x)), Box::new(y)),
            },
        }
    }
    pub fn print(&self) -> String {
        match self {
            Print::List(xs) => {
                let xs: Vec<String> = xs.iter().rev().map(|x| x.print()).collect();
                format!("({})", xs.join(" "))
            }
            Print::Pair(car, cdr) => format!("({} . {})", car.print(), cdr.print()),
            Print::Str(sym) => format!("\"{}\"", sym.escape_default()),
            Print::Sym(sym) => format!("{}", sym),
            Print::Num(Num::Scalar(s)) => {
                let bytes = s.to_repr();
                let n = BigUint::from_bytes_le(bytes.as_ref());
                format!("0x{}", n.to_str_radix(16))
            }
            Print::Num(Num::U64(x)) => format!("{:#x}", x),
        }
    }
}

impl<F: PrimeField> Term<F> {
    pub fn print(&self) -> String {
        Print::from_term(&self).print()
    }
}

impl<F: PrimeField> fmt::Display for Term<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.print())
    }
}

pub fn reserved_symbols() -> Vec<String> {
    Vec::from(vec![
        String::from(";;"),
        String::from(";"),
        String::from("."),
        String::from("'"),
        String::from(")"),
        String::from("("),
    ])
}

pub fn parse_line_comment(i: Span) -> IResult<Span, Span, ParseError<Span>> {
    let (i, _) = tag(";;")(i)?;
    let (i, com) = take_till(|c| c == '\n')(i)?;
    Ok((i, com))
}
pub fn parse_space(i: Span) -> IResult<Span, Vec<Span>, ParseError<Span>> {
    let (i, _) = multispace0(i)?;
    let (i, com) = many0(terminated(parse_line_comment, multispace1))(i)?;
    Ok((i, com))
}

pub fn parse_space1(i: Span) -> IResult<Span, Vec<Span>, ParseError<Span>> {
    let (i, _) = multispace1(i)?;
    let (i, com) = many0(terminated(parse_line_comment, multispace1))(i)?;
    Ok((i, com))
}

pub fn is_numeric_symbol_string1(s: &str) -> bool {
    s.starts_with('0')
        || s.starts_with('1')
        || s.starts_with('2')
        || s.starts_with('3')
        || s.starts_with('4')
        || s.starts_with('5')
        || s.starts_with('6')
        || s.starts_with('7')
        || s.starts_with('8')
        || s.starts_with('9')
}

pub fn is_valid_symbol_char(c: char) -> bool {
    c != ';'
        && c != '.'
        && c != '\''
        && c != '('
        && c != ')'
        && !char::is_whitespace(c)
        && !char::is_control(c)
}

pub fn is_valid_symbol_string(s: &str) -> bool {
    let invalid_chars =
        s.starts_with('"') || s.starts_with('\'') || s.chars().any(|x| !is_valid_symbol_char(x));
    !s.is_empty() && !invalid_chars
}

pub fn parse_sym<F: PrimeField>() -> impl Fn(Span) -> IResult<Span, Term<F>, ParseError<Span>> {
    move |from: Span| {
        let (i, s) = take_till1(|x| char::is_whitespace(x) | (x == ')') | (x == '('))(from)?;
        let s: String = String::from(s.fragment().to_owned());
        if s == "nil" {
            Ok((i, Term::Nil))
        } else if reserved_symbols().contains(&s) {
            Err(Err::Error(ParseError::new(
                from,
                ParseErrorKind::ReservedKeyword(s),
            )))
        } else if is_numeric_symbol_string1(&s) {
            Err(Err::Error(ParseError::new(
                from,
                ParseErrorKind::NumericSyntax(s),
            )))
        } else if !is_valid_symbol_string(&s) {
            Err(Err::Error(ParseError::new(
                from,
                ParseErrorKind::InvalidSymbol(s),
            )))
        } else {
            Ok((i, Term::Sym(s)))
        }
    }
}

pub fn parse_str<F: PrimeField>() -> impl Fn(Span) -> IResult<Span, Term<F>, ParseError<Span>> {
    move |i: Span| {
        let (i, _) = context("open quotes", tag("\""))(i)?;
        let (i, s) = parse_string("\"")(i)?;
        let (upto, _) = tag("\"")(i)?;
        Ok((upto, Term::Str(s.into())))
    }
}

pub fn parse_num<F: PrimeField>() -> impl Fn(Span) -> IResult<Span, Term<F>, ParseError<Span>> {
    move |i: Span| {
        let (i, base) = opt(preceded(tag("0"), base::parse_litbase_code()))(i)?;
        let base = base.unwrap_or(base::LitBase::Dec);
        let (i, digits) = base::parse_litbase_digits(base)(i)?;
        let (i, bytes) = match base_x::decode(base.base_digits(), &digits) {
            Ok(bytes) => Ok((i, bytes)),
            Err(_) => Err(nom::Err::Error(ParseError::new(
                i,
                ParseErrorKind::InvalidBaseEncoding(base),
            ))),
        }?;
        let num = BigUint::from_bytes_be(&bytes);
        if num.bits() > F::NUM_BITS.into() {
            Err(nom::Err::Error(ParseError::new(
                i,
                ParseErrorKind::NumericLiteralTooBig,
            )))
        } else if num.bits() <= u64::BITS.into() {
            let num: u64 = num.try_into().unwrap();
            Ok((i, Term::Num(Num::U64(num))))
        } else {
            // bad temporary hack, we should really parse as a multibase of the field
            // repr, which is implementation specific and built into the `F` we're
            // carrying around (i.e. to_repr and from_repr)
            let num = F::from_str_vartime(&digits).unwrap();
            Ok((i, Term::Num(Num::Scalar(num))))
        }
    }
}

pub fn parse_dot_pair<F: PrimeField>() -> impl Fn(Span) -> IResult<Span, Term<F>, ParseError<Span>>
{
    move |i: Span| {
        let (i, _) = context("open paren", tag("("))(i)?;
        let (i, car) = preceded(parse_space, parse_term())(i)?;
        let (i, _) = preceded(parse_space, tag("."))(i)?;
        let (i, cdr) = preceded(parse_space, parse_term())(i)?;
        let (i, _) = context("close paren", preceded(parse_space, tag(")")))(i)?;
        Ok((i, Term::Cons(Box::new(car), Box::new(cdr))))
    }
}

pub fn parse_list<F: PrimeField>() -> impl Fn(Span) -> IResult<Span, Term<F>, ParseError<Span>> {
    move |i: Span| {
        let (i, _) = context("open paren", tag("("))(i)?;
        let mut i = i;
        let mut ts = Vec::new();
        fn end(i: Span) -> IResult<Span, (), ParseError<Span>> {
            let (i, _) = tag(")")(i)?;
            Ok((i, ()))
        }
        loop {
            let (i2, _) = parse_space(i)?;
            match end(i2) {
                Ok((i, _)) => {
                    let trm = ts
                        .into_iter()
                        .rev()
                        .fold(Term::Nil, |acc, t| Term::Cons(Box::new(t), Box::new(acc)));
                    return Ok((i, trm));
                }
                _ => {
                    let (i2, t) = parse_term()(i2)?;
                    ts.push(t);
                    i = i2
                }
            }
        }
    }
}

pub fn parse_quote<F: PrimeField>() -> impl Fn(Span) -> IResult<Span, Term<F>, ParseError<Span>> {
    move |i: Span| {
        let (i, _) = context("open quote", tag("'"))(i)?;
        let (i, x) = parse_term()(i)?;
        Ok((
            i,
            Term::Cons(
                Box::new(Term::Sym(String::from("quote"))),
                Box::new(Term::Cons(Box::new(x), Box::new(Term::Nil))),
            ),
        ))
    }
}

pub fn parse_term<F: PrimeField>() -> impl Fn(Span) -> IResult<Span, Term<F>, ParseError<Span>> {
    move |i: Span| {
        context(
            "term",
            alt((
                parse_quote(),
                parse_sym(),
                parse_str(),
                parse_num(),
                parse_dot_pair(),
                parse_list(),
            )),
        )(i)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use blstrs::Scalar as Fr;

    use quickcheck::{Arbitrary, Gen};
    use rand::Rng;

    macro_rules! cons {
        ($i:expr, $j:expr) => {
            Term::<Fr>::Cons(Box::new($i), Box::new($j))
        };
    }
    macro_rules! nil {
        () => {
            Term::<Fr>::Nil
        };
    }
    macro_rules! sym {
        ($i:literal) => {
            Term::<Fr>::Sym(String::from($i))
        };
    }

    macro_rules! num {
        ($i:literal) => {
            Term::<Fr>::Num(Num::U64($i))
        };
    }

    macro_rules! str_ {
        ($i:literal) => {
            Term::<Fr>::Str(String::from($i))
        };
    }

    pub fn frequency<T, F: Fn(&mut Gen) -> T>(g: &mut Gen, gens: Vec<(i64, F)>) -> T {
        if gens.iter().any(|(v, _)| *v < 0) {
            panic!("Negative weight");
        }
        let sum: i64 = gens.iter().map(|x| x.0).sum();
        let mut rng = rand::thread_rng();
        let mut weight: i64 = rng.gen_range(1..=sum);
        // let mut weight: i64 = g.rng.gen_range(1, sum);
        for gen in gens {
            if weight - gen.0 <= 0 {
                return gen.1(g);
            } else {
                weight -= gen.0;
            }
        }
        panic!("Calculation error for weight = {}", weight);
    }

    pub fn arbitrary_sym<F: PrimeField>(g: &mut Gen) -> Term<F> {
        let mut chars = (b'a'..=b'z').map(char::from);
        let idx: usize = Arbitrary::arbitrary(g);
        let sym = chars.nth(idx % 26).unwrap().into();
        Term::Sym(sym)
    }

    impl<F: PrimeField> Arbitrary for Term<F> {
        fn arbitrary(g: &mut Gen) -> Self {
            let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> Term<F>>)> = vec![
                (100, Box::new(|g| arbitrary_sym(g))),
                // doesn't test Scalar
                (
                    100,
                    Box::new(|g| Term::Num(Num::U64(Arbitrary::arbitrary(g)))),
                ),
                (100, Box::new(|g| Term::Str(Arbitrary::arbitrary(g)))),
                (100, Box::new(|_| Term::Nil)),
                (
                    50,
                    Box::new(|g| Term::Cons(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g))),
                ),
            ];
            frequency(g, input)
        }
    }

    #[test]
    fn test_print() {
        assert_eq!("()", nil!().print());
        assert_eq!("a", sym!("a").print());
        assert_eq!("(a)", cons!(sym!("a"), nil!()).print());
        assert_eq!("(a b)", cons!(sym!("a"), cons!(sym!("b"), nil!())).print());
        assert_eq!(
            "(a b c)",
            cons!(sym!("a"), cons!(sym!("b"), cons!(sym!("c"), nil!()))).print()
        );
        assert_eq!(
            "(a b c d)",
            cons!(
                sym!("a"),
                cons!(sym!("b"), cons!(sym!("c"), cons!(sym!("d"), nil!())))
            )
            .print()
        );
        assert_eq!("(a . b)", cons!(sym!("a"), sym!("b")).print());
        assert_eq!(
            "(c (a . b))",
            cons!(sym!("c"), cons!(cons!(sym!("a"), sym!("b")), nil!())).print()
        );
        assert_eq!(
            "((a . b) c)",
            cons!(cons!(sym!("a"), sym!("b")), cons!(sym!("c"), nil!())).print()
        );
        assert_eq!(
            "((a . b) . c)",
            cons!(cons!(sym!("a"), sym!("b")), sym!("c")).print()
        );
        assert_eq!(
            "((a . b) c)",
            cons!(cons!(sym!("a"), sym!("b")), cons!(sym!("c"), nil!())).print()
        );
        assert_eq!(
            "((a . b) (a . b) c)",
            cons!(
                cons!(sym!("a"), sym!("b")),
                cons!(cons!(sym!("a"), sym!("b")), cons!(sym!("c"), nil!()))
            )
            .print()
        );
    }

    fn test<'a, P>(mut p: P, i: &'a str, expected: Option<Term<Fr>>)
    where
        P: Parser<Span<'a>, Term<Fr>, ParseError<Span<'a>>>,
    {
        match (expected, p.parse(Span::new(i))) {
            (Some(expected), Ok((i, x))) if x == expected => (),
            (Some(expected), Ok((i, x))) => {
                println!("input: {:?}", i);
                println!("expected: {:?}", expected);
                println!("detected: {:?}", x);
                assert!(false)
            }
            (Some(..), Err(e)) => {
                println!("{}", e);
                assert!(false)
            }
            (None, Ok((i, x))) => {
                println!("input: {:?}", i);
                println!("expected parse error");
                println!("detected: {:?}", x);
                assert!(false)
            }
            (None, Err(e)) => (),
        }
    }

    #[test]
    fn test_parse_sym() {
        test(parse_sym(), "asdf", Some(Term::Sym(String::from("asdf"))));
        test(parse_sym(), "ASDF", Some(Term::Sym(String::from("ASDF"))));
        test(parse_sym(), "nil", Some(Term::Nil));
        test(parse_sym(), "+", Some(Term::Sym(String::from("+"))));
        test(parse_sym(), ";;", None);
        test(parse_sym(), ")", None);
        test(parse_sym(), "(", None);
        test(parse_sym(), ".", None);
    }

    #[test]
    fn test_parse_str() {
        test(parse_str(), "(", None);
        test(parse_str(), "\"asdf\"", Some(str_!("asdf")));
        test(parse_str(), "\"as\\ndf\"", Some(str_!("as\ndf")));
        test(parse_str(), "\"\\\\\"", Some(str_!("\\")));
        test(parse_str(), "\"'\"", Some(str_!("'")));
        test(parse_str(), "\"\\u{41}\"", Some(str_!("A")));
    }
    #[test]
    fn test_parse_num() {
        test(parse_num(), "0x0", Some(num!(0x0)));
        test(parse_num(), "0xdead_beef", Some(num!(0xdead_beef)));
        test(parse_num(), "0b0", Some(num!(0b0)));
        test(parse_num(), "0b1011_1100", Some(num!(0b1011_1100)));
        test(parse_num(), "42", Some(num!(42)));
    }

    #[test]
    fn test_parse_dot_pair() {
        test(parse_dot_pair(), "(", None);
        test(
            parse_dot_pair(),
            "(a . b)",
            Some(cons!(sym!("a"), sym!("b"))),
        );
        test(parse_dot_pair(), "(a .)", None);
        test(parse_dot_pair(), "(. b)", None);
        test(parse_dot_pair(), "(.)", None);
        test(parse_dot_pair(), "()", None);
    }

    #[test]
    fn test_parse_list() {
        test(parse_list(), "(", None);
        test(parse_list(), "()", Some(nil!()));
        test(parse_list(), "(a)", Some(cons!(sym!("a"), nil!())));
        test(
            parse_list(),
            "(a b)",
            Some(cons!(sym!("a"), cons!(sym!("b"), nil!()))),
        );
        test(
            parse_list(),
            "(() b)",
            Some(cons!(nil!(), cons!(sym!("b"), nil!()))),
        );
    }

    #[test]
    fn test_parse_term() {
        fn parse_print(i: &str, t: Term<Fr>) {
            test(parse_term(), i, Some(t.clone()));
            assert_eq!(i, format!("{}", t));
        }
        parse_print("()", nil!());
        parse_print("(())", cons!(nil!(), nil!()));
        parse_print("(() t)", cons!(nil!(), cons!(sym!("t"), nil!())));
        parse_print(
            "(f (u . p))",
            cons!(sym!("f"), cons!(cons!(sym!("u"), sym!("p")), nil!())),
        );
        parse_print("(() . t)", cons!(nil!(), sym!("t")));
    }

    #[quickcheck]
    fn term_parse_print(x: Term<Fr>) -> bool {
        let i = format!("{}", x);
        match parse_term()(Span::new(&i)) {
            Ok((_, y)) if x == y => true,
            Ok((_, y)) => {
                println!("x: {}", x);
                println!("x: {:?}", x);
                println!("y: {}", y);
                println!("y: {:?}", y);
                false
            }
            Err(e) => {
                println!("{}", x);
                println!("{}", e);
                false
            }
        }
    }
}
