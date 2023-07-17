use lurk::field::LurkField;
use lurk::parser::error;
use lurk::parser::syntax::{parse_space, parse_space1};
use lurk::parser::ParseResult;
use lurk::parser::Span;

use im::Vector;

use nom::branch::alt;
use nom::bytes::complete::is_not;
use nom::bytes::complete::tag;
use nom::combinator::verify;
use nom::multi::{many0, many1};
use nom::sequence::preceded;

use crate::syntax::Syntax;

pub fn parse_name<'a, F: LurkField>() -> impl Fn(Span<'a>) -> ParseResult<'a, F, String> {
    move |from: Span<'a>| {
        let mut s = String::from("λ()\\.");
        for c in lurk::parser::LURK_WHITESPACE {
            s.push(c);
        }
        let (i, s) = verify(is_not(&*s), |s: &Span<'a>| !s.fragment().is_empty())(from)?;
        Ok((i, s.to_string()))
    }
}

pub fn parse_var<F: LurkField>(
    ctx: Vector<String>,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax> {
    move |from: Span<'_>| {
        let (i, name) = parse_name()(from)?;
        if let Some(idx) = ctx.iter().position(|x| x == &name) {
            Ok((i, Syntax::Var(name, idx)))
        } else {
            // TODO: This is the wrong error message
            error::ParseError::throw(i, error::ParseErrorKind::UnknownBaseCode)
        }
    }
}

// λx y z. B ~> λx.λy.λz B
pub fn parse_lam<F: LurkField>(
    ctx: Vector<String>,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax> {
    move |from: Span<'_>| {
        let (i, _) = tag("λ")(from)?;
        let (i, name) = preceded(parse_space, parse_name())(i)?;
        let (i, names) = many0(preceded(parse_space1, parse_name()))(i)?;
        let (i, _) = parse_space(i)?;
        let (i, _) = tag(".")(i)?;
        let mut ctx = ctx.clone();
        ctx.push_front(name.clone());
        for name in names.iter() {
            ctx.push_front(name.clone());
        }
        let (i, bod) = parse_syntax(ctx)(i)?;
        let term = names
            .iter()
            .rev()
            .fold(bod, |acc, name| Syntax::Lam(name.clone(), Box::new(acc)));
        let term = Syntax::Lam(name, Box::new(term));
        Ok((i, term))
    }
}

// (M N), (a b c d) ~> (((a b) c) d)
pub fn parse_app<F: LurkField>(
    ctx: Vector<String>,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax> {
    move |from: Span<'_>| {
        let (i, _) = tag("(")(from)?;
        let (i, _) = parse_space(i)?;
        let (i, fun) = parse_syntax(ctx.clone())(i)?;
        let (i, args) = many0(preceded(parse_space, parse_syntax(ctx.clone())))(i)?;
        let (i, _) = parse_space(i)?;
        let (i, _) = tag(")")(i)?;
        let term = args
            .into_iter()
            .fold(fun, |acc, arg| Syntax::App(Box::new(acc), Box::new(arg)));
        Ok((i, term))
    }
}

pub fn parse_syntax<F: LurkField>(
    ctx: Vector<String>,
) -> impl Fn(Span<'_>) -> ParseResult<'_, F, Syntax> {
    move |from: Span<'_>| {
        alt((
            parse_lam(ctx.clone()),
            parse_app(ctx.clone()),
            parse_var(ctx.clone()),
        ))(from)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use blstrs::Scalar;
    use lurk::parser::error::ParseError;
    use nom::Parser;

    fn test<'a, P, R>(mut p: P, i: &'a str, expected: Option<R>) -> bool
    where
        P: Parser<Span<'a>, R, ParseError<Span<'a>, Scalar>>,
        R: std::fmt::Display + std::fmt::Debug + Clone + Eq,
    {
        match (expected, p.parse(Span::<'a>::new(i))) {
            (Some(expected), Ok((_, x))) if x == expected => true,
            (Some(_), Ok((_, x))) => {
                println!("input: {:?}", i);
                //println!("expected: {} {:?}", expected.clone(), expected);
                println!("detected: {} {:?}", x.clone(), x);
                false
            }
            (Some(..), Err(e)) => {
                println!("{}", e);
                false
            }
            (None, Ok((_, x))) => {
                println!("input: {:?}", i);
                println!("expected parse error");
                println!("detected: {:?}", x);
                false
            }
            (None, Err(_e)) => true,
        }
    }

    #[test]
    fn unit_parse_lambda() {
        assert!(test(
            parse_lam(Vector::new()),
            "λx.x",
            Some(Syntax::Lam(
                String::from("x"),
                Box::new(Syntax::Var(String::from("x"), 0))
            ))
        ));
        assert!(test(
            parse_lam(Vector::new()),
            "λy.y",
            Some(Syntax::Lam(
                String::from("y"),
                Box::new(Syntax::Var(String::from("y"), 0))
            ))
        ));
        assert!(test(
            parse_lam(Vector::new()),
            "λx y z.x",
            Some(Syntax::Lam(
                String::from("x"),
                Box::new(Syntax::Lam(
                    String::from("y"),
                    Box::new(Syntax::Lam(
                        String::from("z"),
                        Box::new(Syntax::Var(String::from("x"), 2))
                    ))
                ))
            ))
        ));
        assert!(test(
            parse_lam(Vector::new()),
            "λx y z.y",
            Some(Syntax::Lam(
                String::from("x"),
                Box::new(Syntax::Lam(
                    String::from("y"),
                    Box::new(Syntax::Lam(
                        String::from("z"),
                        Box::new(Syntax::Var(String::from("y"), 1))
                    ))
                ))
            ))
        ));
        assert!(test(
            parse_lam(Vector::new()),
            "λx y z.z",
            Some(Syntax::Lam(
                String::from("x"),
                Box::new(Syntax::Lam(
                    String::from("y"),
                    Box::new(Syntax::Lam(
                        String::from("z"),
                        Box::new(Syntax::Var(String::from("z"), 0))
                    ))
                ))
            ))
        ));
    }

    #[test]
    fn unit_parse_app() {
        assert!(test(
            parse_app(Vector::new()),
            "(λx.x λy.y)",
            Some(Syntax::App(
                Box::new(Syntax::Lam(
                    String::from("x"),
                    Box::new(Syntax::Var(String::from("x"), 0))
                )),
                Box::new(Syntax::Lam(
                    String::from("y"),
                    Box::new(Syntax::Var(String::from("y"), 0))
                ))
            ))
        ));
        assert!(test(
            parse_app(Vector::new()),
            "(λx.x λy.y λz.z)",
            Some(Syntax::App(
                Box::new(Syntax::App(
                    Box::new(Syntax::Lam(
                        String::from("x"),
                        Box::new(Syntax::Var(String::from("x"), 0))
                    )),
                    Box::new(Syntax::Lam(
                        String::from("y"),
                        Box::new(Syntax::Var(String::from("y"), 0))
                    ))
                )),
                Box::new(Syntax::Lam(
                    String::from("z"),
                    Box::new(Syntax::Var(String::from("z"), 0))
                ))
            ))
        ));
    }
    #[quickcheck]
    fn parse_print_syntax(x: Syntax) -> bool {
        match parse_syntax::<Scalar>(Vector::new()).parse(Span::new(&format!("{}", x))) {
            Ok((i, y)) => {
                println!("input: {:?}", i);
                println!("expected: {} {:?}", x.clone(), x);
                println!("detected: {} {:?}", y.clone(), y);
                x == y
            }
            Err(e) => {
                println!("{}", e);
                false
            }
        }
    }
}
