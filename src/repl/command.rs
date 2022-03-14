use crate::parser::error::ParseError;
use crate::parser::error::ParseErrorKind;
use crate::parser::syntax::parse_space1;
use crate::parser::syntax::parse_term;
use crate::parser::syntax::Term;
use crate::parser::Span;

use blstrs::Scalar as Fr;
use nom::{self, branch::alt, bytes::complete::tag, bytes::complete::take_till1, Err, IResult};
use std::path::PathBuf;

pub enum Command {
    Eval(Box<Term<Fr>>),
    Load(PathBuf),
    // TODO: port/decipher handle_run function
    // Run
    Clear,
    Quit,
}

pub fn parse_eval() -> impl Fn(Span) -> IResult<Span, Command, ParseError<Span>> {
    move |i: Span| {
        let (i, trm) = parse_term()(i)?;
        Ok((i, Command::Eval(Box::new(trm))))
    }
}

pub fn parse_pathbuf() -> impl Fn(Span) -> IResult<Span, PathBuf, ParseError<Span>> {
    move |from: Span| {
        let (i, s) = take_till1(|x| char::is_whitespace(x))(from)?;
        let path = PathBuf::from(s.fragment());
        if path.exists() {
            Ok((i, path))
        } else {
            Err(Err::Error(ParseError::new(
                from,
                ParseErrorKind::ReplErrUnknownPath(path),
            )))
        }
    }
}

pub fn parse_load() -> impl Fn(Span) -> IResult<Span, Command, ParseError<Span>> {
    move |i: Span| {
        let (i, _) = alt((tag(":load"), tag(":l")))(i)?;
        let (i, _) = parse_space1(i)?;
        let (i, path) = parse_pathbuf()(i)?;
        Ok((i, Command::Load(path)))
    }
}
// TODO: Need clarity on :run arguments
pub fn parse_run() -> impl Fn(Span) -> IResult<Span, Command, ParseError<Span>> {
    move |i: Span| {
        let (i, _) = alt((tag(":run"), tag(":r")))(i)?;
        let (i, _) = parse_space1(i)?;
        todo!();
        // Ok((i, Command::Run))
    }
}

pub fn parse_clear() -> impl Fn(Span) -> IResult<Span, Command, ParseError<Span>> {
    move |i: Span| {
        let (i, _) = alt((tag(":c"), tag(":clear")))(i)?;
        Ok((i, Command::Clear))
    }
}

pub fn parse_quit() -> impl Fn(Span) -> IResult<Span, Command, ParseError<Span>> {
    move |i: Span| {
        let (i, _) = alt((tag(":q"), tag(":quit")))(i)?;
        Ok((i, Command::Quit))
    }
}

pub fn parse_command() -> impl Fn(Span) -> IResult<Span, Command, ParseError<Span>> {
    move |i: Span| {
        alt((
            parse_quit(),
            parse_load(),
            parse_clear(),
            // parse_run(),
            parse_eval(),
        ))(i)
    }
}
