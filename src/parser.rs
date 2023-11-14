use std::cell::RefCell;
use std::rc::Rc;

use crate::field::LurkField;
use crate::ptr::Ptr;
use crate::state::State;
use crate::store::Store;
use nom::sequence::preceded;
use nom::Parser;
use thiserror;

pub mod base;
pub mod error;
pub mod position;
pub mod string;
pub mod syntax;

pub type Span<'a> = nom_locate::LocatedSpan<&'a str>;
pub type ParseResult<'a, F, T> = nom::IResult<Span<'a>, T, error::ParseError<Span<'a>, F>>;

// see https://github.com/sg16-unicode/sg16/issues/69
pub static LURK_WHITESPACE: [char; 27] = [
    '\u{0009}', '\u{000A}', '\u{000B}', '\u{000C}', '\u{000D}', '\u{0020}', '\u{0085}', '\u{200E}',
    '\u{200F}', '\u{2028}', '\u{2029}', '\u{20A0}', '\u{1680}', '\u{2000}', '\u{2001}', '\u{2002}',
    '\u{2003}', '\u{2004}', '\u{2005}', '\u{2006}', '\u{2007}', '\u{2008}', '\u{2009}', '\u{200A}',
    '\u{202F}', '\u{205F}', '\u{3000}',
];

#[derive(thiserror::Error, Debug, Clone)]
pub enum Error {
    #[error("Empty input error")]
    NoInput,
    #[error("Syntax error: {0}")]
    Syntax(String),
}

impl<F: LurkField> Store<F> {
    pub fn read(&self, input: &str) -> Result<Ptr<F>, Error> {
        let state = State::init_lurk_state().rccell();
        match preceded(
            syntax::parse_space,
            syntax::parse_syntax(state, false, false),
        )
        .parse(Span::new(input))
        {
            Ok((_i, x)) => Ok(self.intern_syntax(x)),
            Err(e) => Err(Error::Syntax(format!("{e}"))),
        }
    }

    pub fn read_with_state(&self, state: Rc<RefCell<State>>, input: &str) -> Result<Ptr<F>, Error> {
        match preceded(
            syntax::parse_space,
            syntax::parse_syntax(state, false, false),
        )
        .parse(Span::new(input))
        {
            Ok((_i, x)) => Ok(self.intern_syntax(x)),
            Err(e) => Err(Error::Syntax(format!("{e}"))),
        }
    }

    pub fn read_maybe_meta_with_state<'a>(
        &self,
        state: Rc<RefCell<State>>,
        input: Span<'a>,
    ) -> Result<(Span<'a>, Ptr<F>, bool), Error> {
        use syntax::*;
        match preceded(parse_space, parse_maybe_meta(state, false)).parse(input) {
            Ok((i, Some((is_meta, x)))) => Ok((i, self.intern_syntax(x), is_meta)),
            Ok((_, None)) => Err(Error::NoInput),
            Err(e) => Err(Error::Syntax(format!("{e}"))),
        }
    }
}
