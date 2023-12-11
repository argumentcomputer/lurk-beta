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
