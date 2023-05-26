use std::{cmp::Ordering, fmt, fmt::Write, num::ParseIntError, string::String};

use crate::field::LurkField;
use nom::{error::ErrorKind, AsBytes, Err, IResult, InputLength};

use crate::parser::{base, Span};

#[derive(PartialEq, Debug, Clone)]
pub enum ParseErrorKind<F: LurkField> {
    InvalidBase16EscapeSequence(String, Option<ParseIntError>),
    InvalidBaseEncoding(base::LitBase),
    //    NumericSyntax(String),
    // U64Error(F),
    NumError(String),
    NumLiteralTooBig(F, num_bigint::BigUint),
    UnknownBaseCode,
    ParseIntErr(ParseIntError),
    InvalidChar(String),
    //    InvalidSymbol(String),
    Nom(ErrorKind),
}

impl<F: LurkField> fmt::Display for ParseErrorKind<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidBase16EscapeSequence(seq, _) => {
                write!(f, "Unknown base 16 string escape sequence {}.", seq)
            }
            Self::ParseIntErr(e) => {
                write!(f, "Error parsing number: {}", e)
            }
            e => write!(f, "internal parser error {:?}", e),
        }
    }
}

impl<F: LurkField> ParseErrorKind<F> {
    pub fn is_nom_err(&self) -> bool {
        matches!(self, Self::Nom(_))
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct ParseError<I: AsBytes, F: LurkField> {
    pub input: I,
    pub expected: Option<&'static str>,
    pub errors: Vec<ParseErrorKind<F>>,
}

impl<I: AsBytes, F: LurkField> ParseError<I, F> {
    pub fn new(input: I, error: ParseErrorKind<F>) -> Self {
        ParseError {
            input,
            expected: None,
            errors: vec![error],
        }
    }

    pub fn throw<A>(input: I, e: ParseErrorKind<F>) -> IResult<I, A, Self> {
        Err(Err::Error(ParseError::new(input, e)))
    }

    pub fn opt<A>(opt: Option<A>, input: I, error: ParseErrorKind<F>) -> IResult<I, A, Self> {
        match opt {
            Some(a) => Ok((input, a)),
            None => Err(Err::Error(ParseError::new(input, error))),
        }
    }

    pub fn res<A, E, Fun: Fn(E) -> ParseErrorKind<F>>(
        res: Result<A, E>,
        input: I,
        f: Fun,
    ) -> IResult<I, A, Self> {
        match res {
            Ok(a) => Ok((input, a)),
            Err(e) => Err(Err::Error(ParseError::new(input, f(e)))),
        }
    }
}

impl<'a, F: LurkField> fmt::Display for ParseError<Span<'a>, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut res = String::new();

        writeln!(
            &mut res,
            "at line {}:{}",
            self.input.location_line(),
            self.input.get_column()
        )?;
        let line = String::from_utf8_lossy(self.input.get_line_beginning());

        writeln!(&mut res, "{} | {}", self.input.location_line(), line)?;

        let cols = format!("{} | ", self.input.location_line()).len() + self.input.get_column();
        for _ in 0..(cols - 1) {
            write!(&mut res, " ")?;
        }
        writeln!(&mut res, "^")?;

        if let Some(exp) = self.expected {
            writeln!(&mut res, "Expected {}", exp)?;
        }

        let mut errs = self.errors.iter().filter(|x| !x.is_nom_err()).peekable();
        match errs.peek() {
            // TODO: Nom verbose mode
            None => writeln!(&mut res, "Internal parser error")?,
            Some(_) => {
                writeln!(&mut res, "Reported errors:")?;
                for kind in errs {
                    writeln!(&mut res, "- {}", kind)?;
                }
            }
        }

        write!(f, "{}", res)
    }
}

impl<I: AsBytes, F: LurkField> nom::error::ParseError<I> for ParseError<I, F>
where
    I: InputLength,
    I: Clone,
{
    fn from_error_kind(input: I, kind: ErrorKind) -> Self {
        ParseError::new(input, ParseErrorKind::Nom(kind))
    }

    fn append(input: I, kind: ErrorKind, mut other: Self) -> Self {
        match input.input_len().cmp(&other.input.input_len()) {
            Ordering::Less => ParseError::new(input, ParseErrorKind::Nom(kind)),
            Ordering::Equal => {
                other.errors.push(ParseErrorKind::Nom(kind));
                other
            }
            Ordering::Greater => other,
        }
    }

    fn or(self, mut other: Self) -> Self {
        match self.input.input_len().cmp(&other.input.input_len()) {
            Ordering::Less => self,
            Ordering::Equal => {
                for x in self.errors {
                    other.errors.push(x);
                }
                other
            }
            Ordering::Greater => other,
        }
    }
}

impl<I: AsBytes, F: LurkField> nom::error::ContextError<I> for ParseError<I, F>
where
    I: InputLength,
    I: Clone,
{
    fn add_context(input: I, ctx: &'static str, other: Self) -> Self {
        match input.input_len().cmp(&other.input.input_len()) {
            Ordering::Less => ParseError {
                input,
                expected: Some(ctx),
                errors: vec![],
            },
            Ordering::Equal => match other.expected {
                None => ParseError {
                    input,
                    expected: Some(ctx),
                    errors: other.errors,
                },
                _ => other,
            },
            Ordering::Greater => other,
        }
    }
}

pub fn map_parse_err<I: AsBytes, F: LurkField, A, Fun: Fn(ParseError<I, F>) -> ParseError<I, F>>(
    x: IResult<I, A, ParseError<I, F>>,
    f: Fun,
) -> IResult<I, A, ParseError<I, F>> {
    x.map_err(|e| match e {
        Err::Incomplete(n) => Err::Incomplete(n),
        Err::Error(e) => Err::Error(f(e)),
        Err::Failure(e) => Err::Failure(f(e)),
    })
}
