use bellperson::SynthesisError;
use nova::errors::NovaError;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("Nova error")]
    Nova(NovaError),
    #[error("Synthesis error: {0}")]
    Synthesis(#[from] SynthesisError),
    #[error("Lurk error: {0}")]
    Lurk(#[from] LurkError),
}

#[derive(Error, Debug, Clone)]
pub enum LurkError {
    #[error("Evaluation error: {0}")]
    Eval(String),
    #[error("Reduction error: {0}")]
    Reduce(String),
    #[error("Lookup error: {0}")]
    Store(String),
    #[error("Parser error: {0}")]
    Parser(#[from] ParserError),
}

#[derive(Error, Debug, Clone)]
pub enum ParserError {
    #[error("Empty input error")]
    NoInput,
    #[error("Syntax error: {0}")]
    Syntax(String),
}
