use crate::parser;
use crate::store;
use bellperson::SynthesisError;
use nova::errors::NovaError;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ProofError {
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
    #[error("Lookup error: {0}")]
    Store(#[from] store::Error),
    #[error("Parser error: {0}")]
    Parser(#[from] parser::Error),
    #[error("Parser error: {0}")]
    Provable(String),
}