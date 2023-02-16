use std::io;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum VerifyError {
    #[error("Verification error: {0}")]
    Verification(String),
    #[error("IO error: {0}")]
    IO(#[from] io::Error),
    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),
    #[error("Commitment error: {0}")]
    Commitment(#[from] CommitmentError),
    #[error("Store error: {0}")]
    Store(#[from] lurk::parser::Error),
}

#[derive(Error, Debug)]
pub enum CommitmentError {
    #[error("Parser error: {0}")]
    Parser(#[from] hex::FromHexError),
    #[error("Unknown commitment error")]
    UnknownCommitment,
    #[error("Opening failure")]
    OpeningFailure,
}
