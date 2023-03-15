use bellperson::SynthesisError;
use lurk::store;
use std::io;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("Verification error: {0}")]
    VerificationError(String),
    #[error("Unsupported reduction count: {0}")]
    UnsupportedReductionCount(usize),
    #[error("IO error: {0}")]
    IOError(io::Error),
    #[error("JSON error: {0}")]
    JsonError(serde_json::Error),
    #[error("Synthesis error: {0}")]
    SynthesisError(SynthesisError),
    #[error("Commitment parser error: {0}")]
    CommitmentParseError(hex::FromHexError),
    #[error("Unknown commitment")]
    UnknownCommitment,
    #[error("Opening Failure: {0}")]
    OpeningFailure(String),
    #[error("Evaluation Failure")]
    EvaluationFailure,
    #[error("Store error: {0}")]
    StoreError(String),
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::IOError(err)
    }
}

impl From<serde_json::Error> for Error {
    fn from(err: serde_json::Error) -> Error {
        Error::JsonError(err)
    }
}

impl From<SynthesisError> for Error {
    fn from(err: SynthesisError) -> Error {
        Error::SynthesisError(err)
    }
}

impl From<store::Error> for Error {
    fn from(err: store::Error) -> Error {
        Error::StoreError(err.0)
    }
}
