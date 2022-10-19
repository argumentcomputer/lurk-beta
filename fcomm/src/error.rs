use bellperson::SynthesisError;
use std::io;

#[derive(Debug)]
pub enum Error {
    VerificationError(String),
    UnsupportedReductionCount(usize),
    IOError(io::Error),
    JsonError(serde_json::Error),
    SynthesisError(SynthesisError),
    CommitmentParseError(hex::FromHexError),
    UnknownCommitment,
    OpeningFailure,
    EvaluationFailure,
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
