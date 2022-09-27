use thiserror::Error;

#[derive(Error, Debug)]
pub enum LurkError {
    #[error("Evaluation error: {0}")]
    Eval(String),
    #[error("Reduction error: {0}")]
    Reduce(String),
    #[error("Lookup error: {0}")]
    Store(String),
}
