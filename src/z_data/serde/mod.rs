use thiserror::Error;

mod de;
mod ser;

pub use ser::to_z_data;

#[derive(Error, Debug)]
pub enum SerdeError {
    #[error("Function error")]
    Function(String),
    #[error("Type error")]
    Type(String),
}

impl serde::ser::Error for SerdeError {
    fn custom<T: core::fmt::Display>(msg: T) -> Self {
        Self::Function(msg.to_string())
    }
}

impl serde::de::Error for SerdeError {
    fn custom<T: core::fmt::Display>(msg: T) -> Self {
        Self::Function(msg.to_string())
    }
}
