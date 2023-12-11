#![doc = include_str!("../README.md")]
#![deny(unreachable_pub)]

#[macro_use]
pub mod circuit;
pub mod cli;
pub mod config;
pub mod coprocessor;
pub mod error;
pub mod eval;
pub mod field;
mod hash;
pub mod lem;
mod num;
mod package;
pub mod parser;
pub mod proof;
pub mod public_parameters;
pub mod state;
mod symbol;
mod syntax;
mod syntax_macros;
mod tag;
mod uint;
pub mod z_data;
pub use num::Num;
pub use symbol::Symbol;
pub use uint::UInt;

pub use z_data::{z_cont, z_expr, z_ptr, z_store};

mod store {
    #[derive(thiserror::Error, Debug, Clone)]
    pub struct Error(pub String);

    impl std::fmt::Display for Error {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "StoreError: {}", self.0)
        }
    }
}
