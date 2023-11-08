#![doc = include_str!("../README.md")]
#![deny(unreachable_pub)]

#[macro_use]
pub mod circuit;
pub mod cli;
pub mod config;
pub mod cont;
pub mod coprocessor;
pub mod error;
pub mod eval;
pub mod expr;
pub mod field;
pub mod hash;
pub mod hash_witness;
pub mod lem;
mod num;
pub mod package;
pub mod parser;
pub mod proof;
pub mod ptr;
pub mod public_parameters;
pub mod state;
pub mod store;
pub mod symbol;
pub mod syntax;
mod syntax_macros;
pub mod tag;
pub mod uint;
pub mod writer;
pub mod z_data;
pub use num::Num;
pub use symbol::Symbol;
pub use uint::UInt;

pub use z_data::{z_cont, z_expr, z_ptr, z_store};
