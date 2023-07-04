#![allow(clippy::single_match, clippy::type_complexity)]
#![allow(clippy::uninlined_format_args)]
#![warn(rust_2018_idioms, unreachable_pub)]

#[macro_use]
extern crate alloc;

pub mod cache_map;
pub mod circuit;
pub mod cont;
pub mod coprocessor;
pub mod eval;
pub mod expr;
pub mod field;
pub mod hash;
pub mod hash_witness;
//pub mod package;
pub mod error;
pub mod lem;
mod num;
pub mod parser;
pub mod proof;
pub mod ptr;
pub mod public_parameters;
pub mod repl;
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

pub const TEST_SEED: [u8; 16] = [
    0x62, 0x59, 0x5d, 0xbe, 0x3d, 0x76, 0x3d, 0x8d, 0xdb, 0x17, 0x32, 0x37, 0x06, 0x54, 0xe5, 0xbc,
];
