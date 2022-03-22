#![allow(clippy::single_match, clippy::type_complexity)]

pub mod circuit;
pub mod eval;
pub mod parser;
pub mod proof;
pub mod repl;
pub mod scalar_store;
pub mod store;
pub mod writer;

mod num;
pub use num::Num;

pub const TEST_SEED: [u8; 16] = [
    0x62, 0x59, 0x5d, 0xbe, 0x3d, 0x76, 0x3d, 0x8d, 0xdb, 0x17, 0x32, 0x37, 0x06, 0x54, 0xe5, 0xbc,
];
