#![allow(clippy::single_match)]

// #[macro_use]
// mod gadgets;

pub mod parser;
pub mod pool;
pub mod writer;
// pub mod circuit;
pub mod eval;
// pub mod proof;

pub const TEST_SEED: [u8; 16] = [
    0x62, 0x59, 0x5d, 0xbe, 0x3d, 0x76, 0x3d, 0x8d, 0xdb, 0x17, 0x32, 0x37, 0x06, 0x54, 0xe5, 0xbc,
];
