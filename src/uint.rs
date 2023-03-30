#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
use serde::{Deserialize, Serialize};
use std::{
    fmt::Display,
    ops::{Add, Div, Mul, Rem, Sub},
};

/// Unsigned fixed-width integer type for Lurk.
#[derive(Debug, Copy, Clone, PartialEq, PartialOrd, Eq, Serialize, Deserialize)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
pub enum UInt {
    U64(u64),
}

impl UInt {
    pub fn is_zero(&self) -> bool {
        match self {
            UInt::U64(n) => *n == 0,
        }
    }
}

impl From<u64> for UInt {
    fn from(n: u64) -> Self {
        Self::U64(n)
    }
}

impl From<UInt> for u64 {
    fn from(u: UInt) -> u64 {
        match u {
            UInt::U64(n) => n,
        }
    }
}

impl Display for UInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UInt::U64(n) => write!(f, "{n}"),
        }
    }
}

impl Add for UInt {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        match (self, other) {
            (UInt::U64(a), UInt::U64(b)) => UInt::U64(a.wrapping_add(b)),
        }
    }
}

impl Sub for UInt {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        match (self, other) {
            (UInt::U64(a), UInt::U64(b)) => UInt::U64(a.wrapping_sub(b)),
        }
    }
}
impl Div for UInt {
    type Output = Self;
    fn div(self, other: Self) -> Self {
        match (self, other) {
            (UInt::U64(a), UInt::U64(b)) => UInt::U64(a / b),
        }
    }
}
impl Mul for UInt {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        match (self, other) {
            (UInt::U64(a), UInt::U64(b)) => UInt::U64(a.wrapping_mul(b)),
        }
    }
}
impl Rem for UInt {
    type Output = Self;
    fn rem(self, other: Self) -> Self {
        match (self, other) {
            (UInt::U64(a), UInt::U64(b)) => UInt::U64(a % b),
        }
    }
}
