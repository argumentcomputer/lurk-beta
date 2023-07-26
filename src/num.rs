#![deny(missing_docs)]
//! This module defines the `Num` type, which is used to represent field elements in Lurk.
//! The `Num` type is an enum that can represent a field element in either full field representation
//! or in U64 representation. The U64 representation is used for convenience, and is converted to full
//! field representation when necessary (e.g. overflow).
use crate::field::FWrap;
use serde::{Deserialize, Serialize};
use std::{
    cmp::Ordering,
    fmt::Display,
    hash::Hash,
    ops::{AddAssign, DivAssign, MulAssign, SubAssign},
};

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;

use crate::field::LurkField;
use crate::uint::UInt;

/// Finite field element type for Lurk. Has different internal representations to optimize evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Num<F: LurkField> {
    /// a scalar field element in full field representation
    Scalar(F),
    /// a small scalar field element in U64 representation for convenience
    U64(u64),
}

#[cfg(not(target_arch = "wasm32"))]
impl<Fr: LurkField> Arbitrary for Num<Fr> {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        any::<FWrap<Fr>>()
            .prop_map(|f| match f.0.to_u64() {
                Some(x) => Self::U64(x),
                None => Self::Scalar(f.0),
            })
            .boxed()
    }
}

impl<F: LurkField> Copy for Num<F> {}

impl<F: LurkField> Display for Num<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Num::Scalar(s) => {
                let le_bytes = s.to_repr();
                write!(f, "0x")?;
                for &b in le_bytes.as_ref().iter().rev() {
                    write!(f, "{b:02x}")?;
                }
                Ok(())
            }
            Num::U64(n) => write!(f, "{n}"),
        }
    }
}

#[allow(clippy::derived_hash_with_manual_eq)]
impl<F: LurkField> Hash for Num<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Num::Scalar(s) => s.to_repr().as_ref().hash(state),

            Num::U64(n) => {
                let mut bytes = F::Repr::default();

                bytes.as_mut()[..8].copy_from_slice(&n.to_le_bytes());
                bytes.as_ref().hash(state);
            }
        }
    }
}

impl<F: LurkField> PartialOrd for Num<F> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self == other {
            return Some(Ordering::Equal);
        };

        if self.is_less_than(other) {
            Some(Ordering::Less)
        } else {
            Some(Ordering::Greater)
        }
    }
}

impl<F: LurkField> AddAssign for Num<F> {
    fn add_assign(&mut self, rhs: Self) {
        match (*self, rhs) {
            (Num::U64(ref mut a), Num::U64(b)) => {
                *self = if let Some(res) = a.checked_add(b) {
                    Num::U64(res)
                } else {
                    Num::Scalar(F::from(*a) + F::from(b))
                };
            }
            (Num::Scalar(ref mut a), Num::Scalar(b)) => {
                *a += b;
                *self = Num::Scalar(*a);
            }
            (Num::Scalar(ref mut a), Num::U64(b)) => {
                *a += F::from(b);
                *self = Num::Scalar(*a);
            }
            (Num::U64(a), Num::Scalar(b)) => {
                *self = Num::Scalar(F::from(a) + b);
            }
        }
    }
}

impl<F: LurkField> SubAssign for Num<F> {
    fn sub_assign(&mut self, rhs: Self) {
        match (*self, rhs) {
            (Num::U64(ref mut a), Num::U64(b)) => {
                *self = if let Some(res) = a.checked_sub(b) {
                    Num::U64(res)
                } else {
                    Num::Scalar(F::from(*a) - F::from(b))
                };
            }
            (Num::Scalar(ref mut a), Num::Scalar(b)) => {
                *a -= b;
                *self = Num::Scalar(*a);
            }
            (Num::Scalar(ref mut a), Num::U64(b)) => {
                *a -= F::from(b);
                *self = Num::Scalar(*a);
            }
            (Num::U64(a), Num::Scalar(b)) => {
                *self = Num::Scalar(F::from(a) - b);
            }
        }
    }
}

impl<F: LurkField> MulAssign for Num<F> {
    fn mul_assign(&mut self, rhs: Self) {
        match (*self, rhs) {
            (Num::U64(ref mut a), Num::U64(b)) => {
                *self = if let Some(res) = a.checked_mul(b) {
                    Num::U64(res)
                } else {
                    Num::Scalar(F::from(*a) * F::from(b))
                };
            }
            (Num::Scalar(ref mut a), Num::Scalar(b)) => {
                *a *= b;
                *self = Num::Scalar(*a);
            }
            (Num::Scalar(ref mut a), Num::U64(b)) => {
                *a *= F::from(b);
                *self = Num::Scalar(*a);
            }
            (Num::U64(a), Num::Scalar(b)) => {
                *self = Num::Scalar(F::from(a) * b);
            }
        }
    }
}

impl<F: LurkField> DivAssign for Num<F> {
    fn div_assign(&mut self, rhs: Self) {
        assert!(!rhs.is_zero(), "can not divide by 0");
        match (*self, rhs) {
            (Num::U64(ref mut a), Num::U64(b)) => {
                // The result will only be Num::U64 if b divides a.
                *self = if *a % b == 0 {
                    Num::U64(*a / b)
                } else {
                    Num::Scalar(F::from(*a) * F::from(b).invert().unwrap())
                };
            }
            (Num::Scalar(ref mut a), Num::Scalar(b)) => {
                *a *= b.invert().unwrap();
                *self = Num::Scalar(*a);
            }
            (Num::Scalar(ref mut a), Num::U64(b)) => {
                *a *= F::from(b).invert().unwrap();
                *self = Num::Scalar(*a);
            }
            (Num::U64(a), Num::Scalar(b)) => {
                *self = Num::Scalar(F::from(a) * b.invert().unwrap());
            }
        }
    }
}

impl<F: LurkField> Num<F> {
    /// Determines if `self` is zero.
    pub fn is_zero(&self) -> bool {
        match self {
            Num::Scalar(s) => s.is_zero().into(),
            Num::U64(n) => n == &0,
        }
    }

    fn is_less_than(&self, other: &Num<F>) -> bool {
        assert!(self != other);
        match (self.is_negative(), other.is_negative()) {
            // Both negative or neither negative
            (true, true) | (false, false) => self.is_less_than_aux(*other),
            (true, false) => true,
            (false, true) => false,
        }
    }

    fn is_less_than_aux(&self, other: Num<F>) -> bool {
        match (self, other) {
            (Num::U64(s), Num::U64(other)) => s < &other,
            (Num::Scalar(s), Num::Scalar(other)) => Num::Scalar(*s - other).is_negative(),
            (a, b) => Num::Scalar(a.into_scalar()) < Num::Scalar(b.into_scalar()),
        }
    }

    /// Returns the most negative value representable by `Num<F>`.
    pub fn most_negative() -> Self {
        Num::Scalar(F::most_negative())
    }

    /// Returns the most positive value representable by `Num<F>`.
    pub fn most_positive() -> Self {
        Num::Scalar(F::most_positive())
    }

    /// Returns true if `self` is negative.
    pub fn is_negative(&self) -> bool {
        match self {
            // This assumes field modulus is >= 65 bits.
            Num::U64(_) => false,
            Num::Scalar(s) => s.is_negative(),
        }
    }

    /// Converts `self` into a scalar value of type `F`.
    pub fn into_scalar(self) -> F {
        match self {
            Num::U64(n) => F::from(n),
            Num::Scalar(s) => s,
        }
    }

    /// Creates a new `Num<F>` from the given scalar `s`.
    pub fn from_scalar(s: F) -> Self {
        Num::Scalar(s)
    }
}

impl<F: LurkField> From<u64> for Num<F> {
    fn from(n: u64) -> Self {
        Num::<F>::U64(n)
    }
}

impl<F: LurkField> From<UInt> for Num<F> {
    fn from(n: UInt) -> Self {
        match n {
            UInt::U64(n) => Num::<F>::U64(n),
        }
    }
}

impl<F: LurkField> Serialize for Num<F> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Num::Scalar(f) => FWrap::serialize(&FWrap(*f), serializer),
            Num::U64(x) => FWrap::serialize(&FWrap(F::from(*x)), serializer),
        }
    }
}

impl<'de, F: LurkField> Deserialize<'de> for Num<F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let f = FWrap::deserialize(deserializer)?;
        Ok(Num::Scalar(f.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use blstrs::Scalar;
    use blstrs::Scalar as Fr;
    use ff::Field;

    #[test]
    fn test_add_assign() {
        // u64 - u64 - no overflow
        let mut a = Num::<Scalar>::U64(5);
        a += Num::from(10);
        assert_eq!(a, Num::from(15));

        // u64 - u64 - overflow
        let mut a = Num::from(u64::MAX);
        a += Num::from(10);
        assert_eq!(a, Num::Scalar(Scalar::from(u64::MAX) + Scalar::from(10)));

        // scalar - scalar - no overflow
        let mut a = Num::Scalar(Scalar::from(5));
        a += Num::Scalar(Scalar::from(10));
        assert_eq!(a, Num::Scalar(Scalar::from(5) + Scalar::from(10)));

        // scalar - u64 - overflow
        let mut a = Num::Scalar(Scalar::from(5));
        a += Num::from(u64::MAX);
        assert_eq!(a, Num::Scalar(Scalar::from(5) + Scalar::from(u64::MAX)));

        // scalar - u64 - overflow
        let mut a = Num::from(u64::MAX);
        a += Num::Scalar(Scalar::from(5));
        assert_eq!(a, Num::Scalar(Scalar::from(5) + Scalar::from(u64::MAX)));
    }

    #[test]
    fn test_sub_assign() {
        // u64 - u64 - no overflow
        let mut a = Num::<Scalar>::U64(10);
        a -= Num::U64(5);
        assert_eq!(a, Num::U64(5));

        // u64 - u64 - overflow
        let mut a = Num::U64(0);
        a -= Num::U64(10);
        assert_eq!(a, Num::Scalar(Scalar::from(0) - Scalar::from(10)));

        // scalar - scalar - no overflow
        let mut a = Num::Scalar(Scalar::from(10));
        a -= Num::Scalar(Scalar::from(5));
        assert_eq!(a, Num::Scalar(Scalar::from(10) - Scalar::from(5)));

        // scalar - u64 - overflow
        let mut a = Num::Scalar(Scalar::from(5));
        a -= Num::U64(10);
        assert_eq!(a, Num::Scalar(Scalar::from(5) - Scalar::from(10)));

        // scalar - u64 - no overflow
        let mut a = Num::Scalar(Scalar::from(10));
        a -= Num::U64(5);
        assert_eq!(a, Num::Scalar(Scalar::from(10) - Scalar::from(5)));

        // scalar - u64 - overflow
        let mut a = Num::U64(5);
        a -= Num::Scalar(Scalar::from(10));
        assert_eq!(a, Num::Scalar(Scalar::from(5) - Scalar::from(10)));

        // scalar - u64 - no overflow
        let mut a = Num::U64(10);
        a -= Num::Scalar(Scalar::from(5));
        assert_eq!(a, Num::Scalar(Scalar::from(10) - Scalar::from(5)));
    }

    #[test]
    fn test_mul_assign() {
        // u64 - u64 - no overflow
        let mut a = Num::<Scalar>::U64(5);
        a *= Num::U64(10);
        assert_eq!(a, Num::U64(5 * 10));

        // u64 - u64 - overflow
        let mut a = Num::U64(u64::MAX);
        a *= Num::U64(10);
        assert_eq!(a, Num::Scalar(Scalar::from(u64::MAX) * Scalar::from(10)));

        // scalar - scalar - no overflow
        let mut a = Num::Scalar(Scalar::from(5));
        a *= Num::Scalar(Scalar::from(10));
        assert_eq!(a, Num::Scalar(Scalar::from(5) * Scalar::from(10)));

        // scalar - u64 - overflow
        let mut a = Num::Scalar(Scalar::from(5));
        a *= Num::U64(u64::MAX);
        assert_eq!(a, Num::Scalar(Scalar::from(5) * Scalar::from(u64::MAX)));

        // scalar - u64 - overflow
        let mut a = Num::U64(u64::MAX);
        a *= Num::Scalar(Scalar::from(5));
        assert_eq!(a, Num::Scalar(Scalar::from(5) * Scalar::from(u64::MAX)));
    }

    #[test]
    fn test_div_assign() {
        // u64 - u64 - no overflow
        let mut a = Num::<Scalar>::U64(10);
        a /= Num::U64(5);
        assert_eq!(a, Num::U64(10 / 5));

        let mut a = Num::<Scalar>::U64(10);
        a /= Num::U64(3);

        // The result is not a Num::U64.
        assert!(matches!(a, Num::<Scalar>::Scalar(_)));

        a *= Num::U64(3);
        assert_eq!(a, Num::<Scalar>::Scalar(Scalar::from(10)));

        // scalar - scalar - no overflow
        let mut a = Num::Scalar(Scalar::from(10));
        a /= Num::Scalar(Scalar::from(5));
        assert_eq!(
            a,
            Num::Scalar(Scalar::from(10) * Scalar::from(5).invert().unwrap())
        );

        // scalar - u64 - no overflow
        let mut a = Num::Scalar(Scalar::from(10));
        a /= Num::U64(5);
        assert_eq!(
            a,
            Num::Scalar(Scalar::from(10) * Scalar::from(5).invert().unwrap())
        );

        // scalar - u64 - no overflow
        let mut a = Num::U64(10);
        a /= Num::Scalar(Scalar::from(5));
        assert_eq!(
            a,
            Num::Scalar(Scalar::from(10) * Scalar::from(5).invert().unwrap())
        );
    }

    #[test]
    fn test_num_hash() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::Hasher;

        let n = 123u64;
        let a: Num<Scalar> = Num::U64(n);
        let b = Num::Scalar(Scalar::from(n));

        let a_hash = {
            let mut hasher = DefaultHasher::new();
            a.hash(&mut hasher);
            hasher.finish()
        };

        let b_hash = {
            let mut hasher = DefaultHasher::new();
            b.hash(&mut hasher);
            hasher.finish()
        };

        assert_eq!(a_hash, b_hash);
    }

    #[test]
    fn test_negative_positive() {
        let mns = Fr::most_negative();
        let mps = mns - Fr::ONE;
        let mn = Num::Scalar(mns);
        let mp = Num::Scalar(mps);
        let zero = Num::Scalar(Fr::ZERO);

        assert!(mn.is_negative());
        assert!(!mp.is_negative());
        assert!(!zero.is_negative());
    }
}
