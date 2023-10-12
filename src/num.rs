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
        prop_oneof![
            any::<u64>().prop_map(Num::U64),
            any::<FWrap<Fr>>().prop_map(|f| Num::Scalar(f.0)),
        ]
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
    use nom::ToUsize;
    use proptest::proptest;

    use ff::Field;
    use pasta_curves::pallas::Scalar;
    use pasta_curves::pallas::Scalar as Fr;

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 1000,
            .. ProptestConfig::default()
          })]


        #[test]
        fn prop_add_assign(a in any::<Num<Fr>>(), b in any::<Num<Fr>>()){
            let mut c = a;
            c += b;

            match (a, b) {
                (Num::U64(x1), Num::U64(x2)) => {
                    // does this overflow?
                    if x1.checked_add(x2).is_none() {
                        assert_eq!(c, Num::Scalar(Scalar::from(x1) + Scalar::from(x2)));
                    } else {
                        assert_eq!(c, Num::U64(x1 + x2));
                    }
                },
                (Num::Scalar(x1), Num::U64(x2))  | (Num::U64(x2), Num::Scalar(x1)) => {
                    assert_eq!(c, Num::Scalar(x1 + Scalar::from(x2)));
                },
                (Num::Scalar(x1), Num::Scalar(x2)) => {
                    assert_eq!(c, Num::Scalar(x1 + x2));
                }
            }
        }

        #[test]
        fn prop_sub_assign(a in any::<Num<Fr>>(), b in any::<Num<Fr>>()) {
            let mut c = a;
            c -= b;

            match (a, b) {
                (Num::U64(x1), Num::U64(x2)) => {
                    // does this underflow?
                    if x1.to_usize().checked_sub(x2.to_usize()).is_none(){
                        assert_eq!(c, Num::Scalar(Scalar::from(x1) - Scalar::from(x2)));
                    } else {
                        assert_eq!(c, Num::U64(x1 - x2));
                    }
                },
                (Num::Scalar(x1), Num::U64(x2))  => {
                    assert_eq!(c, Num::Scalar(x1 - Scalar::from(x2)));
                },
                 (Num::U64(x1), Num::Scalar(x2)) => {
                    assert_eq!(c, Num::Scalar(Scalar::from(x1) - x2));
                },
                (Num::Scalar(x1), Num::Scalar(x2)) => {
                    assert_eq!(c, Num::Scalar(x1 - x2));
                }
            }
        }

        #[test]
        fn prop_mul_assign(a in any::<Num<Fr>>(), b in any::<Num<Fr>>()){
            let mut c = a;
            c *= b;

            match (a, b) {
                (Num::U64(x1), Num::U64(x2)) => {
                    // does this overflow?
                    if  x1.checked_mul(x2).is_none() {
                        assert_eq!(c, Num::Scalar(Scalar::from(x1) * Scalar::from(x2)));
                    } else {
                        assert_eq!(c, Num::U64(x1 * x2));
                    }
                },
                (Num::Scalar(x1), Num::U64(x2))  | (Num::U64(x2), Num::Scalar(x1)) => {
                    assert_eq!(c, Num::Scalar(x1 * Scalar::from(x2)));
                },
                (Num::Scalar(x1), Num::Scalar(x2)) => {
                    assert_eq!(c, Num::Scalar(x1 * x2));
                }
            }
        }

        #[test]
        fn prop_div_assign(a in any::<Num<Fr>>(), b in any::<Num<Fr>>().prop_filter("divisor must be non-zero", |b| !b.is_zero())){
            let mut c = a;
            c /= b;

            match (a, b) {
                (Num::U64(x1), Num::U64(x2)) => {
                    // is x1 an exact multiple?
                    if let Some(x) = x1.checked_rem_euclid(x2){
                        if x == 0 {
                            assert_eq!(c, Num::U64(x1 / x2));

                        } else {
                            c *= b;
                            assert_eq!(c, Num::Scalar(Scalar::from(x1)));
                        }
                    } else {
                        unreachable!("excluded by prop_filter")
                    }
                },
                (Num::U64(x1), Num::Scalar(_))  => {
                    c *= b;
                    assert_eq!(c, Num::Scalar(Scalar::from(x1)));
                },
                (Num::Scalar(_), _) => {
                    c *= b;
                    assert_eq!(c, a);
                }
            }
        }

        #[test]
        fn prop_mosts(a in any::<Num<Fr>>()) {
            if a.is_negative() {
                assert!(a >= Num::most_negative());
                assert!(a < Num::most_positive());
            } else {
                assert!(a <= Num::most_positive());
                assert!(a > Num::most_negative());
            }
        }

        #[test]
        fn prop_sign_and_sub(a in any::<Num<Fr>>(), b in any::<Num<Fr>>()) {
            let mut c = a;
            c -= b;

            if a.is_negative() {
                // does this "underflow" (in the sense of consistency w/ Num::is_less_than)
                let mut underflow_boundary = Num::most_negative();
                underflow_boundary += b;

                if a >= underflow_boundary {
                  assert!(c.is_negative());
                }
            } else if b.is_negative() {
                // does this "overflow" (in the sense of consistency w/ Num::is_less_than)
                // b negative, a - b = a + |b| which can be greater than most_positive
                let mut overflow_boundary = Num::most_positive();
                overflow_boundary -= b;

                if a <= overflow_boundary {
                    assert!(a.is_less_than(&c));
                }
            } else {
                assert!(c.is_less_than(&a));
            }
        }

        #[test]
        fn prop_lesser(a in any::<Num<Fr>>(), b in any::<Num<Fr>>()) {
            // operands should be distinct for is_less_than
            prop_assume!(a != b);

            // anti-symmetry
            if a.is_less_than(&b) && b.is_less_than(&a)  {
                assert_eq!(a, b);
            }

            match (a, b) {
                (Num::U64(x1), Num::U64(x2)) => {
                    assert_eq!(a.is_less_than(&b), x1 < x2);
                },
                (Num::Scalar(x1), Num::Scalar(x2)) => {
                    // this time, we express the conditions in terms of the
                    // saclar  operation
                    let underflow = {
                        let mut underflow_boundary = Scalar::most_negative();
                        underflow_boundary += x2;
                        x1 > underflow_boundary
                    };
                    let overflow = {
                        let mut overflow_boundary = Scalar::most_positive();
                        overflow_boundary -= x2;
                        x1 > overflow_boundary
                    };
                    if !underflow && !overflow {
                        assert_eq!(a.is_less_than(&b), Num::Scalar(x1 - x2).is_negative());
                    }
                },
                (Num::U64(x1), Num::Scalar(x2)) if !x2.is_negative() => {
                    assert_eq!(a.is_less_than(&b), Scalar::from(x1) < x2);
                },
                (Num::U64(_), Num::Scalar(_))  => { // right_operand.is_negative()
                    assert!(!a.is_less_than(&b));
                },
                (Num::Scalar(x1), Num::U64(x2)) if !x1.is_negative() => {
                    assert_eq!(a.is_less_than(&b), x1 < Scalar::from(x2));
                }
                (Num::Scalar(_), Num::U64(_))  => { // left_operand.is_negative()
                    assert!(a.is_less_than(&b));
                },
            }
        }
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
