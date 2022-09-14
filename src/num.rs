use crate::field::FWrap;
use serde::{Deserialize, Serialize};
use std::{
    fmt::Display,
    hash::Hash,
    ops::{AddAssign, DivAssign, MulAssign, SubAssign},
};

use crate::field::LurkField;

/// Number type for Lurk. Has different internal representations to optimize evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Num<F: LurkField> {
    Scalar(F),
    U64(u64),
}

impl<F: LurkField> Copy for Num<F> {}

impl<F: LurkField> Display for Num<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Num::Scalar(s) => {
                let le_bytes = s.to_repr();
                write!(f, "0x")?;
                for &b in le_bytes.as_ref().iter().rev() {
                    write!(f, "{:02x}", b)?;
                }
                Ok(())
            }
            Num::U64(n) => write!(f, "{}", n),
        }
    }
}

#[allow(clippy::derive_hash_xor_eq)]
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

impl<F: LurkField> AddAssign for Num<F> {
    fn add_assign(&mut self, rhs: Self) {
        match (*self, rhs) {
            (Num::U64(ref mut a), Num::U64(b)) => {
                if let Some(res) = a.checked_add(b) {
                    *self = Num::U64(res);
                } else {
                    *self = Num::Scalar(F::from(*a) + F::from(b));
                }
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
                if let Some(res) = a.checked_sub(b) {
                    *self = Num::U64(res);
                } else {
                    *self = Num::Scalar(F::from(*a) - F::from(b));
                }
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
                if let Some(res) = a.checked_mul(b) {
                    *self = Num::U64(res);
                } else {
                    *self = Num::Scalar(F::from(*a) * F::from(b));
                }
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
                if *a % b == 0 {
                    *self = Num::U64(*a / b);
                } else {
                    *self = Num::Scalar(F::from(*a) * F::from(b).invert().unwrap());
                }
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
    pub fn is_zero(&self) -> bool {
        match self {
            Num::Scalar(s) => s.is_zero_vartime(),
            Num::U64(n) => n == &0,
        }
    }

    pub fn is_less_than(&self, other: Num<F>) -> bool {
        match (self.is_negative(), other.is_negative()) {
            // Both positive
            (false, false) => self.is_less_than_aux(other),
            // Both negative, reverse sign of simple test.
            (true, true) => !self.is_equal(other) && !self.is_less_than_aux(other),
            (true, false) => true,
            (false, true) => false,
        }
    }

    fn is_less_than_aux(&self, other: Num<F>) -> bool {
        match (self, other) {
            (Num::U64(s), Num::U64(other)) => s < &other,
            (Num::Scalar(s), Num::Scalar(other)) => Num::Scalar(*s - other).is_negative(),
            (a, b) => Num::Scalar(a.into_scalar()).is_less_than(Num::Scalar(b.into_scalar())),
        }
    }

    pub fn is_equal(&self, other: Num<F>) -> bool {
        match (self, other) {
            (Num::U64(s), Num::U64(other)) => s == &other,
            (a, b) => a.into_scalar() == b.into_scalar(),
        }
    }

    pub fn most_negative() -> Self {
        Num::Scalar(F::most_negative())
    }

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

    pub fn into_scalar(self) -> F {
        match self {
            Num::U64(n) => F::from(n),
            Num::Scalar(s) => s,
        }
    }

    pub fn from_scalar(s: F) -> Self {
        Num::Scalar(s)
    }
}

impl<F: LurkField> From<u64> for Num<F> {
    fn from(n: u64) -> Self {
        Num::<F>::U64(n)
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

    use quickcheck::{Arbitrary, Gen};

    use crate::field::FWrap;
    use crate::test::frequency;
    use blstrs::Scalar;
    use blstrs::Scalar as Fr;
    use ff::Field;

    impl Arbitrary for Num<Fr> {
        fn arbitrary(g: &mut Gen) -> Self {
            let input: Vec<(i64, Box<dyn Fn(&mut Gen) -> Num<Fr>>)> = vec![
                (100, Box::new(|g| Num::U64(Arbitrary::arbitrary(g)))),
                (
                    100,
                    Box::new(|g| {
                        let f = FWrap::arbitrary(g);
                        Num::Scalar(f.0)
                    }),
                ),
            ];
            frequency(g, input)
        }
    }

    #[quickcheck]
    fn prop_num_ipld(x: Num<Fr>) -> bool {
        if let Ok(ipld) = libipld::serde::to_ipld(x) {
            if let Ok(y) = libipld::serde::from_ipld(ipld) {
                Num::Scalar(x.into_scalar()) == y
            } else {
                false
            }
        } else {
            false
        }
    }

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
        let mps = mns - Fr::one();
        let mn = Num::Scalar(mns);
        let mp = Num::Scalar(mps);
        let zero = Num::Scalar(Fr::zero());

        assert!(mn.is_negative());
        assert!(!mp.is_negative());
        assert!(!zero.is_negative());
    }
}
