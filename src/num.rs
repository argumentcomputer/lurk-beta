use std::{
    fmt::Display,
    hash::Hash,
    ops::{AddAssign, DivAssign, MulAssign, SubAssign},
};

use ff::PrimeField;

/// Number type for Lurk. Has different internal representations to optimize evaluation.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Num<F: PrimeField> {
    Scalar(F),
    U64(u64),
}

impl<F: PrimeField> Display for Num<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Num::Scalar(s) => {
                let be_bytes = s.to_repr();
                write!(f, "Num(0x")?;
                for &b in be_bytes.as_ref().iter().rev() {
                    write!(f, "{:02x}", b)?;
                }
                write!(f, ")")?;
                Ok(())
            }
            Num::U64(n) => write!(f, "Num({:#x})", n),
        }
    }
}

#[allow(clippy::derive_hash_xor_eq)]
impl<F: PrimeField> Hash for Num<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Num::Scalar(s) => s.to_repr().as_ref().hash(state),
            Num::U64(n) => n.hash(state),
        }
    }
}

impl<F: PrimeField> AddAssign for Num<F> {
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

impl<F: PrimeField> SubAssign for Num<F> {
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

impl<F: PrimeField> MulAssign for Num<F> {
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

impl<F: PrimeField> DivAssign for Num<F> {
    fn div_assign(&mut self, rhs: Self) {
        assert!(!rhs.is_zero(), "can not divide by 0");
        match (*self, rhs) {
            (Num::U64(ref mut a), Num::U64(b)) => {
                if let Some(res) = a.checked_div(b) {
                    *self = Num::U64(res);
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

impl<F: PrimeField> Num<F> {
    pub fn is_zero(&self) -> bool {
        match self {
            Num::Scalar(s) => s.is_zero_vartime(),
            Num::U64(n) => n == &0,
        }
    }

    pub fn into_scalar(self) -> F {
        match self {
            Num::U64(n) => F::from(n),
            Num::Scalar(s) => s,
        }
    }
}

impl<F: PrimeField> From<u64> for Num<F> {
    fn from(n: u64) -> Self {
        Num::<F>::U64(n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use blstrs::Scalar;
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
        assert_eq!(a, Num::U64(10 / 3));

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
}
