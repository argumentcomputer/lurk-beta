use std::fmt::Display;

use crate::field::LurkField;

#[derive(Clone, Copy, PartialEq, Debug, PartialOrd, Ord, Eq, Hash)]
pub enum LurkSymbol {
    Nil,
}

impl LurkSymbol {
    #[inline]
    pub fn field<F: LurkField>(&self) -> F {
        F::from_u64(*self as u64)
    }

    pub fn from_field<F: LurkField>(f: &F) -> Option<Self> {
        match f.to_u64()? {
            0 => Some(Self::Nil),
            _ => None,
        }
    }
}

impl Display for LurkSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nil => write!(f, "Nil"),
        }
    }
}
