use std::fmt::Display;

use crate::field::LurkField;

pub enum Symbol {
    Sym(Vec<String>),
    Key(Vec<String>),
}

impl Symbol {
    pub fn sym(path: Vec<&str>) -> Symbol {
        Symbol::Sym(path.iter().map(|x| x.to_string()).collect())
    }

    pub fn key(path: Vec<&str>) -> Symbol {
        Symbol::Key(path.iter().map(|x| x.to_string()).collect())
    }

    #[inline]
    pub fn root() -> Self {
        Self::Sym(vec![])
    }

    #[inline]
    pub fn path(&self) -> &Vec<String> {
        match self {
            Self::Sym(path) | Self::Key(path) => path,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Debug, PartialOrd, Ord, Eq, Hash)]
pub enum LurkSymbol {
    Nil,
}

impl LurkSymbol {
    #[inline]
    pub fn field<F: LurkField>(&self) -> F {
        F::from_u64(*self as u64)
    }
}

impl Display for LurkSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nil => write!(f, "Nil"),
        }
    }
}
