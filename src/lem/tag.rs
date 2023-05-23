use std::fmt::Display;

use crate::field::LurkField;

#[derive(Clone, Copy, PartialEq, Debug, PartialOrd, Ord, Eq, Hash)]
pub enum Tag {
    // expression tags
    Dummy,
    Num,
    U64,
    Char,
    Str,
    Comm,
    Fun,
    Cons,
    Sym,
    Key,
    // continuation tags
    Outermost,
    Terminal,
    Error,
}

impl Tag {
    #[inline]
    pub fn to_field<F: LurkField>(self) -> F {
        // TODO: match values from current approach
        F::from_u64(self as u64)
    }
}

impl Display for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Tag::Dummy => write!(f, "Dummy"),
            Tag::Char => write!(f, "Char"),
            Tag::Num => write!(f, "Num"),
            Tag::Sym => write!(f, "Sym"),
            Tag::Outermost => write!(f, "Outermost"),
            Tag::Terminal => write!(f, "Terminal"),
            Tag::Error => write!(f, "Error"),
            _ => todo!(),
        }
    }
}
