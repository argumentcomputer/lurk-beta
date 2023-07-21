use std::fmt::Display;

use crate::field::LurkField;

#[derive(Clone, Copy, PartialEq, Debug, PartialOrd, Ord, Eq, Hash)]
pub enum Tag {
    // expression tags
    Nil,
    Num,
    U64,
    Char,
    Str,
    Comm,
    Fun,
    Cons,
    Sym,
    Key,
    Thunk,
    // continuation tags
    Outermost,
    Dummy,
    Terminal,
    Error,
    Tail,
    Lookup,
    Let,
    // control tags. Note that this is a hack because we can't add arbitrary
    // constants yet.
    Return,
    MakeThunk,
    ApplyContinuation,
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
            Tag::Nil => write!(f, "Nil"),
            Tag::Num => write!(f, "Num"),
            Tag::U64 => write!(f, "U64"),
            Tag::Char => write!(f, "Char"),
            Tag::Str => write!(f, "Str"),
            Tag::Comm => write!(f, "Comm"),
            Tag::Fun => write!(f, "Fun"),
            Tag::Cons => write!(f, "Cons"),
            Tag::Sym => write!(f, "Sym"),
            Tag::Key => write!(f, "Key"),
            Tag::Thunk => write!(f, "Thunk"),
            Tag::Outermost => write!(f, "Outermost"),
            Tag::Dummy => write!(f, "Dummy"),
            Tag::Terminal => write!(f, "Terminal"),
            Tag::Error => write!(f, "Error"),
            Tag::Tail => write!(f, "Tail"),
            Tag::Lookup => write!(f, "Lookup"),
            Tag::Let => write!(f, "Let"),
            Tag::Return => write!(f, "Return"),
            Tag::ApplyContinuation => write!(f, "ApplyContinuation"),
            Tag::MakeThunk => write!(f, "MakeThunk"),
        }
    }
}
