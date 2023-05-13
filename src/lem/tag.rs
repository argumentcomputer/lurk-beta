use crate::field::LurkField;

#[derive(Clone, Copy, PartialEq, std::cmp::PartialOrd, std::cmp::Ord, std::cmp::Eq, Hash)]
pub enum Tag {
    LurkSym,
    Num,
    U64,
    Char,
    Str,
    Comm,
    Fun,
    Cons,
    Sym,
    Key,
    Outermost,
    Terminal,
    Error,
}

impl Tag {
    pub fn field<F: LurkField>(self) -> F {
        match self {
            // Expression
            //Tag::Nil   => F::from_u16(0),
            Tag::Cons  => F::from_u16(1),
            Tag::Sym   => F::from_u16(2),
            Tag::Fun   => F::from_u16(3),
            Tag::Num   => F::from_u16(4),
            //Tag::Thunk => F::from_u16(5),
            Tag::Str   => F::from_u16(6),
            Tag::Char  => F::from_u16(7),
            Tag::Comm => F::from_u16(8),
            Tag::U64 => F::from_u16(9),
            Tag::Key => F::from_u16(10),
            // Continuation
            Tag::Outermost => F::from_u16(4096), // Outermost = 0b0001_0000_0000_0000
            Tag::Error => F::from_u16(4101), // Error = 0b0001_0000_0000_0101
            Tag::Terminal => F::from_u16(4110), // Terminal = 0b0001_0000_0000_1111
            // TODO: Unconvered
            _ => F::from_u16(666),
        }
    }
}
