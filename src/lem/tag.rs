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
        todo!()
    }
}
