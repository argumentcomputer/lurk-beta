use crate::field::LurkField;

#[derive(Clone, Copy, PartialEq, std::cmp::PartialOrd, std::cmp::Ord, std::cmp::Eq, Hash)]
pub enum Tag {
    Nil,
    Reserved,
    Const,
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
    Outermost,
    Terminal,
    Error,
}

impl Tag {
    pub fn field<F: LurkField>(self) -> F {
        todo!()
    }
}
