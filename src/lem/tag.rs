use crate::field::LurkField;

#[derive(Clone, Copy, PartialEq, std::cmp::Eq, Hash)]
pub enum Tag {
    Nil,
    Num,
    U64,
    Char,
    Str,
    Comm,
    Fun,
    Cons,
    Name,
    Sym,
    Key,
    Thunk,
    Outermost,
    Terminal,
    Error,
}

impl Tag {
    pub fn to_field<F: LurkField>(self) -> F {
        todo!()
    }

    pub fn from_field<F: LurkField>(f: F) -> Option<Tag> {
        todo!()
    }
}
