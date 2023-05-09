use crate::field::LurkField;

use super::tag::Tag;

#[derive(Clone, Copy, PartialEq, std::cmp::Eq, Hash)]
pub enum LurkData<F: LurkField> {
    Char(char),
    U64(u64),
    Num(F),
    Comm(F, F),
    Ptr(Tag, Option<usize>),
}

impl<F: LurkField> LurkData<F> {
    pub fn key_ptr_if_sym_ptr(self) -> LurkData<F> {
        match self {
            LurkData::Ptr(Tag::Sym, idx) => LurkData::Ptr(Tag::Key, idx),
            _ => self,
        }
    }
}

pub enum AquaPtr<F: LurkField> {
    Leaf(Tag, F),
    Tree2(Tag, F, Box<(AquaPtr<F>, AquaPtr<F>)>),
    Tree3(Tag, F, Box<(AquaPtr<F>, AquaPtr<F>, AquaPtr<F>)>),
    Tree4(
        Tag,
        F,
        Box<(AquaPtr<F>, AquaPtr<F>, AquaPtr<F>, AquaPtr<F>)>,
    ),
}
