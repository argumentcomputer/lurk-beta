use crate::field::*;

use super::tag::Tag;

#[derive(Clone, Copy, PartialEq, std::cmp::Eq)]
pub enum Ptr<F: LurkField> {
    Char(char),
    U64(u64),
    Num(F),
    Indexed(Tag, Option<usize>),
}

impl<F: LurkField> std::hash::Hash for Ptr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Ptr::Char(x) => (0, x).hash(state),
            Ptr::U64(x) => (1, x).hash(state),
            Ptr::Num(x) => (2, x.to_repr().as_ref()).hash(state),
            Ptr::Indexed(x, y) => (3, x, y).hash(state),
        }
    }
}

impl<F: LurkField> Ptr<F> {
    pub fn key_ptr_if_sym_ptr(self) -> Ptr<F> {
        match self {
            Ptr::Indexed(Tag::Sym, idx) => Ptr::Indexed(Tag::Key, idx),
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
