use crate::field::*;

use super::tag::Tag;

#[derive(Clone, Copy, PartialEq, std::cmp::Eq)]
pub enum PtrVal<F: LurkField> {
    Char(char),
    U64(u64),
    Num(F),
    Index(usize),
    Null,
}

impl<F: LurkField> std::hash::Hash for PtrVal<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            PtrVal::Char(x) => (0, x).hash(state),
            PtrVal::U64(x) => (1, x).hash(state),
            PtrVal::Num(x) => (2, x.to_repr().as_ref()).hash(state),
            PtrVal::Index(x) => (3, x).hash(state),
            PtrVal::Null => (0).hash(state),
        }
    }
}

#[derive(Clone, Copy, PartialEq, std::cmp::Eq)]
pub struct Ptr<F: LurkField> {
    pub tag: Tag,
    pub val: PtrVal<F>,
}

impl<F: LurkField> std::hash::Hash for Ptr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.tag.hash(state);
        self.val.hash(state);
    }
}

impl<F: LurkField> Ptr<F> {
    pub fn key_ptr_if_sym_ptr(self) -> Ptr<F> {
        match self {
            Ptr { tag: Tag::Sym, val } => Ptr {tag: Tag::Key, val},
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
