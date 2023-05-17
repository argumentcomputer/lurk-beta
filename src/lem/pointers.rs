use crate::field::*;

use super::{lurk_symbol::LurkSymbol, tag::Tag};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PtrVal<F: LurkField> {
    Field(F),
    Index2(usize),
    Index3(usize),
    Index4(usize),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Ptr<F: LurkField> {
    pub tag: Tag,
    pub val: PtrVal<F>,
}

impl<F: LurkField> std::hash::Hash for Ptr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self.val {
            PtrVal::Field(x) => (0, self.tag, x.to_repr().as_ref()).hash(state),
            PtrVal::Index2(x) => (1, self.tag, x).hash(state),
            PtrVal::Index3(x) => (2, self.tag, x).hash(state),
            PtrVal::Index4(x) => (3, self.tag, x).hash(state),
        }
    }
}

impl<F: LurkField> Ptr<F> {
    pub fn key_ptr_if_sym_ptr(self) -> Self {
        match self {
            Ptr { tag: Tag::Sym, val } => Ptr { tag: Tag::Key, val },
            _ => self,
        }
    }

    #[inline]
    pub fn num(f: F) -> Self {
        Ptr {
            tag: Tag::Num,
            val: PtrVal::Field(f),
        }
    }

    #[inline]
    pub fn char(c: char) -> Self {
        Ptr {
            tag: Tag::Char,
            val: PtrVal::Field(F::from_char(c)),
        }
    }

    #[inline]
    pub fn null(tag: Tag) -> Self {
        Ptr {
            tag,
            val: PtrVal::Field(F::zero()),
        }
    }

    #[inline]
    pub fn lurk_sym(sym: LurkSymbol) -> Self {
        Ptr {
            tag: Tag::LurkSym,
            val: PtrVal::Field(sym.field()),
        }
    }

    #[inline]
    pub fn get_index2(&self) -> Option<usize> {
        match self.val {
            PtrVal::Index2(idx) => Some(idx),
            _ => None,
        }
    }

    #[inline]
    pub fn get_index3(&self) -> Option<usize> {
        match self.val {
            PtrVal::Index3(idx) => Some(idx),
            _ => None,
        }
    }

    #[inline]
    pub fn get_index4(&self) -> Option<usize> {
        match self.val {
            PtrVal::Index4(idx) => Some(idx),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AquaPtr<F: LurkField> {
    pub tag: Tag,
    pub val: F,
}

impl<F: LurkField> std::hash::Hash for AquaPtr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.tag.hash(state);
        self.val.to_repr().as_ref().hash(state);
    }
}

pub enum AquaPtrKind<F: LurkField> {
    Tree2(AquaPtr<F>, AquaPtr<F>),
    Tree3(AquaPtr<F>, AquaPtr<F>, AquaPtr<F>),
    Tree4(AquaPtr<F>, AquaPtr<F>, AquaPtr<F>, AquaPtr<F>),
    Comm(F, AquaPtr<F>), // secret, src
}
