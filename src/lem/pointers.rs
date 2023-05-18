use crate::field::*;

use super::{lurk_symbol::LurkSymbol, tag::Tag};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Ptr<F: LurkField> {
    Leaf(Tag, F),
    Tree2(Tag, usize),
    Tree3(Tag, usize),
    Tree4(Tag, usize),
}

impl<F: LurkField> std::hash::Hash for Ptr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Ptr::Leaf(tag, f) => (0, tag, f.to_repr().as_ref()).hash(state),
            Ptr::Tree2(tag, x) => (1, tag, x).hash(state),
            Ptr::Tree3(tag, x) => (2, tag, x).hash(state),
            Ptr::Tree4(tag, x) => (3, tag, x).hash(state),
        }
    }
}

impl<F: LurkField> Ptr<F> {
    pub fn tag(&self) -> &Tag {
        match self {
            Ptr::Leaf(tag, _) => tag,
            Ptr::Tree2(tag, _) => tag,
            Ptr::Tree3(tag, _) => tag,
            Ptr::Tree4(tag, _) => tag,
        }
    }

    pub fn key_ptr_if_sym_ptr(self) -> Self {
        match self {
            Ptr::Leaf(Tag::Sym, f) => Ptr::Leaf(Tag::Key, f),
            Ptr::Tree2(Tag::Sym, x) => Ptr::Tree2(Tag::Key, x),
            Ptr::Tree3(Tag::Sym, x) => Ptr::Tree3(Tag::Key, x),
            Ptr::Tree4(Tag::Sym, x) => Ptr::Tree4(Tag::Key, x),
            _ => panic!("No Tag::Sym"),
        }
    }

    #[inline]
    pub fn num(f: F) -> Self {
        Ptr::Leaf(Tag::Num, f)
    }

    #[inline]
    pub fn char(c: char) -> Self {
        Ptr::Leaf(Tag::Char, F::from_char(c))
    }

    #[inline]
    pub fn comm(hash: F) -> Self {
        Ptr::Leaf(Tag::Comm, hash)
    }

    #[inline]
    pub fn null(tag: Tag) -> Self {
        Ptr::Leaf(tag, F::zero())
    }

    #[inline]
    pub fn lurk_sym(sym: &LurkSymbol) -> Self {
        Ptr::Leaf(Tag::LurkSym, sym.field())
    }

    #[inline]
    pub fn get_index2(&self) -> Option<usize> {
        match self {
            Ptr::Tree2(_, x) => Some(*x),
            _ => None,
        }
    }

    #[inline]
    pub fn get_index3(&self) -> Option<usize> {
        match self {
            Ptr::Tree3(_, x) => Some(*x),
            _ => None,
        }
    }

    #[inline]
    pub fn get_index4(&self) -> Option<usize> {
        match self {
            Ptr::Tree4(_, x) => Some(*x),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AquaPtr<F: LurkField> {
    pub tag: Tag,
    pub val: F,
}

impl<F: LurkField> AquaPtr<F> {
    #[inline]
    pub fn dummy() -> Self {
        Self {
            tag: Tag::Dummy,
            val: F::zero(),
        }
    }
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
