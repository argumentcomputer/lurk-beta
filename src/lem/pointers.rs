use crate::field::*;

use super::{lurk_symbol::LurkSymbol, tag::Tag};

/// `Ptr` is the main piece of data LEMs operate on. We can think of a pointer
/// as a building block for trees that represent Lurk data. A pointer can be a
/// leaf that contains data encoded as an element of a `LurkField` or it can have
/// children. For performance, the children of a pointer are stored on an
/// `IndexMap` and the resulding index is carried by the pointer itself.
///
/// Finally, a pointer also has a tag, which says what kind of data it encodes.
/// Note that, in theory, the tag would be enough to tell how many children a
/// pointer has. But to simplify the implementation (and probably speed up
/// hydration), we express the number of children in the pointer's enum.
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

    pub fn sym_to_key(self) -> Self {
        match self {
            Ptr::Leaf(Tag::Sym, f) => Ptr::Leaf(Tag::Key, f),
            Ptr::Tree2(Tag::Sym, x) => Ptr::Tree2(Tag::Key, x),
            _ => panic!("Malformed sym pointer"),
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
        Ptr::Leaf(Tag::LurkSymbol, sym.field())
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

/// An `AquaPtr` is the result of "hydrating" a `Ptr`. This process is better
/// explained in the store but, in short, we want to know the Poseidon hash of
/// the children of a `Ptr`.
///
/// `AquaPtr`s are used mainly for proofs, but they're also useful when we want
/// to content-address a store.
///
/// An important note is that computing the respective `AquaPtr` of a `Ptr` can
/// be expensive because of the Poseidon hashes. That's why we operate on `Ptr`s
/// when interpreting LEMs and delay the need for `AquaPtr`s as much as possible.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AquaPtr<F: LurkField> {
    pub tag: Tag,
    pub hash: F,
}

#[allow(dead_code)]
pub(crate) enum AquaPtrKind<F: LurkField> {
    Tree2(AquaPtr<F>, AquaPtr<F>),
    Tree3(AquaPtr<F>, AquaPtr<F>, AquaPtr<F>),
    Tree4(AquaPtr<F>, AquaPtr<F>, AquaPtr<F>, AquaPtr<F>),
    Comm(F, AquaPtr<F>), // secret, src
}

impl<F: LurkField> AquaPtr<F> {
    #[inline]
    pub fn dummy() -> Self {
        Self {
            tag: Tag::Dummy,
            hash: F::zero(),
        }
    }
}

impl<F: LurkField> std::hash::Hash for AquaPtr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.tag.hash(state);
        self.hash.to_repr().as_ref().hash(state);
    }
}
