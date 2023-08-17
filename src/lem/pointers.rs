use crate::{field::*, tag::ContTag::Dummy, tag::ExprTag::*};

use super::Tag;

/// `Ptr` is the main piece of data LEMs operate on. We can think of a pointer
/// as a building block for trees that represent Lurk data. A pointer can be a
/// leaf that contains data encoded as an element of a `LurkField` or it can have
/// children. For performance, the children of a pointer are stored on an
/// `IndexSet` and the resulding index is carried by the pointer itself.
///
/// A pointer also has a tag, which says what kind of data it encodes. On
/// previous implementations, the tag would be used to infer the number of
/// children a pointer has. However, LEMs require extra flexibility because LEM
/// hashing operations can plug any tag to the resulting pointer. Thus, the
/// number of children have to be made explicit as the `Ptr` enum.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
            Ptr::Leaf(tag, _) | Ptr::Tree2(tag, _) | Ptr::Tree3(tag, _) | Ptr::Tree4(tag, _) => tag,
        }
    }

    #[inline]
    pub fn num(f: F) -> Self {
        Ptr::Leaf(Tag::Expr(Num), f)
    }

    #[inline]
    pub fn char(c: char) -> Self {
        Ptr::Leaf(Tag::Expr(Char), F::from_char(c))
    }

    #[inline]
    pub fn comm(hash: F) -> Self {
        Ptr::Leaf(Tag::Expr(Comm), hash)
    }

    #[inline]
    pub fn null(tag: Tag) -> Self {
        Ptr::Leaf(tag, F::ZERO)
    }

    pub fn is_null(&self) -> bool {
        match self {
            Ptr::Leaf(_, f) => f == &F::ZERO,
            _ => false,
        }
    }

    pub fn is_nil(&self) -> bool {
        self.tag() == &Tag::Expr(Nil)
    }

    #[inline]
    pub fn cast(&self, tag: Tag) -> Self {
        match self {
            Ptr::Leaf(_, f) => Ptr::Leaf(tag, *f),
            Ptr::Tree2(_, x) => Ptr::Tree2(tag, *x),
            Ptr::Tree3(_, x) => Ptr::Tree3(tag, *x),
            Ptr::Tree4(_, x) => Ptr::Tree4(tag, *x),
        }
    }

    #[inline]
    pub fn get_num(&self) -> Option<&F> {
        match self {
            Ptr::Leaf(Tag::Expr(Num), f) => Some(f),
            _ => None,
        }
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

/// A `ZPtr` is the result of "hydrating" a `Ptr`. This process is better
/// explained in the store but, in short, we want to know the Poseidon hash of
/// the children of a `Ptr`.
///
/// `ZPtr`s are used mainly for proofs, but they're also useful when we want
/// to content-address a store.
///
/// An important note is that computing the respective `ZPtr` of a `Ptr` can be
/// expensive because of the Poseidon hashes. That's why we operate on `Ptr`s
/// when interpreting LEMs and delay the need for `ZPtr`s as much as possible.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ZPtr<F: LurkField> {
    pub tag: Tag,
    pub hash: F,
}

/// `ZChildren` keeps track of the children of `ZPtr`s, in case they have any.
/// This information is saved during hydration and is needed to content-address
/// a store.
pub(crate) enum ZChildren<F: LurkField> {
    Tree2(ZPtr<F>, ZPtr<F>),
    Tree3(ZPtr<F>, ZPtr<F>, ZPtr<F>),
    Tree4(ZPtr<F>, ZPtr<F>, ZPtr<F>, ZPtr<F>),
}

impl<F: LurkField> ZPtr<F> {
    #[inline]
    pub fn dummy() -> Self {
        Self {
            tag: Tag::Cont(Dummy),
            hash: F::ZERO,
        }
    }
}

impl<F: LurkField> std::hash::Hash for ZPtr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.tag.hash(state);
        self.hash.to_repr().as_ref().hash(state);
    }
}
