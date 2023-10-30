use serde::{Deserialize, Serialize};

use crate::{
    field::*,
    tag::ExprTag::{Char, Comm, Nil, Num, U64},
};

use super::Tag;

/// `Ptr` is the main piece of data LEMs operate on. We can think of a pointer
/// as a building block for trees that represent Lurk data. A pointer can be a
/// atom that contains data encoded as an element of a `LurkField` or it can have
/// children. For performance, the children of a pointer are stored on an
/// `IndexSet` and the resulding index is carried by the pointer itself.
///
/// A pointer also has a tag, which says what kind of data it encodes. On
/// previous implementations, the tag would be used to infer the number of
/// children a pointer has. However, LEMs require extra flexibility because LEM
/// hashing operations can plug any tag to the resulting pointer. Thus, the
/// number of children have to be made explicit as the `Ptr` enum.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Ptr<F: LurkField> {
    Atom(Tag, F),
    Tuple2(Tag, usize),
    Tuple3(Tag, usize),
    Tuple4(Tag, usize),
}

impl<F: LurkField> std::hash::Hash for Ptr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Ptr::Atom(tag, f) => (0, tag, f.to_repr().as_ref()).hash(state),
            Ptr::Tuple2(tag, x) => (1, tag, x).hash(state),
            Ptr::Tuple3(tag, x) => (2, tag, x).hash(state),
            Ptr::Tuple4(tag, x) => (3, tag, x).hash(state),
        }
    }
}

impl<F: LurkField> Ptr<F> {
    pub fn tag(&self) -> &Tag {
        match self {
            Ptr::Atom(tag, _) | Ptr::Tuple2(tag, _) | Ptr::Tuple3(tag, _) | Ptr::Tuple4(tag, _) => {
                tag
            }
        }
    }

    #[inline]
    pub fn num(f: F) -> Self {
        Ptr::Atom(Tag::Expr(Num), f)
    }

    #[inline]
    pub fn num_u64(u: u64) -> Self {
        Ptr::Atom(Tag::Expr(Num), F::from_u64(u))
    }

    #[inline]
    pub fn u64(u: u64) -> Self {
        Ptr::Atom(Tag::Expr(U64), F::from_u64(u))
    }

    #[inline]
    pub fn char(c: char) -> Self {
        Ptr::Atom(Tag::Expr(Char), F::from_char(c))
    }

    #[inline]
    pub fn comm(hash: F) -> Self {
        Ptr::Atom(Tag::Expr(Comm), hash)
    }

    #[inline]
    pub fn zero(tag: Tag) -> Self {
        Ptr::Atom(tag, F::ZERO)
    }

    pub fn is_zero(&self) -> bool {
        match self {
            Ptr::Atom(_, f) => f == &F::ZERO,
            _ => false,
        }
    }

    pub fn is_nil(&self) -> bool {
        self.tag() == &Tag::Expr(Nil)
    }

    #[inline]
    pub fn dummy() -> Self {
        Self::zero(Tag::Expr(Nil))
    }

    #[inline]
    pub fn cast(self, tag: Tag) -> Self {
        match self {
            Ptr::Atom(_, f) => Ptr::Atom(tag, f),
            Ptr::Tuple2(_, x) => Ptr::Tuple2(tag, x),
            Ptr::Tuple3(_, x) => Ptr::Tuple3(tag, x),
            Ptr::Tuple4(_, x) => Ptr::Tuple4(tag, x),
        }
    }

    #[inline]
    pub fn is_tuple(&self) -> bool {
        matches!(self, Ptr::Tuple2(..) | Ptr::Tuple3(..) | Ptr::Tuple4(..))
    }

    #[inline]
    pub fn get_atom(&self) -> Option<&F> {
        match self {
            Ptr::Atom(_, f) => Some(f),
            _ => None,
        }
    }

    #[inline]
    pub fn get_index2(&self) -> Option<usize> {
        match self {
            Ptr::Tuple2(_, x) => Some(*x),
            _ => None,
        }
    }

    #[inline]
    pub fn get_index3(&self) -> Option<usize> {
        match self {
            Ptr::Tuple3(_, x) => Some(*x),
            _ => None,
        }
    }

    #[inline]
    pub fn get_index4(&self) -> Option<usize> {
        match self {
            Ptr::Tuple4(_, x) => Some(*x),
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
pub type ZPtr<F> = crate::z_data::z_ptr::ZPtr<Tag, F>;

impl<F: LurkField> ZPtr<F> {
    #[inline]
    pub fn dummy() -> Self {
        Self(Tag::Expr(Nil), F::ZERO)
    }
}

/// `ZChildren` keeps track of the children of `ZPtr`s, in case they have any.
/// This information is saved during hydration and is needed to content-address
/// a store.
#[derive(Debug, Serialize, Deserialize)]
pub enum ZChildren<F: LurkField> {
    Atom,
    Tuple2(ZPtr<F>, ZPtr<F>),
    Tuple3(ZPtr<F>, ZPtr<F>, ZPtr<F>),
    Tuple4(ZPtr<F>, ZPtr<F>, ZPtr<F>, ZPtr<F>),
}
