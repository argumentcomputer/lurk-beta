use serde::{Deserialize, Serialize};

use crate::{
    field::LurkField,
    tag::ExprTag::{Cons, Fun, Nil, Num, Str, Sym},
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub enum Ptr {
    Atom(Tag, usize),
    Tuple2(Tag, usize),
    Tuple3(Tag, usize),
    Tuple4(Tag, usize),
}

impl Ptr {
    pub fn tag(&self) -> &Tag {
        match self {
            Ptr::Atom(tag, _) | Ptr::Tuple2(tag, _) | Ptr::Tuple3(tag, _) | Ptr::Tuple4(tag, _) => {
                tag
            }
        }
    }

    #[inline]
    pub fn has_tag(&self, tag: &Tag) -> bool {
        self.tag() == tag
    }

    #[inline]
    pub fn has_tag_in(&self, tags: &[Tag]) -> bool {
        tags.contains(self.tag())
    }

    #[inline]
    pub fn is_sym(&self) -> bool {
        self.has_tag(&Tag::Expr(Sym))
    }

    #[inline]
    pub fn is_num(&self) -> bool {
        self.has_tag(&Tag::Expr(Num))
    }

    #[inline]
    pub fn is_str(&self) -> bool {
        self.has_tag(&Tag::Expr(Str))
    }

    #[inline]
    pub fn is_fun(&self) -> bool {
        self.has_tag(&Tag::Expr(Fun))
    }

    #[inline]
    pub fn is_nil(&self) -> bool {
        self.has_tag(&Tag::Expr(Nil))
    }

    #[inline]
    pub fn is_list(&self) -> bool {
        self.has_tag_in(&[Tag::Expr(Cons), Tag::Expr(Nil)])
    }

    #[inline]
    pub fn cast(self, tag: Tag) -> Self {
        match self {
            Ptr::Atom(_, x) => Ptr::Atom(tag, x),
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
    pub fn get_atom(&self) -> Option<usize> {
        match self {
            Ptr::Atom(_, x) => Some(*x),
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
