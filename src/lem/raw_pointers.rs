use serde::{Deserialize, Serialize};

use crate::tag::ExprTag::{Cons, Fun, Nil, Num, Str, Sym};

use super::Tag;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub enum RawPtr {
    Atom(usize),
    Hash3(usize),
    Hash4(usize),
    Hash6(usize),
    Hash8(usize),
}

impl RawPtr {
    #[inline]
    pub fn is_hash(&self) -> bool {
        matches!(
            self,
            RawPtr::Hash3(..) | RawPtr::Hash4(..) | RawPtr::Hash6(..) | RawPtr::Hash8(..)
        )
    }

    #[inline]
    pub fn get_atom(&self) -> Option<usize> {
        match self {
            RawPtr::Atom(x) => Some(*x),
            _ => None,
        }
    }

    #[inline]
    pub fn get_hash3(&self) -> Option<usize> {
        match self {
            RawPtr::Hash3(x) => Some(*x),
            _ => None,
        }
    }

    #[inline]
    pub fn get_hash4(&self) -> Option<usize> {
        match self {
            RawPtr::Hash4(x) => Some(*x),
            _ => None,
        }
    }

    #[inline]
    pub fn get_hash6(&self) -> Option<usize> {
        match self {
            RawPtr::Hash6(x) => Some(*x),
            _ => None,
        }
    }

    #[inline]
    pub fn get_hash8(&self) -> Option<usize> {
        match self {
            RawPtr::Hash8(x) => Some(*x),
            _ => None,
        }
    }
}

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
pub struct Ptr {
    tag: Tag,
    pay: RawPtr,
}

impl Ptr {
    pub fn new(tag: Tag, pay: RawPtr) -> Self {
        Ptr { tag, pay }
    }

    pub fn tag(&self) -> &Tag {
        &self.tag
    }

    pub fn pay(&self) -> &RawPtr {
        &self.pay
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
        Ptr { tag, pay: self.pay }
    }

    #[inline]
    pub fn get_atom(&self) -> Option<usize> {
        self.pay().get_atom()
    }

    #[inline]
    pub fn get_index2(&self) -> Option<usize> {
        self.pay().get_hash4()
    }

    #[inline]
    pub fn get_index3(&self) -> Option<usize> {
        self.pay().get_hash6()
    }

    #[inline]
    pub fn get_index4(&self) -> Option<usize> {
        self.pay().get_hash8()
    }

    #[inline]
    pub fn atom(tag: Tag, idx: usize) -> Ptr {
        Ptr {
            tag,
            pay: RawPtr::Atom(idx),
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

/*
impl<F: LurkField> ZPtr<F> {
    #[inline]
    pub fn dummy() -> Self {
        Self(Tag::Expr(Nil), F::ZERO)
    }
}
*/
