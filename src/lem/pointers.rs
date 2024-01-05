use serde::{Deserialize, Serialize};

use crate::{
    field::LurkField,
    tag::ExprTag::{Cons, Fun, Nil, Num, Str, Sym},
};

use super::Tag;

/// `RawPtr` is the basic pointer type of the LEM store. An `Atom` points to a field
/// element, and a `HashN` points to `N` children, which are also raw pointers. Thus,
/// they are a building block for graphs that represent Lurk data.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub enum RawPtr {
    Atom(usize),
    Hash4(usize),
    Hash6(usize),
    Hash8(usize),
}

impl RawPtr {
    #[inline]
    pub fn is_hash(&self) -> bool {
        matches!(
            self,
            RawPtr::Hash4(..) | RawPtr::Hash6(..) | RawPtr::Hash8(..)
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

/// `Ptr` is a tagged pointer. The tag is there to say what kind of data it encodes.
/// Since tags can be encoded as field elements, they are also able to be expressed
/// as raw pointers. A `Ptr` can thus be seen as a tuple of `RawPtr`s.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub struct Ptr {
    tag: Tag,
    raw: RawPtr,
}

impl Ptr {
    #[inline]
    pub fn new(tag: Tag, raw: RawPtr) -> Self {
        Ptr { tag, raw }
    }

    #[inline]
    pub fn tag(&self) -> &Tag {
        &self.tag
    }

    #[inline]
    pub fn raw(&self) -> &RawPtr {
        &self.raw
    }

    #[inline]
    pub fn parts(&self) -> (&Tag, &RawPtr) {
        let Ptr { tag, raw } = self;
        (tag, raw)
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
        Ptr { tag, raw: self.raw }
    }

    #[inline]
    pub fn get_atom(&self) -> Option<usize> {
        self.raw().get_atom()
    }

    #[inline]
    pub fn get_index2(&self) -> Option<usize> {
        self.raw().get_hash4()
    }

    #[inline]
    pub fn get_index3(&self) -> Option<usize> {
        self.raw().get_hash6()
    }

    #[inline]
    pub fn get_index4(&self) -> Option<usize> {
        self.raw().get_hash8()
    }

    #[inline]
    pub fn atom(tag: Tag, idx: usize) -> Ptr {
        Ptr {
            tag,
            raw: RawPtr::Atom(idx),
        }
    }
}

/// A `ZPtr` is the result of "hydrating" a `Ptr`, which is a process of replacing
/// indices by hashes. That is, a `ZPtr` is a content-addressed, tagged, pointer.
/// By analogy, we can view ordinary field elements as hydrated raw pointers.
///
/// With `ZPtr`s we are able to content-address arbitrary DAGs, and thus be able to
/// represent these data structures as field elements. This is how we can prove facts
/// about data structures only using field elements. `ZPtr`s are also useful when we
/// want to content-address the store.
///
/// In principle, `ZPtr`s could be used in place of `Ptr`, but it is important to
/// note that content-addressing can be expensive, especially in the context of
/// interpretation, because of the Poseidon hashes. That's why we operate on `Ptr`s
/// when interpreting LEMs and delay the need for `ZPtr`s as much as possible.
pub type ZPtr<F> = crate::z_data::z_ptr::ZPtr<Tag, F>;

impl<F: LurkField> ZPtr<F> {
    #[inline]
    pub fn dummy() -> Self {
        Self(Tag::Expr(Nil), F::ZERO)
    }
}
