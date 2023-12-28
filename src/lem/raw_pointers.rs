use super::Tag;
use crate::tag::ExprTag::{Cons, Fun, Nil, Num, Str, Sym};
use serde::{Deserialize, Serialize};

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
}
