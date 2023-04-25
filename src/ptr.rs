#[cfg(not(target_arch = "wasm32"))]
use std::hash::Hash;
use std::marker::PhantomData;

use crate::field::LurkField;
use crate::tag::{ContTag, ExprTag};

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RawPtr {
    Null,
    Opaque(usize),
    Index(usize),
}

impl RawPtr {
    pub fn new(p: usize) -> Self {
        Self::Index(p)
    }

    pub const fn is_opaque(&self) -> bool {
        matches!(self, Self::Opaque(_))
    }

    pub fn is_null(&self) -> bool {
        matches!(self, Self::Null)
    }

    pub fn opaque_idx(&self) -> Option<usize> {
        match self {
            Self::Opaque(x) => Some(*x),
            _ => None,
        }
    }

    pub fn idx(&self) -> Option<usize> {
        match self {
            Self::Index(x) => Some(*x),
            _ => None,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Ptr<F: LurkField> {
    pub tag: ExprTag,
    pub raw: RawPtr,
    pub _f: PhantomData<F>,
}

#[allow(clippy::derived_hash_with_manual_eq)]
impl<F: LurkField> Hash for Ptr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.tag.hash(state);
        self.raw.hash(state);
    }
}

impl<F: LurkField> Ptr<F> {
    // TODO: Make these methods and the similar ones defined on expression consistent, probably including a shared trait.

    // NOTE: Although this could be a type predicate now, when NIL becomes a symbol, it won't be possible.
    pub const fn is_nil(&self) -> bool {
        matches!(self.tag, ExprTag::Nil)
        // FIXME: check value also, probably
    }
    pub const fn is_cons(&self) -> bool {
        matches!(self.tag, ExprTag::Cons)
    }

    pub const fn is_atom(&self) -> bool {
        !self.is_cons()
    }

    pub const fn is_list(&self) -> bool {
        matches!(self.tag, ExprTag::Nil | ExprTag::Cons)
    }

    pub const fn is_opaque(&self) -> bool {
        self.raw.is_opaque()
    }

    pub const fn as_cons(self) -> Option<Self> {
        if self.is_cons() {
            Some(self)
        } else {
            None
        }
    }

    pub const fn as_list(self) -> Option<Self> {
        if self.is_list() {
            Some(self)
        } else {
            None
        }
    }

    pub fn index(tag: ExprTag, idx: usize) -> Self {
        Ptr {
            tag,
            raw: RawPtr::Index(idx),
            _f: Default::default(),
        }
    }

    pub fn opaque(tag: ExprTag, idx: usize) -> Self {
        Ptr {
            tag,
            raw: RawPtr::Opaque(idx),
            _f: Default::default(),
        }
    }

    pub fn null(tag: ExprTag) -> Self {
        Ptr {
            tag,
            raw: RawPtr::Null,
            _f: Default::default(),
        }
    }
}

impl<F: LurkField> From<char> for Ptr<F> {
    fn from(c: char) -> Self {
        Self {
            tag: ExprTag::Char,
            raw: RawPtr::Index(u32::from(c) as usize),
            _f: Default::default(),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ContPtr<F: LurkField> {
    pub tag: ContTag,
    pub raw: RawPtr,
    pub _f: PhantomData<F>,
}

#[allow(clippy::derived_hash_with_manual_eq)]
impl<F: LurkField> Hash for ContPtr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.tag.hash(state);
        self.raw.hash(state);
    }
}

impl<F: LurkField> ContPtr<F> {
    pub fn new(tag: ContTag, raw: RawPtr) -> Self {
        Self {
            tag,
            raw,
            _f: Default::default(),
        }
    }
    pub const fn is_error(&self) -> bool {
        matches!(self.tag, ContTag::Error)
    }

    pub fn index(tag: ContTag, idx: usize) -> Self {
        ContPtr {
            tag,
            raw: RawPtr::Index(idx),
            _f: Default::default(),
        }
    }

    pub fn opaque(tag: ContTag, idx: usize) -> Self {
        ContPtr {
            tag,
            raw: RawPtr::Index(idx),
            _f: Default::default(),
        }
    }

    pub fn null(tag: ContTag) -> Self {
        ContPtr {
            tag,
            raw: RawPtr::Null,
            _f: Default::default(),
        }
    }
}
