use match_opt::match_opt;
use serde::{Deserialize, Serialize};

use crate::{
    field::{FWrap, LurkField},
    tag::{
        ExprTag::{Cons, Fun, Nil, Num, Str, Sym},
        Tag as TagTrait,
    },
};

use super::Tag;

/// An ergonomic pair type for tagged pointer semantics
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct GPtr<T, V> {
    pub tag: T,
    pub val: V,
}

impl<T, V> GPtr<T, V> {
    #[inline]
    pub fn new(tag: T, val: V) -> Self {
        Self { tag, val }
    }

    #[inline]
    pub fn tag(&self) -> &T {
        &self.tag
    }

    #[inline]
    pub fn val(&self) -> &V {
        &self.val
    }

    #[inline]
    pub fn parts(&self) -> (&T, &V) {
        let Self { tag, val } = self;
        (tag, val)
    }

    #[inline]
    pub fn into_parts(self) -> (T, V) {
        let Self { tag, val } = self;
        (tag, val)
    }
}

/// Encoding for pointer children that are stored in index-based data structures
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IVal {
    /// Holds the index of leaf data
    Atom(usize),
    /// Holds the index of two children
    Tuple2(usize),
    /// Holds the index of three children
    Tuple3(usize),
    /// Holds the index of four children
    Tuple4(usize),
    /// Similar to `Tuple3`, but ignores the tags of the first and third children
    /// for content-addressing
    Compact(usize),
}

impl IVal {
    #[inline]
    pub fn is_atom(&self) -> bool {
        matches!(self, IVal::Atom(_))
    }

    #[inline]
    pub fn is_compound(&self) -> bool {
        !self.is_atom()
    }

    #[inline]
    pub fn get_atom_idx(&self) -> Option<usize> {
        match_opt!(self, IVal::Atom(idx) => *idx)
    }

    #[inline]
    pub fn get_tuple2_idx(&self) -> Option<usize> {
        match_opt!(self, IVal::Tuple2(idx) => *idx)
    }

    #[inline]
    pub fn get_tuple3_idx(&self) -> Option<usize> {
        match_opt!(self, IVal::Tuple3(idx) => *idx)
    }

    #[inline]
    pub fn get_tuple4_idx(&self) -> Option<usize> {
        match_opt!(self, IVal::Tuple4(idx) => *idx)
    }

    #[inline]
    pub fn get_compact_idx(&self) -> Option<usize> {
        match_opt!(self, IVal::Compact(idx) => *idx)
    }
}

/// A `GPtr` that is generic on the `tag` type and uses `IVal` as the `val` type
pub type IPtr<T> = GPtr<T, IVal>;

/// Specialization of `IPtr` that uses LEM tags
pub type Ptr = IPtr<Tag>;

impl Ptr {
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
    pub fn is_cons(&self) -> bool {
        self.has_tag(&Tag::Expr(Cons))
    }

    #[inline]
    pub fn is_list(&self) -> bool {
        self.has_tag_in(&[Tag::Expr(Cons), Tag::Expr(Nil)])
    }

    #[inline]
    pub fn cast(self, tag: Tag) -> Self {
        Ptr { tag, val: self.val }
    }

    #[inline]
    pub fn get_atom_idx(&self) -> Option<usize> {
        self.val().get_atom_idx()
    }

    #[inline]
    pub fn get_tuple2_idx(&self) -> Option<usize> {
        self.val().get_tuple2_idx()
    }

    #[inline]
    pub fn get_tuple3_idx(&self) -> Option<usize> {
        self.val().get_tuple3_idx()
    }

    #[inline]
    pub fn get_tuple4_idx(&self) -> Option<usize> {
        self.val().get_tuple4_idx()
    }

    #[inline]
    pub fn atom(tag: Tag, idx: usize) -> Ptr {
        Ptr {
            tag,
            val: IVal::Atom(idx),
        }
    }
}

/// A `ZPtr` is the content-addressed representation of a `Ptr` that is used to
/// uniquely identify arbitrary DAGs with raw field elements (modulo unlikely
/// hash collisions).
///
/// In principle, `ZPtr`s could be used in place of `Ptr`, but it is important to
/// note that content-addressing can be expensive, especially in the context of
/// interpretation, because of the Poseidon hashes. That's why we operate on `Ptr`s
/// when interpreting LEMs and delay the need for `ZPtr`s as much as possible.
pub type ZPtr<F> = GPtr<Tag, FWrap<F>>;

impl<F: LurkField> ZPtr<F> {
    #[inline]
    pub fn dummy() -> Self {
        GPtr::new(Tag::Expr(Nil), FWrap(F::ZERO))
    }

    #[inline]
    pub fn hash(&self) -> &F {
        self.val().get()
    }

    #[inline]
    pub fn from_parts(tag: Tag, hash: F) -> Self {
        Self::new(tag, FWrap(hash))
    }
}

impl<T: TagTrait, F: LurkField> GPtr<T, FWrap<F>> {
    #[inline]
    pub fn tag_field(&self) -> F {
        self.tag().to_field()
    }
}
