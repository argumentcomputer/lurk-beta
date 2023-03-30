use anyhow::anyhow;
use generic_array::typenum::{U3, U4, U6, U8};
use neptune::Poseidon;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;
use rayon::prelude::*;
use std::collections::VecDeque;
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use std::sync::Arc;
use std::{fmt, marker::PhantomData};
use string_interner::symbol::{Symbol, SymbolUsize};
use thiserror;

use neptune::poseidon::PoseidonConstants;
use once_cell::sync::OnceCell;
#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;

use libipld::Cid;
use libipld::Multihash;

use crate::light_data::Encodable;
use crate::light_data::LightData;

use crate::field::{FWrap, LurkField};
use crate::package::{Package, LURK_EXTERNAL_SYMBOL_NAMES};
use crate::parser::{convert_sym_case, names_keyword};
use crate::scalar_store::{ScalarContinuation, ScalarExpression, ScalarStore};
use crate::sym::Sym;
use crate::tag::{ContTag, ExprTag, Op1, Op2, Tag};
use crate::{Num, UInt};

use serde::Deserialize;
use serde::Serialize;
use serde::{de, ser};

pub enum HashArity {
    A3,
    A4,
    A6,
    A8,
}

impl From<usize> for HashArity {
    fn from(n: usize) -> Self {
        match n {
            3 => Self::A3,
            4 => Self::A4,
            6 => Self::A6,
            8 => Self::A8,
            _ => panic!("unsupported arity: {}", n),
        }
    }
}

pub enum HashConst<'a, F: LurkField> {
    A3(&'a PoseidonConstants<F, U3>),
    A4(&'a PoseidonConstants<F, U4>),
    A6(&'a PoseidonConstants<F, U6>),
    A8(&'a PoseidonConstants<F, U8>),
}

/// Holds the constants needed for poseidon hashing.
#[derive(Debug)]
pub(crate) struct HashConstants<F: LurkField> {
    c3: OnceCell<PoseidonConstants<F, U3>>,
    c4: OnceCell<PoseidonConstants<F, U4>>,
    c6: OnceCell<PoseidonConstants<F, U6>>,
    c8: OnceCell<PoseidonConstants<F, U8>>,
}

impl<F: LurkField> Default for HashConstants<F> {
    fn default() -> Self {
        Self {
            c3: OnceCell::new(),
            c4: OnceCell::new(),
            c6: OnceCell::new(),
            c8: OnceCell::new(),
        }
    }
}

impl<F: LurkField> HashConstants<F> {
    pub fn c3(&self) -> &PoseidonConstants<F, U3> {
        self.c3.get_or_init(|| PoseidonConstants::new())
    }

    pub fn c4(&self) -> &PoseidonConstants<F, U4> {
        self.c4.get_or_init(|| PoseidonConstants::new())
    }

    pub fn c6(&self) -> &PoseidonConstants<F, U6> {
        self.c6.get_or_init(|| PoseidonConstants::new())
    }

    pub fn c8(&self) -> &PoseidonConstants<F, U8> {
        self.c8.get_or_init(|| PoseidonConstants::new())
    }

    pub fn constants(&self, arity: HashArity) -> HashConst<F> {
        match arity {
            HashArity::A3 => HashConst::A3(self.c3.get_or_init(|| PoseidonConstants::new())),
            HashArity::A4 => HashConst::A4(self.c4.get_or_init(|| PoseidonConstants::new())),
            HashArity::A6 => HashConst::A6(self.c6.get_or_init(|| PoseidonConstants::new())),
            HashArity::A8 => HashConst::A8(self.c8.get_or_init(|| PoseidonConstants::new())),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum HashScalar {
    Create,
    Get,
}

type IndexSet<K> = indexmap::IndexSet<K, ahash::RandomState>;

#[derive(Debug)]
struct StringSet(
    string_interner::StringInterner<
        string_interner::backend::BufferBackend<SymbolUsize>,
        ahash::RandomState,
    >,
);

impl Default for StringSet {
    fn default() -> Self {
        StringSet(string_interner::StringInterner::new())
    }
}

#[derive(Debug)]
pub struct Store<F: LurkField> {
    pub(crate) cons_store: IndexSet<(Ptr<F>, Ptr<F>)>,
    pub(crate) comm_store: IndexSet<(FWrap<F>, Ptr<F>)>,

    fun_store: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>)>,

    sym_store: StringSet,

    // Other sparse storage format without hashing is likely more efficient
    pub(crate) num_store: IndexSet<Num<F>>,

    str_store: StringSet,
    thunk_store: IndexSet<Thunk<F>>,
    call0_store: IndexSet<(Ptr<F>, ContPtr<F>)>,
    call_store: IndexSet<(Ptr<F>, Ptr<F>, ContPtr<F>)>,
    call2_store: IndexSet<(Ptr<F>, Ptr<F>, ContPtr<F>)>,
    tail_store: IndexSet<(Ptr<F>, ContPtr<F>)>,
    lookup_store: IndexSet<(Ptr<F>, ContPtr<F>)>,
    unop_store: IndexSet<(Op1, ContPtr<F>)>,
    binop_store: IndexSet<(Op2, Ptr<F>, Ptr<F>, ContPtr<F>)>,
    binop2_store: IndexSet<(Op2, Ptr<F>, ContPtr<F>)>,
    if_store: IndexSet<(Ptr<F>, ContPtr<F>)>,
    let_store: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>, ContPtr<F>)>,
    letrec_store: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>, ContPtr<F>)>,
    emit_store: IndexSet<ContPtr<F>>,

    opaque_map: dashmap::DashMap<Ptr<F>, ScalarPtr<F>>,
    /// Holds a mapping of ScalarPtr -> Ptr for reverse lookups
    pub(crate) scalar_ptr_map: dashmap::DashMap<ScalarPtr<F>, Ptr<F>, ahash::RandomState>,
    /// Holds a mapping of ScalarPtr -> ContPtr<F> for reverse lookups
    scalar_ptr_cont_map: dashmap::DashMap<ScalarContPtr<F>, ContPtr<F>, ahash::RandomState>,

    /// Caches poseidon hashes
    poseidon_cache: PoseidonCache<F>,
    /// Contains Ptrs which have not yet been hydrated.
    dehydrated: Vec<Ptr<F>>,
    dehydrated_cont: Vec<ContPtr<F>>,
    opaque_raw_ptr_count: usize,

    pointer_scalar_ptr_cache: dashmap::DashMap<Ptr<F>, ScalarPtr<F>>,

    pub(crate) lurk_package: Arc<Package>,
    constants: OnceCell<NamedConstants<F>>,
}

#[derive(Default, Debug)]
struct PoseidonCache<F: LurkField> {
    a3: dashmap::DashMap<CacheKey<F, 3>, F, ahash::RandomState>,
    a4: dashmap::DashMap<CacheKey<F, 4>, F, ahash::RandomState>,
    a6: dashmap::DashMap<CacheKey<F, 6>, F, ahash::RandomState>,
    a8: dashmap::DashMap<CacheKey<F, 8>, F, ahash::RandomState>,

    constants: HashConstants<F>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct CacheKey<F: LurkField, const N: usize>([F; N]);

#[allow(clippy::derive_hash_xor_eq)]
impl<F: LurkField, const N: usize> Hash for CacheKey<F, N> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for el in &self.0 {
            el.to_repr().as_ref().hash(state);
        }
    }
}

impl<F: LurkField> PoseidonCache<F> {
    fn hash3(&self, preimage: &[F; 3]) -> F {
        let hash = self
            .a3
            .entry(CacheKey(*preimage))
            .or_insert_with(|| Poseidon::new_with_preimage(preimage, self.constants.c3()).hash());

        *hash
    }

    fn hash4(&self, preimage: &[F; 4]) -> F {
        let hash = self
            .a4
            .entry(CacheKey(*preimage))
            .or_insert_with(|| Poseidon::new_with_preimage(preimage, self.constants.c4()).hash());

        *hash
    }

    fn hash6(&self, preimage: &[F; 6]) -> F {
        let hash = self
            .a6
            .entry(CacheKey(*preimage))
            .or_insert_with(|| Poseidon::new_with_preimage(preimage, self.constants.c6()).hash());
        *hash
    }

    fn hash8(&self, preimage: &[F; 8]) -> F {
        let hash = self
            .a8
            .entry(CacheKey(*preimage))
            .or_insert_with(|| Poseidon::new_with_preimage(preimage, self.constants.c8()).hash());
        *hash
    }
}

pub trait Object<F: LurkField>: fmt::Debug + Clone + PartialEq {
    type Pointer: Pointer<F>;
}

pub trait Pointer<F: LurkField + From<u64>>: fmt::Debug + Copy + Clone + PartialEq + Hash {
    type Tag: Tag;

    fn tag(&self) -> Self::Tag;
    fn tag_field(&self) -> F {
        F::from(self.tag().into() as u64)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Ptr<F: LurkField>(ExprTag, RawPtr<F>);

#[allow(clippy::derive_hash_xor_eq)]
impl<F: LurkField> Hash for Ptr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}

impl<F: LurkField> Ptr<F> {
    // TODO: Make these methods and the similar ones defined on expression consistent, probably including a shared trait.

    // NOTE: Although this could be a type predicate now, when NIL becomes a symbol, it won't be possible.
    pub const fn is_nil(&self) -> bool {
        matches!(self.0, ExprTag::Nil)
        // FIXME: check value also, probably
    }
    pub const fn is_cons(&self) -> bool {
        matches!(self.0, ExprTag::Cons)
    }

    pub const fn is_atom(&self) -> bool {
        !self.is_cons()
    }

    pub const fn is_list(&self) -> bool {
        matches!(self.0, ExprTag::Nil | ExprTag::Cons)
    }

    pub const fn is_opaque(&self) -> bool {
        self.1.is_opaque()
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
}

impl<F: LurkField> From<char> for Ptr<F> {
    fn from(c: char) -> Self {
        Self(ExprTag::Char, RawPtr::new(u32::from(c) as usize))
    }
}

impl<F: LurkField> Pointer<F> for Ptr<F> {
    type Tag = ExprTag;

    fn tag(&self) -> ExprTag {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
// Note: the trait bound E: Tag is not necessary in the struct, but it makes the proptest strategy more efficient.
/// A struct representing a scalar pointer with a tag and a value.
///
/// The `SPtr` struct is used to store a tagged scalar pointer, where `E` is its tag, and `F` the field for its values.
/// It has two important aliases, `ScalarPtr` and `ScalarContPtr`, which are used respectively with `ExprTag` and `ContTag`,
/// i.e. the type of expressions and the type of continuations.
pub struct SPtr<E: Tag, F: LurkField>(
    E,
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(strategy = "any::<FWrap<F>>().prop_map(|x| x.0)")
    )]
    F,
);

impl<E: Tag + Display, F: LurkField> Display for SPtr<E, F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let tag = self.0;
        let trimmed_f = self.1.trimmed_hex_digits();
        write!(f, "(ptr->{tag}, {trimmed_f})",)
    }
}

impl<E: Tag, F: LurkField> PartialOrd for SPtr<E, F> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        (
            self.0.to_field_bytes::<F>().as_ref(),
            self.1.to_repr().as_ref(),
        )
            .partial_cmp(&(
                other.0.to_field_bytes::<F>().as_ref(),
                other.1.to_repr().as_ref(),
            ))
    }
}

impl<E: Tag, F: LurkField> Ord for SPtr<E, F> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.partial_cmp(other)
            .expect("SPtr::cmp: partial_cmp domain invariant violation")
    }
}

impl<E: Tag, F: LurkField> Encodable for SPtr<E, F> {
    fn ser(&self) -> LightData {
        let (x, y): (FWrap<F>, FWrap<F>) = (FWrap(self.0.to_field()), FWrap(self.1));
        (x, y).ser()
    }
    fn de(ld: &LightData) -> anyhow::Result<Self> {
        let (x, y): (FWrap<F>, FWrap<F>) = Encodable::de(ld)?;
        let tag_as_u16 =
            x.0.to_u16()
                .ok_or_else(|| anyhow!("invalid range for field element representing a tag"))?;
        let tag = E::try_from(tag_as_u16).map_err(|_| anyhow!("invalid tag"))?;
        Ok(SPtr(tag, y.0))
    }
}

#[allow(clippy::derive_hash_xor_eq)]
impl<E: Tag, F: LurkField> Hash for SPtr<E, F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_field_bytes::<F>().as_ref().hash(state);
        self.1.to_repr().as_ref().hash(state);
    }
}

impl<E: Tag, F: LurkField> SPtr<E, F> {
    pub fn from_parts(tag: E, value: F) -> Self {
        SPtr(tag, value)
    }

    pub fn tag(&self) -> E {
        self.0
    }

    pub fn tag_field(&self) -> F {
        self.0.to_field::<F>()
    }

    pub fn value(&self) -> &F {
        &self.1
    }
}

impl<E: Tag, F: LurkField> Serialize for SPtr<E, F> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use ser::Error;
        let tag = self.tag_field();
        let val = self.value();
        // magic numbers to avoid multicodec table collisons
        // this will disappear when we move from IPLD to LDON
        let codec: u64 = 0x10de << 48 | tag.to_u64_unchecked();
        let hash = Multihash::wrap(codec, &val.to_bytes())
            .map_err(|_| S::Error::custom("expected validly tagged ScalarPtr".to_string()))?;
        let cid = Cid::new_v1(codec, hash);
        cid.serialize(serializer)
    }
}

impl<'de, E: Tag, F: LurkField> Deserialize<'de> for SPtr<E, F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use de::Error;
        let cid = Cid::deserialize(deserializer)?;
        let tag = F::from_u64(cid.codec() & 0x0000_0000_ffff_ffff);
        let val = F::from_bytes(cid.hash().digest())
            .ok_or_else(|| D::Error::custom("expected ScalarContPtr value".to_string()))?;
        // TODO(fga): eliminate this round-trip through the field
        let e_tag = E::from_field(&tag).ok_or_else(|| D::Error::custom("invalid Tag"))?;
        Ok(SPtr::from_parts(e_tag, val))
    }
}

pub type ScalarPtr<F> = SPtr<ExprTag, F>;

pub trait IntoHashComponents<F: LurkField> {
    fn into_hash_components(self) -> [F; 2];
}

impl<F: LurkField> IntoHashComponents<F> for [F; 2] {
    fn into_hash_components(self) -> [F; 2] {
        self
    }
}

impl<E: Tag, F: LurkField> IntoHashComponents<F> for SPtr<E, F> {
    fn into_hash_components(self) -> [F; 2] {
        [self.0.to_field::<F>(), self.1]
    }
}

pub type ScalarContPtr<F> = SPtr<ContTag, F>;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ContPtr<F: LurkField>(ContTag, RawPtr<F>);

#[allow(clippy::derive_hash_xor_eq)]
impl<F: LurkField> Hash for ContPtr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}

impl<F: LurkField> Pointer<F> for ContPtr<F> {
    type Tag = ContTag;

    fn tag(&self) -> Self::Tag {
        self.0
    }
}

impl<F: LurkField> ContPtr<F> {
    pub const fn new(tag: ContTag, raw_ptr: RawPtr<F>) -> Self {
        Self(tag, raw_ptr)
    }
    pub const fn is_error(&self) -> bool {
        matches!(self.0, ContTag::Error)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
// If .0 is negative, RawPtr is opaque. This lets us retain the efficiency and structure of the current implementation.
// It cuts the local store's address space in half, which is likely not an issue. This representation does not affect
// external data, so if we want to change it in the future, we can do so without a change of defined behavior.
pub struct RawPtr<F: LurkField>((usize, bool), PhantomData<F>);

impl<F: LurkField> RawPtr<F> {
    fn new(p: usize) -> Self {
        RawPtr((p, false), Default::default())
    }

    const fn is_opaque(&self) -> bool {
        self.0 .1
    }

    pub const fn idx(&self) -> usize {
        self.0 .0
    }
}

#[allow(clippy::derive_hash_xor_eq)]
impl<F: LurkField> Hash for RawPtr<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

// Expressions, Continuations, Op1, Op2 occupy the same namespace in
// their encoding.
// As a 16bit integer their representation is as follows
//    [typ] [value       ]
// 0b 0000_ 0000_0000_0000
//
// where typ is
// - `0b0000` for ExprTag
// - `0b0001` for ContTag
// - `0b0010` for Op1
// - `0b0011` for Op2

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expression<'a, F: LurkField> {
    Nil,
    Cons(Ptr<F>, Ptr<F>),
    Comm(F, Ptr<F>),
    Sym(Sym),
    /// arg, body, closed env
    Fun(Ptr<F>, Ptr<F>, Ptr<F>),
    Num(Num<F>),
    Str(&'a str),
    Thunk(Thunk<F>),
    Opaque(Ptr<F>),
    Char(char),
    UInt(UInt),
}

impl<F: LurkField> Object<F> for Expression<'_, F> {
    type Pointer = Ptr<F>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Thunk<F: LurkField> {
    pub(crate) value: Ptr<F>,
    pub(crate) continuation: ContPtr<F>,
}

#[allow(clippy::derive_hash_xor_eq)]
impl<F: LurkField> Hash for Thunk<F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state);
        self.continuation.hash(state);
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Continuation<F: LurkField> {
    Outermost,
    Call0 {
        saved_env: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Call {
        unevaled_arg: Ptr<F>,
        saved_env: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Call2 {
        function: Ptr<F>,
        saved_env: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Tail {
        saved_env: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Error,
    Lookup {
        saved_env: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Unop {
        operator: Op1,
        continuation: ContPtr<F>,
    },
    Binop {
        operator: Op2,
        saved_env: Ptr<F>,
        unevaled_args: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Binop2 {
        operator: Op2,
        evaled_arg: Ptr<F>,
        continuation: ContPtr<F>,
    },
    If {
        unevaled_args: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Let {
        var: Ptr<F>,
        body: Ptr<F>,
        saved_env: Ptr<F>,
        continuation: ContPtr<F>,
    },
    LetRec {
        var: Ptr<F>,
        saved_env: Ptr<F>,
        body: Ptr<F>,
        continuation: ContPtr<F>,
    },
    Emit {
        continuation: ContPtr<F>,
    },
    Dummy,
    Terminal,
}

impl<F: LurkField> Object<F> for Continuation<F> {
    type Pointer = ContPtr<F>;
}

impl<F: LurkField> Continuation<F> {
    pub(crate) fn intern_aux(&self, store: &mut Store<F>) -> ContPtr<F> {
        match self {
            Self::Outermost | Self::Dummy | Self::Error | Self::Terminal => {
                let cont_ptr = self.get_simple_cont();
                store.mark_dehydrated_cont(cont_ptr);
                cont_ptr
            }
            _ => {
                let (p, inserted) = self.insert_in_store(store);
                let ptr = ContPtr(self.cont_tag(), RawPtr::new(p));
                if inserted {
                    store.dehydrated_cont.push(ptr)
                }
                ptr
            }
        }
    }
    pub fn insert_in_store(&self, store: &mut Store<F>) -> (usize, bool) {
        match self {
            Self::Outermost | Self::Dummy | Self::Error | Self::Terminal => (0, false),
            Self::Call0 {
                saved_env,
                continuation,
            } => store.call0_store.insert_full((*saved_env, *continuation)),
            Self::Call {
                unevaled_arg,
                saved_env,
                continuation,
            } => store
                .call_store
                .insert_full((*unevaled_arg, *saved_env, *continuation)),
            Self::Call2 {
                function,
                saved_env,
                continuation,
            } => store
                .call2_store
                .insert_full((*function, *saved_env, *continuation)),
            Self::Tail {
                saved_env,
                continuation,
            } => store.tail_store.insert_full((*saved_env, *continuation)),
            Self::Lookup {
                saved_env,
                continuation,
            } => store.lookup_store.insert_full((*saved_env, *continuation)),
            Self::Unop {
                operator,
                continuation,
            } => store.unop_store.insert_full((*operator, *continuation)),
            Self::Binop {
                operator,
                saved_env,
                unevaled_args,
                continuation,
            } => store.binop_store.insert_full((
                *operator,
                *saved_env,
                *unevaled_args,
                *continuation,
            )),
            Self::Binop2 {
                operator,
                evaled_arg,
                continuation,
            } => store
                .binop2_store
                .insert_full((*operator, *evaled_arg, *continuation)),
            Self::If {
                unevaled_args,
                continuation,
            } => store.if_store.insert_full((*unevaled_args, *continuation)),
            Self::Let {
                var,
                body,
                saved_env,
                continuation,
            } => store
                .let_store
                .insert_full((*var, *body, *saved_env, *continuation)),
            Self::LetRec {
                var,
                body,
                saved_env,
                continuation,
            } => store
                .letrec_store
                .insert_full((*var, *body, *saved_env, *continuation)),
            Self::Emit { continuation } => store.emit_store.insert_full(*continuation),
        }
    }

    pub const fn cont_tag(&self) -> ContTag {
        match self {
            Self::Outermost => ContTag::Outermost,
            Self::Dummy => ContTag::Dummy,
            Self::Error => ContTag::Error,
            Self::Terminal => ContTag::Terminal,
            Self::Call0 {
                saved_env: _,
                continuation: _,
            } => ContTag::Call0,
            Self::Call {
                unevaled_arg: _,
                saved_env: _,
                continuation: _,
            } => ContTag::Call,
            Self::Call2 {
                function: _,
                saved_env: _,
                continuation: _,
            } => ContTag::Call2,
            Self::Tail {
                saved_env: _,
                continuation: _,
            } => ContTag::Tail,
            Self::Lookup {
                saved_env: _,
                continuation: _,
            } => ContTag::Lookup,
            Self::Unop {
                operator: _,
                continuation: _,
            } => ContTag::Unop,
            Self::Binop {
                operator: _,
                saved_env: _,
                unevaled_args: _,
                continuation: _,
            } => ContTag::Binop,
            Self::Binop2 {
                operator: _,
                evaled_arg: _,
                continuation: _,
            } => ContTag::Binop2,
            Self::If {
                unevaled_args: _,
                continuation: _,
            } => ContTag::If,
            Self::Let {
                var: _,
                body: _,
                saved_env: _,
                continuation: _,
            } => ContTag::Let,
            Self::LetRec {
                var: _,
                body: _,
                saved_env: _,
                continuation: _,
            } => ContTag::LetRec,
            Self::Emit { continuation: _ } => ContTag::Emit,
        }
    }
    pub fn get_simple_cont(&self) -> ContPtr<F> {
        match self {
            Self::Outermost | Self::Dummy | Self::Error | Self::Terminal => {
                ContPtr(self.cont_tag(), RawPtr::new(0))
            }

            _ => unreachable!("Not a simple Continuation: {:?}", self),
        }
    }
}

pub trait TypePredicates {
    fn is_fun(&self) -> bool;
    fn is_self_evaluating(&self) -> bool;
    fn is_potentially(&self, tag: ExprTag) -> bool;
}

impl<F: LurkField> TypePredicates for Ptr<F> {
    fn is_fun(&self) -> bool {
        self.tag().is_fun()
    }
    fn is_self_evaluating(&self) -> bool {
        self.tag().is_self_evaluating()
    }
    fn is_potentially(&self, tag: ExprTag) -> bool {
        self.tag().is_potentially(tag)
    }
}

impl<F: LurkField> Default for Store<F> {
    fn default() -> Self {
        let mut store = Store {
            cons_store: Default::default(),
            comm_store: Default::default(),
            sym_store: Default::default(),
            num_store: Default::default(),
            fun_store: Default::default(),
            str_store: Default::default(),
            thunk_store: Default::default(),
            call0_store: Default::default(),
            call_store: Default::default(),
            call2_store: Default::default(),
            tail_store: Default::default(),
            lookup_store: Default::default(),
            unop_store: Default::default(),
            binop_store: Default::default(),
            binop2_store: Default::default(),
            if_store: Default::default(),
            let_store: Default::default(),
            letrec_store: Default::default(),
            emit_store: Default::default(),
            opaque_map: Default::default(),
            scalar_ptr_map: Default::default(),
            scalar_ptr_cont_map: Default::default(),
            poseidon_cache: Default::default(),
            dehydrated: Default::default(),
            dehydrated_cont: Default::default(),
            opaque_raw_ptr_count: 0,
            pointer_scalar_ptr_cache: Default::default(),
            lurk_package: Arc::new(Package::lurk()),
            constants: Default::default(),
        };

        store.lurk_sym("");

        for name in LURK_EXTERNAL_SYMBOL_NAMES {
            store.lurk_sym(name);
        }

        {
            // Intern the root symbol.
            let sym = Sym::root();
            store.intern_sym(&sym);
        }

        store
    }
}

#[derive(thiserror::Error, Debug, Clone)]
pub struct Error(pub String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "StoreError: {}", self.0)
    }
}

/// These methods provide a more ergonomic means of constructing and manipulating Lurk data.
/// They can be thought of as a minimal DSL for working with Lurk data in Rust code.
/// Prefer these methods when constructing literal data or assembling program fragments in
/// tests or during evaluation, etc.
impl<F: LurkField> Store<F> {
    pub fn nil(&mut self) -> Ptr<F> {
        self.intern_nil()
    }

    pub fn t(&mut self) -> Ptr<F> {
        self.lurk_sym("T")
    }

    pub fn cons(&mut self, car: Ptr<F>, cdr: Ptr<F>) -> Ptr<F> {
        self.intern_cons(car, cdr)
    }
    pub fn strcons(&mut self, car: Ptr<F>, cdr: Ptr<F>) -> Ptr<F> {
        self.intern_strcons(car, cdr)
    }

    pub fn hidden(&self, secret: F, payload: Ptr<F>) -> Option<Ptr<F>> {
        self.comm_store
            .get_index_of(&(FWrap(secret), payload))
            .map(|c| Ptr(ExprTag::Comm, RawPtr::new(c)))
    }

    pub fn hide(&mut self, secret: F, payload: Ptr<F>) -> Ptr<F> {
        self.intern_comm(secret, payload)
    }

    pub fn open(&self, ptr: Ptr<F>) -> Option<(F, Ptr<F>)> {
        let p = match ptr.0 {
            ExprTag::Comm => ptr,
            ExprTag::Num => {
                let scalar = self.fetch_num(&ptr).map(|x| x.into_scalar()).unwrap();
                match self.get_maybe_opaque(ExprTag::Comm, scalar) {
                    Some(c) => c,
                    None => {
                        panic!("Can't find commitment in the store.")
                    }
                }
            }
            _ => return None,
        };

        if let Some((secret, payload)) = self.fetch_comm(&p) {
            Some((secret.0, *payload))
        } else {
            None
        }
    }

    pub fn open_mut(&mut self, ptr: Ptr<F>) -> Result<(F, Ptr<F>), Error> {
        let p = match ptr.0 {
            ExprTag::Comm => ptr,
            ExprTag::Num => {
                let scalar = self.fetch_num(&ptr).map(|x| x.into_scalar()).unwrap();

                self.intern_maybe_opaque_comm(scalar)
            }
            _ => return Err(Error("wrong type for commitment specifier".into())),
        };

        if let Some((secret, payload)) = self.fetch_comm(&p) {
            Ok((secret.0, *payload))
        } else {
            Err(Error("hidden value could not be opened".into()))
        }
    }

    pub fn secret(&self, ptr: Ptr<F>) -> Option<Ptr<F>> {
        let p = match ptr.0 {
            ExprTag::Comm => ptr,
            _ => return None,
        };

        self.fetch_comm(&p)
            .and_then(|(secret, _payload)| self.get_num(Num::Scalar(secret.0)))
    }

    pub fn secret_mut(&mut self, ptr: Ptr<F>) -> Result<Ptr<F>, Error> {
        let p = match ptr.0 {
            ExprTag::Comm => ptr,
            _ => return Err(Error("wrong type for commitment specifier".into())),
        };

        if let Some((secret, _payload)) = self.fetch_comm(&p) {
            let secret_element = Num::Scalar(secret.0);
            let secret_num = self.intern_num(secret_element);
            Ok(secret_num)
        } else {
            Err(Error("secret could not be extracted".into()))
        }
    }

    pub fn list(&mut self, elts: &[Ptr<F>]) -> Ptr<F> {
        self.intern_list(elts)
    }

    pub fn num<T: Into<Num<F>>>(&mut self, num: T) -> Ptr<F> {
        self.intern_num(num)
    }

    pub fn uint64(&mut self, n: u64) -> Ptr<F> {
        self.get_u64(n)
    }

    pub fn str<T: AsRef<str>>(&mut self, name: T) -> Ptr<F> {
        self.intern_str(name)
    }

    pub fn lurk_sym<T: AsRef<str>>(&mut self, name: T) -> Ptr<F> {
        let package = self.lurk_package.clone();

        self.intern_sym_with_case_conversion(name, &package)
    }

    pub fn sym<T: AsRef<str>>(&mut self, name: T) -> Ptr<F> {
        let package = Default::default();
        self.intern_sym_with_case_conversion(name, &package)
    }

    pub fn key<T: AsRef<str>>(&mut self, name: T) -> Ptr<F> {
        self.root_sym(name, true)
    }

    pub fn root_sym<T: AsRef<str>>(&mut self, name: T, is_keyword: bool) -> Ptr<F> {
        assert!(!name.as_ref().starts_with(':'));
        assert!(!name.as_ref().starts_with('.'));
        let package = Package::root();

        let name = if is_keyword {
            format!(":{}", name.as_ref())
        } else {
            name.as_ref().into()
        };
        self.intern_sym_with_case_conversion(name, &package)
    }

    pub fn car(&self, expr: &Ptr<F>) -> Result<Ptr<F>, Error> {
        Ok(self.car_cdr(expr)?.0)
    }

    pub fn cdr(&self, expr: &Ptr<F>) -> Result<Ptr<F>, Error> {
        Ok(self.car_cdr(expr)?.1)
    }

    pub(crate) const fn poseidon_constants(&self) -> &HashConstants<F> {
        &self.poseidon_cache.constants
    }

    pub fn new() -> Self {
        Store::default()
    }

    pub fn intern_nil(&mut self) -> Ptr<F> {
        self.lurk_sym("nil")
    }

    pub fn get_nil(&self) -> Ptr<F> {
        self.get_lurk_sym("nil", true).expect("missing NIL")
    }

    pub fn get_begin(&self) -> Ptr<F> {
        self.get_lurk_sym("begin", true).expect("missing BEGIN")
    }

    pub fn get_quote(&self) -> Ptr<F> {
        self.get_lurk_sym("quote", true).expect("missing QUOTE")
    }

    pub fn get_t(&self) -> Ptr<F> {
        self.get_lurk_sym("t", true).expect("missing T")
    }

    pub fn intern_cons(&mut self, car: Ptr<F>, cdr: Ptr<F>) -> Ptr<F> {
        if car.is_opaque() || cdr.is_opaque() {
            self.hash_expr(&car);
            self.hash_expr(&cdr);
        }

        let (p, inserted) = self.cons_store.insert_full((car, cdr));
        let ptr = Ptr(ExprTag::Cons, RawPtr::new(p));
        if inserted {
            self.dehydrated.push(ptr);
        }
        ptr
    }

    pub fn intern_strcons(&mut self, car: Ptr<F>, cdr: Ptr<F>) -> Ptr<F> {
        if car.is_opaque() || cdr.is_opaque() {
            self.hash_expr(&car);
            self.hash_expr(&cdr);
        }
        assert_eq!((car.tag(), cdr.tag()), (ExprTag::Char, ExprTag::Str));
        let (c, s) = (
            self.fetch_char(&car).unwrap(),
            self.fetch_str(&cdr).unwrap(),
        );
        let new_str = format!("{c}{s}");

        self.intern_str(&new_str)
    }

    pub fn intern_comm(&mut self, secret: F, payload: Ptr<F>) -> Ptr<F> {
        if payload.is_opaque() {
            self.hash_expr(&payload);
        }
        let (p, inserted) = self.comm_store.insert_full((FWrap(secret), payload));

        let ptr = Ptr(ExprTag::Comm, RawPtr::new(p));

        if inserted {
            self.dehydrated.push(ptr);
        }
        ptr
    }

    // Intern a potentially-opaque value. If the corresponding value is already known to the store,
    // return the known value.
    fn intern_maybe_opaque(&mut self, tag: ExprTag, hash: F) -> Ptr<F> {
        self.intern_opaque_aux(tag, hash, true)
    }

    // Intern an opaque value. If the corresponding non-opaque value is already known to the store,
    // return an opaque one anyway.
    fn intern_opaque(&mut self, tag: ExprTag, hash: F) -> Ptr<F> {
        self.intern_opaque_aux(tag, hash, false)
    }

    pub fn get_maybe_opaque(&self, tag: ExprTag, hash: F) -> Option<Ptr<F>> {
        let scalar_ptr = ScalarPtr::from_parts(tag, hash);

        let ptr = self.scalar_ptr_map.get(&scalar_ptr);
        if let Some(p) = ptr {
            return Some(*p);
        }
        None
    }

    // Intern a potentially-opaque value. If the corresponding non-opaque value is already known to the store, and
    // `return_non_opaque_if_existing` is true, return the known value.
    fn intern_opaque_aux(
        &mut self,
        tag: ExprTag,
        hash: F,
        return_non_opaque_if_existing: bool,
    ) -> Ptr<F> {
        self.hydrate_scalar_cache();
        let scalar_ptr = ScalarPtr::from_parts(tag, hash);

        // Scope the first immutable borrow.
        {
            let ptr = self.scalar_ptr_map.get(&scalar_ptr);
            if let Some(p) = ptr {
                if return_non_opaque_if_existing || p.is_opaque() {
                    return *p;
                }
            }
        }

        let ptr = Ptr(tag, self.new_opaque_raw_ptr());
        // Always insert. Key is unique because of newly allocated opaque raw_ptr.
        self.opaque_map.insert(ptr, scalar_ptr);
        ptr
    }

    pub fn intern_scalar_cont_ptr(
        &mut self,
        ptr: ScalarContPtr<F>,
        scalar_store: &ScalarStore<F>,
    ) -> Option<ContPtr<F>> {
        use ScalarContinuation::*;
        let tag: ContTag = ptr.tag();

        if let Some(cont) = scalar_store.get_cont(&ptr) {
            let continuation = match cont {
                Outermost => Continuation::Outermost,
                Dummy => Continuation::Dummy,
                Terminal => Continuation::Terminal,
                Call {
                    unevaled_arg,
                    saved_env,
                    continuation,
                } => Continuation::Call {
                    unevaled_arg: self.intern_scalar_ptr(*unevaled_arg, scalar_store)?,
                    saved_env: self.intern_scalar_ptr(*saved_env, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },

                Call2 {
                    function,
                    saved_env,
                    continuation,
                } => Continuation::Call2 {
                    function: self.intern_scalar_ptr(*function, scalar_store)?,
                    saved_env: self.intern_scalar_ptr(*saved_env, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                Tail {
                    saved_env,
                    continuation,
                } => Continuation::Tail {
                    saved_env: self.intern_scalar_ptr(*saved_env, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                Error => Continuation::Error,
                Lookup {
                    saved_env,
                    continuation,
                } => Continuation::Lookup {
                    saved_env: self.intern_scalar_ptr(*saved_env, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                Unop {
                    operator,
                    continuation,
                } => Continuation::Unop {
                    operator: *operator,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                Binop {
                    operator,
                    saved_env,
                    unevaled_args,
                    continuation,
                } => Continuation::Binop {
                    operator: *operator,
                    saved_env: self.intern_scalar_ptr(*saved_env, scalar_store)?,
                    unevaled_args: self.intern_scalar_ptr(*unevaled_args, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                Binop2 {
                    operator,
                    evaled_arg,
                    continuation,
                } => Continuation::Binop2 {
                    operator: *operator,
                    evaled_arg: self.intern_scalar_ptr(*evaled_arg, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                If {
                    unevaled_args,
                    continuation,
                } => Continuation::If {
                    unevaled_args: self.intern_scalar_ptr(*unevaled_args, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                Let {
                    var,
                    body,
                    saved_env,
                    continuation,
                } => Continuation::Let {
                    var: self.intern_scalar_ptr(*var, scalar_store)?,
                    body: self.intern_scalar_ptr(*body, scalar_store)?,
                    saved_env: self.intern_scalar_ptr(*saved_env, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                LetRec {
                    var,
                    body,
                    saved_env,
                    continuation,
                } => Continuation::LetRec {
                    var: self.intern_scalar_ptr(*var, scalar_store)?,
                    body: self.intern_scalar_ptr(*body, scalar_store)?,
                    saved_env: self.intern_scalar_ptr(*saved_env, scalar_store)?,
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
                Emit { continuation } => Continuation::Emit {
                    continuation: self.intern_scalar_cont_ptr(*continuation, scalar_store)?,
                },
            };

            if continuation.cont_tag() == tag {
                Some(continuation.intern_aux(self))
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn intern_scalar_ptr(
        &mut self,
        ptr: ScalarPtr<F>,
        scalar_store: &ScalarStore<F>,
    ) -> Option<Ptr<F>> {
        let tag: ExprTag = ptr.tag();
        let expr = scalar_store.get_expr(&ptr);
        use ScalarExpression::*;
        match (tag, expr) {
            (ExprTag::Nil, Some(Nil)) => Some(self.intern_nil()),
            (ExprTag::Cons, Some(Cons(car, cdr))) => {
                let car = self.intern_scalar_ptr(*car, scalar_store)?;
                let cdr = self.intern_scalar_ptr(*cdr, scalar_store)?;
                Some(self.intern_cons(car, cdr))
            }
            (ExprTag::Str, Some(Str(s))) => Some(self.intern_str(s)),
            (ExprTag::Sym, Some(Sym(s))) => Some(self.intern_sym(s)),
            (ExprTag::Key, Some(Sym(k))) => Some(self.intern_key(k)),
            (ExprTag::Num, Some(Num(x))) => Some(self.intern_num(crate::Num::Scalar(*x))),
            (ExprTag::Thunk, Some(Thunk(t))) => {
                let value = self.intern_scalar_ptr(t.value, scalar_store)?;
                let continuation = self.intern_scalar_cont_ptr(t.continuation, scalar_store)?;
                Some(self.intern_thunk(crate::store::Thunk {
                    value,
                    continuation,
                }))
            }
            (
                ExprTag::Fun,
                Some(Fun {
                    arg,
                    body,
                    closed_env,
                }),
            ) => {
                let arg = self.intern_scalar_ptr(*arg, scalar_store)?;
                let body = self.intern_scalar_ptr(*body, scalar_store)?;
                let env = self.intern_scalar_ptr(*closed_env, scalar_store)?;
                Some(self.intern_fun(arg, body, env))
            }
            (tag, None) => Some(self.intern_maybe_opaque(tag, ptr.1)),
            _ => None,
        }
    }

    pub fn intern_maybe_opaque_fun(&mut self, hash: F) -> Ptr<F> {
        self.intern_maybe_opaque(ExprTag::Fun, hash)
    }

    pub fn intern_maybe_opaque_sym(&mut self, hash: F) -> Ptr<F> {
        self.intern_maybe_opaque(ExprTag::Sym, hash)
    }

    pub fn intern_maybe_opaque_cons(&mut self, hash: F) -> Ptr<F> {
        self.intern_maybe_opaque(ExprTag::Cons, hash)
    }

    pub fn intern_maybe_opaque_comm(&mut self, hash: F) -> Ptr<F> {
        self.intern_maybe_opaque(ExprTag::Comm, hash)
    }

    pub fn intern_opaque_fun(&mut self, hash: F) -> Ptr<F> {
        self.intern_opaque(ExprTag::Fun, hash)
    }

    pub fn intern_opaque_sym(&mut self, hash: F) -> Ptr<F> {
        self.intern_opaque(ExprTag::Sym, hash)
    }

    pub fn intern_opaque_cons(&mut self, hash: F) -> Ptr<F> {
        self.intern_opaque(ExprTag::Cons, hash)
    }

    pub fn intern_opaque_comm(&mut self, hash: F) -> Ptr<F> {
        self.intern_opaque(ExprTag::Comm, hash)
    }

    /// Helper to allocate a list, instead of manually using `cons`.
    pub fn intern_list(&mut self, elts: &[Ptr<F>]) -> Ptr<F> {
        elts.iter()
            .rev()
            .fold(self.lurk_sym("nil"), |acc, elt| self.intern_cons(*elt, acc))
    }

    pub fn intern_sym_with_case_conversion<T: AsRef<str>>(
        &mut self,
        name: T,
        package: &Package,
    ) -> Ptr<F> {
        let mut name = name.as_ref().to_string();
        convert_sym_case(&mut name);
        let sym = Sym::new_absolute(name);

        self.intern_sym_in_package(sym, package)
    }

    pub fn intern_sym(&mut self, sym: &Sym) -> Ptr<F> {
        let name = sym.full_name();
        self.intern_sym_by_full_name(name)
    }

    pub fn intern_key(&mut self, sym: &Sym) -> Ptr<F> {
        let name = sym.full_name();

        assert!(names_keyword(&name).0);
        self.intern_sym_by_full_name(name)
    }

    fn get_sym_by_full_name<T: AsRef<str>>(&self, name: T) -> Ptr<F> {
        let name = name.as_ref();

        let (tag, symbol_name) = if name == ".LURK.NIL" {
            (ExprTag::Nil, "LURK.NIL")
        } else {
            let (names_keyword, symbol_name) = names_keyword(name);

            if names_keyword {
                (ExprTag::Key, symbol_name)
            } else {
                (ExprTag::Sym, symbol_name)
            }
        };

        if let Some(ptr) = self.sym_store.0.get(&symbol_name) {
            Ptr(tag, RawPtr::new(ptr.to_usize()))
        } else {
            let ptr = self.sym_store.0.get(symbol_name).unwrap();
            Ptr(tag, RawPtr::new(ptr.to_usize()))
        }
    }

    fn intern_sym_by_full_name<T: AsRef<str>>(&mut self, name: T) -> Ptr<F> {
        let name = name.as_ref();
        self.hash_string_mut(name);

        let (tag, symbol_name) = if name == ".LURK.NIL" {
            (ExprTag::Nil, "LURK.NIL")
        } else {
            let (names_keyword, symbol_name) = names_keyword(name);

            if names_keyword {
                (ExprTag::Key, symbol_name)
            } else {
                (ExprTag::Sym, symbol_name)
            }
        };

        // We need to intern each of the path segments individually, so they will be in the store.
        // Otherwise, there can be an error when calling `hash_symbol()` with an immutable store.
        Sym::new_absolute(name.into()).path().iter().for_each(|x| {
            self.intern_str(x);
        });

        if let Some(ptr) = self.sym_store.0.get(&symbol_name) {
            Ptr(tag, RawPtr::new(ptr.to_usize()))
        } else {
            let ptr = self.sym_store.0.get_or_intern(symbol_name);
            let ptr = Ptr(tag, RawPtr::new(ptr.to_usize()));
            self.dehydrated.push(ptr);
            ptr
        }
    }

    pub fn get_lurk_sym<T: AsRef<str>>(&self, name: T, convert_case: bool) -> Option<Ptr<F>> {
        let mut name = format!(".lurk.{}", name.as_ref());
        if convert_case {
            crate::parser::convert_sym_case(&mut name);
        }

        Some(self.get_sym_by_full_name(name))
    }

    pub fn intern_num<T: Into<Num<F>>>(&mut self, num: T) -> Ptr<F> {
        let num = num.into();
        let num = match num {
            Num::Scalar(scalar) => {
                if let Some(u64_num) = scalar.to_u64() {
                    Num::U64(u64_num)
                } else {
                    num
                }
            }
            Num::U64(_) => num,
        };
        let (ptr, _) = self.num_store.insert_full(num);

        Ptr(ExprTag::Num, RawPtr::new(ptr))
    }

    pub fn get_num<T: Into<Num<F>>>(&self, num: T) -> Option<Ptr<F>> {
        let num = num.into();
        let num = match num {
            Num::Scalar(scalar) => {
                if let Some(u64_num) = scalar.to_u64() {
                    Num::U64(u64_num)
                } else {
                    num
                }
            }
            Num::U64(_) => num,
        };

        self.num_store
            .get_index_of::<Num<F>>(&num)
            .map(|x| Ptr(ExprTag::Num, RawPtr::new(x)))
    }

    pub fn get_char(&self, c: char) -> Ptr<F> {
        self.get_char_from_u32(u32::from(c))
    }

    pub fn get_char_from_u32(&self, code: u32) -> Ptr<F> {
        Ptr(ExprTag::Char, RawPtr::new(code as usize))
    }

    pub fn get_u64(&self, n: u64) -> Ptr<F> {
        Ptr(ExprTag::U64, RawPtr::new(n as usize))
    }

    pub fn intern_str<T: AsRef<str>>(&mut self, str: T) -> Ptr<F> {
        // Hash string for side effect. This will cause all tails to be interned.
        self.hash_string_mut(str.as_ref());
        self.intern_str_aux(str)
    }

    fn intern_str_aux<T: AsRef<str>>(&mut self, str: T) -> Ptr<F> {
        if let Some(ptr) = self.str_store.0.get(&str) {
            Ptr(ExprTag::Str, RawPtr::new(ptr.to_usize()))
        } else {
            let ptr = self.str_store.0.get_or_intern(str);
            let ptr = Ptr(ExprTag::Str, RawPtr::new(ptr.to_usize()));

            self.dehydrated.push(ptr);
            ptr
        }
    }

    pub fn get_str<T: AsRef<str>>(&self, name: T) -> Option<Ptr<F>> {
        let ptr = self.str_store.0.get(name)?;
        Some(Ptr(ExprTag::Str, RawPtr::new(ptr.to_usize())))
    }

    pub fn get_sym<T: AsRef<str>>(&self, sym: Sym) -> Option<Ptr<F>> {
        let name = sym.full_sym_name();
        let ptr = self.sym_store.0.get(name)?;
        Some(Ptr(ExprTag::Sym, RawPtr::new(ptr.to_usize())))
    }

    pub fn intern_fun(&mut self, arg: Ptr<F>, body: Ptr<F>, closed_env: Ptr<F>) -> Ptr<F> {
        // TODO: closed_env must be an env
        assert!(matches!(arg.0, ExprTag::Sym), "ARG must be a symbol");
        let (p, inserted) = self.fun_store.insert_full((arg, body, closed_env));
        let ptr = Ptr(ExprTag::Fun, RawPtr::new(p));
        if inserted {
            self.dehydrated.push(ptr);
        }
        ptr
    }

    pub fn intern_thunk(&mut self, thunk: Thunk<F>) -> Ptr<F> {
        let (p, inserted) = self.thunk_store.insert_full(thunk);
        let ptr = Ptr(ExprTag::Thunk, RawPtr::new(p));
        if inserted {
            self.dehydrated.push(ptr);
        }
        ptr
    }

    fn mark_dehydrated_cont(&mut self, p: ContPtr<F>) -> ContPtr<F> {
        self.dehydrated_cont.push(p);
        p
    }

    pub fn get_cont_outermost(&self) -> ContPtr<F> {
        Continuation::Outermost.get_simple_cont()
    }
    pub fn get_cont_error(&self) -> ContPtr<F> {
        Continuation::Error.get_simple_cont()
    }

    pub fn get_cont_terminal(&self) -> ContPtr<F> {
        Continuation::Terminal.get_simple_cont()
    }

    pub fn get_cont_dummy(&self) -> ContPtr<F> {
        Continuation::Dummy.get_simple_cont()
    }

    pub fn intern_cont_error(&mut self) -> ContPtr<F> {
        self.mark_dehydrated_cont(self.get_cont_error())
    }

    pub fn intern_cont_outermost(&mut self) -> ContPtr<F> {
        self.mark_dehydrated_cont(self.get_cont_outermost())
    }

    pub fn intern_cont_terminal(&mut self) -> ContPtr<F> {
        self.mark_dehydrated_cont(self.get_cont_terminal())
    }

    pub fn intern_cont_dummy(&mut self) -> ContPtr<F> {
        self.mark_dehydrated_cont(self.get_cont_dummy())
    }

    pub fn scalar_from_parts(&self, tag: F, value: F) -> Option<ScalarPtr<F>> {
        let Some(e_tag) = ExprTag::from_field(&tag) else { return None };
        let scalar_ptr = ScalarPtr::from_parts(e_tag, value);
        self.scalar_ptr_map
            .contains_key(&scalar_ptr)
            .then_some(scalar_ptr)
    }

    pub fn scalar_from_parts_cont(&self, tag: F, value: F) -> Option<ScalarContPtr<F>> {
        let Some(e_tag) = ContTag::from_field(&tag) else { return None };
        let scalar_ptr = ScalarContPtr::from_parts(e_tag, value);
        if self.scalar_ptr_cont_map.contains_key(&scalar_ptr) {
            return Some(scalar_ptr);
        }
        None
    }

    pub fn fetch_scalar(&self, scalar_ptr: &ScalarPtr<F>) -> Option<Ptr<F>> {
        self.scalar_ptr_map.get(scalar_ptr).map(|p| *p)
    }

    pub fn fetch_scalar_cont(&self, scalar_ptr: &ScalarContPtr<F>) -> Option<ContPtr<F>> {
        self.scalar_ptr_cont_map.get(scalar_ptr).map(|p| *p)
    }

    pub fn fetch_sym(&self, ptr: &Ptr<F>) -> Option<Sym> {
        debug_assert!(matches!(ptr.0, ExprTag::Sym | ExprTag::Key | ExprTag::Nil));

        if ptr.1.is_opaque() {
            let is_keyword = ptr.0 == ExprTag::Key;

            return Some(Sym::new_opaque(is_keyword));
        }

        if ptr.0 == ExprTag::Nil {
            return Some(Sym::new(".LURK.NIL".into()));
        };
        self.sym_store
            .0
            .resolve(SymbolUsize::try_from_usize(ptr.1.idx()).unwrap())
            .map(|s| match ptr.0 {
                ExprTag::Sym => Sym::new_sym(s.into()),
                ExprTag::Key => Sym::new_key(s.into()),
                _ => unreachable!(),
            })
    }

    pub fn fetch_str(&self, ptr: &Ptr<F>) -> Option<&str> {
        debug_assert!(matches!(ptr.0, ExprTag::Str));
        let symbol = SymbolUsize::try_from_usize(ptr.1.idx()).expect("invalid pointer");
        self.str_store.0.resolve(symbol)
    }

    pub fn fetch_char(&self, ptr: &Ptr<F>) -> Option<char> {
        debug_assert!(matches!(ptr.0, ExprTag::Char));
        char::from_u32(ptr.1 .0 .0 as u32)
    }

    pub fn fetch_fun(&self, ptr: &Ptr<F>) -> Option<&(Ptr<F>, Ptr<F>, Ptr<F>)> {
        debug_assert!(matches!(ptr.0, ExprTag::Fun));
        if ptr.1.is_opaque() {
            None
            // Some(&self.opaque_fun)
        } else {
            self.fun_store.get_index(ptr.1.idx())
        }
    }

    pub fn fetch_cons(&self, ptr: &Ptr<F>) -> Option<&(Ptr<F>, Ptr<F>)> {
        debug_assert!(matches!(ptr.0, ExprTag::Cons));
        if ptr.1.is_opaque() {
            None
        } else {
            self.cons_store.get_index(ptr.1.idx())
        }
    }

    pub fn fetch_comm(&self, ptr: &Ptr<F>) -> Option<&(FWrap<F>, Ptr<F>)> {
        debug_assert!(matches!(ptr.0, ExprTag::Comm));
        if ptr.1.is_opaque() {
            None
        } else {
            self.comm_store.get_index(ptr.1.idx())
        }
    }

    pub fn fetch_num(&self, ptr: &Ptr<F>) -> Option<&Num<F>> {
        debug_assert!(matches!(ptr.0, ExprTag::Num));
        self.num_store.get_index(ptr.1.idx())
    }

    fn fetch_thunk(&self, ptr: &Ptr<F>) -> Option<&Thunk<F>> {
        debug_assert!(matches!(ptr.0, ExprTag::Thunk));
        self.thunk_store.get_index(ptr.1.idx())
    }

    pub fn fetch_uint(&self, ptr: &Ptr<F>) -> Option<UInt> {
        // If more UInt variants are added, the following assertion should be relaxed to check for any of them.
        debug_assert!(matches!(ptr.0, ExprTag::U64));
        match ptr.0 {
            ExprTag::U64 => Some(UInt::U64(ptr.1 .0 .0 as u64)),
            _ => unreachable!(),
        }
    }

    pub fn fetch(&self, ptr: &Ptr<F>) -> Option<Expression<F>> {
        if ptr.is_opaque() {
            return Some(Expression::Opaque(*ptr));
        }
        match ptr.0 {
            ExprTag::Nil => Some(Expression::Nil),
            ExprTag::Cons => self.fetch_cons(ptr).map(|(a, b)| Expression::Cons(*a, *b)),
            ExprTag::Comm => self.fetch_comm(ptr).map(|(a, b)| Expression::Comm(a.0, *b)),
            ExprTag::Sym => self.fetch_sym(ptr).map(|sym| Expression::Sym(sym)),
            ExprTag::Key => self.fetch_sym(ptr).map(|sym| Expression::Sym(sym)),
            ExprTag::Num => self.fetch_num(ptr).map(|num| Expression::Num(*num)),
            ExprTag::Fun => self
                .fetch_fun(ptr)
                .map(|(a, b, c)| Expression::Fun(*a, *b, *c)),
            ExprTag::Thunk => self.fetch_thunk(ptr).map(|thunk| Expression::Thunk(*thunk)),
            ExprTag::Str => self.fetch_str(ptr).map(|str| Expression::Str(str)),
            ExprTag::Char => self.fetch_char(ptr).map(Expression::Char),
            ExprTag::U64 => self.fetch_uint(ptr).map(Expression::UInt),
        }
    }

    pub fn fetch_cont(&self, ptr: &ContPtr<F>) -> Option<Continuation<F>> {
        use ContTag::*;
        match ptr.0 {
            Outermost => Some(Continuation::Outermost),
            Call0 => self
                .call0_store
                .get_index(ptr.1.idx())
                .map(|(saved_env, continuation)| Continuation::Call0 {
                    saved_env: *saved_env,
                    continuation: *continuation,
                }),
            Call => self
                .call_store
                .get_index(ptr.1.idx())
                .map(|(a, b, c)| Continuation::Call {
                    unevaled_arg: *a,
                    saved_env: *b,
                    continuation: *c,
                }),
            Call2 => self
                .call2_store
                .get_index(ptr.1.idx())
                .map(|(a, b, c)| Continuation::Call2 {
                    function: *a,
                    saved_env: *b,
                    continuation: *c,
                }),
            Tail => self
                .tail_store
                .get_index(ptr.1.idx())
                .map(|(a, b)| Continuation::Tail {
                    saved_env: *a,
                    continuation: *b,
                }),
            Error => Some(Continuation::Error),
            Lookup => self
                .lookup_store
                .get_index(ptr.1.idx())
                .map(|(a, b)| Continuation::Lookup {
                    saved_env: *a,
                    continuation: *b,
                }),
            Unop => self
                .unop_store
                .get_index(ptr.1.idx())
                .map(|(a, b)| Continuation::Unop {
                    operator: *a,
                    continuation: *b,
                }),
            Binop => {
                self.binop_store
                    .get_index(ptr.1.idx())
                    .map(|(a, b, c, d)| Continuation::Binop {
                        operator: *a,
                        saved_env: *b,
                        unevaled_args: *c,
                        continuation: *d,
                    })
            }
            Binop2 => {
                self.binop2_store
                    .get_index(ptr.1.idx())
                    .map(|(a, b, c)| Continuation::Binop2 {
                        operator: *a,
                        evaled_arg: *b,
                        continuation: *c,
                    })
            }
            If => self
                .if_store
                .get_index(ptr.1.idx())
                .map(|(a, b)| Continuation::If {
                    unevaled_args: *a,
                    continuation: *b,
                }),
            Let => self
                .let_store
                .get_index(ptr.1.idx())
                .map(|(a, b, c, d)| Continuation::Let {
                    var: *a,
                    body: *b,
                    saved_env: *c,
                    continuation: *d,
                }),
            LetRec => self
                .letrec_store
                .get_index(ptr.1.idx())
                .map(|(a, b, c, d)| Continuation::LetRec {
                    var: *a,
                    body: *b,
                    saved_env: *c,
                    continuation: *d,
                }),
            Dummy => Some(Continuation::Dummy),
            Terminal => Some(Continuation::Terminal),
            Emit => self
                .emit_store
                .get_index(ptr.1.idx())
                .map(|continuation| Continuation::Emit {
                    continuation: *continuation,
                }),
        }
    }

    /// Mutable version of car_cdr to handle Str. `(cdr str)` may return a new str (the tail), which must be allocated.
    pub fn car_cdr_mut(&mut self, ptr: &Ptr<F>) -> Result<(Ptr<F>, Ptr<F>), Error> {
        match ptr.0 {
            ExprTag::Nil => Ok((self.get_nil(), self.get_nil())),
            ExprTag::Cons => match self.fetch(ptr) {
                Some(Expression::Cons(car, cdr)) => Ok((car, cdr)),
                Some(Expression::Opaque(_)) => Err(Error("cannot destructure opaque Cons".into())),
                _ => unreachable!(),
            },
            ExprTag::Str => {
                if let Some(Expression::Str(s)) = self.fetch(ptr) {
                    let mut str = s.chars();
                    if let Some(c) = str.next() {
                        let cdr_str: String = str.collect();
                        let str = self.intern_str(&cdr_str);
                        Ok((self.get_char(c), str))
                    } else {
                        Ok((self.nil(), self.intern_str("")))
                    }
                } else {
                    panic!();
                }
            }
            _ => Err(Error("Invalid tag".into())),
        }
    }

    pub fn car_cdr(&self, ptr: &Ptr<F>) -> Result<(Ptr<F>, Ptr<F>), Error> {
        match ptr.0 {
            ExprTag::Nil => Ok((self.get_nil(), self.get_nil())),
            ExprTag::Cons => match self.fetch(ptr) {
                Some(Expression::Cons(car, cdr)) => Ok((car, cdr)),
                Some(Expression::Opaque(_)) => panic!("cannot destructure opaque Cons"),
                _ => unreachable!(),
            },
            ExprTag::Str => {
                if let Some(Expression::Str(s)) = self.fetch(ptr) {
                    Ok({
                        let mut chars = s.chars();
                        if let Some(c) = chars.next() {
                            let cdr_str: String = chars.collect();
                            let str = self.get_str(cdr_str).expect("cdr str missing");
                            (self.get_char(c), str)
                        } else {
                            (self.get_nil(), self.get_str("").unwrap())
                        }
                    })
                } else {
                    panic!();
                }
            }
            _ => Err(Error("Can only extract car_cdr from Cons".into())),
        }
    }

    pub fn hash_expr(&self, ptr: &Ptr<F>) -> Option<ScalarPtr<F>> {
        self.hash_expr_aux(ptr, HashScalar::Create)
    }

    // Get hash for expr, but only if it already exists. This should never cause create_scalar_ptr to be called. Use
    // this after the cache has been hydrated. NOTE: because dashmap::entry can deadlock, it is important not to call
    // hash_expr in nested call graphs which might trigger that behavior. This discovery is what led to get_expr_hash
    // and the 'get' versions of hash_cons, hash_sym, etc.
    pub fn get_expr_hash(&self, ptr: &Ptr<F>) -> Option<ScalarPtr<F>> {
        self.hash_expr_aux(ptr, HashScalar::Get)
    }

    pub fn hash_expr_aux(&self, ptr: &Ptr<F>, mode: HashScalar) -> Option<ScalarPtr<F>> {
        use ExprTag::*;

        if let Some(scalar_ptr) = &self.pointer_scalar_ptr_cache.get(ptr) {
            return Some(**scalar_ptr);
        }

        let scalar_ptr = match ptr.tag() {
            Nil => self.hash_nil(mode),
            Cons => self.hash_cons(*ptr, mode),
            Comm => self.hash_comm(*ptr, mode),
            Sym => self.hash_sym(*ptr, mode),
            Key => self.hash_sym(*ptr, mode),
            Fun => self.hash_fun(*ptr, mode),
            Num => self.hash_num(*ptr, mode),
            Str => self.hash_str(*ptr, mode),
            Char => self.hash_char(*ptr, mode),
            Thunk => self.hash_thunk(*ptr, mode),
            U64 => self.hash_uint(*ptr, mode),
        };

        match mode {
            HashScalar::Create => {
                if let Some(sp) = scalar_ptr {
                    self.pointer_scalar_ptr_cache.insert(*ptr, sp);
                }
            }
            HashScalar::Get => (),
        }

        scalar_ptr
    }

    pub fn hash_cont(&self, ptr: &ContPtr<F>) -> Option<ScalarContPtr<F>> {
        let components = self.get_hash_components_cont(ptr)?;
        let hash = self.poseidon_cache.hash8(&components);

        Some(self.create_cont_scalar_ptr(*ptr, hash))
    }

    fn scalar_ptr(&self, ptr: Ptr<F>, hash: F, mode: HashScalar) -> ScalarPtr<F> {
        match mode {
            HashScalar::Create => self.create_scalar_ptr(ptr, hash),
            HashScalar::Get => self.get_scalar_ptr(ptr, hash),
        }
    }

    /// The only places that `ScalarPtr`s for `Ptr`s should be created, to
    /// ensure that they are cached properly
    fn create_scalar_ptr(&self, ptr: Ptr<F>, hash: F) -> ScalarPtr<F> {
        let scalar_ptr = ScalarPtr::from_parts(ptr.0, hash);
        let entry = self.scalar_ptr_map.entry(scalar_ptr);
        entry.or_insert(ptr);
        scalar_ptr
    }

    fn get_scalar_ptr(&self, ptr: Ptr<F>, hash: F) -> ScalarPtr<F> {
        ScalarPtr::from_parts(ptr.0, hash)
    }

    /// The only places that `ScalarContPtr`s for `ContPtr`s should be created, to
    /// ensure that they are cached properly
    fn create_cont_scalar_ptr(&self, ptr: ContPtr<F>, hash: F) -> ScalarContPtr<F> {
        let scalar_ptr = ScalarContPtr::from_parts(ptr.0, hash);
        self.scalar_ptr_cont_map.entry(scalar_ptr).or_insert(ptr);

        scalar_ptr
    }

    /// The `get_hash_components_*` functions should be kept in sync with the
    /// the arguments of each variant of ScalarContinuation with respect to the
    /// sourc position order of elements
    fn get_hash_components_default(&self) -> [[F; 2]; 4] {
        let def = [F::zero(), F::zero()];
        [def, def, def, def]
    }

    pub fn get_hash_components_cont(&self, ptr: &ContPtr<F>) -> Option<[F; 8]> {
        use Continuation::*;

        let cont = self.fetch_cont(ptr)?;

        let hash = match &cont {
            Outermost | Terminal | Dummy | Error => self.get_hash_components_default(),
            Call0 {
                saved_env,
                continuation,
            } => self.get_hash_components_call0(saved_env, continuation)?,
            Call {
                unevaled_arg,
                saved_env,
                continuation,
            } => self.get_hash_components_call(unevaled_arg, saved_env, continuation)?,
            Call2 {
                function,
                saved_env,
                continuation,
            } => self.get_hash_components_call2(function, saved_env, continuation)?,
            Tail {
                saved_env,
                continuation,
            } => self.get_hash_components_tail(saved_env, continuation)?,
            Lookup {
                saved_env,
                continuation,
            } => self.get_hash_components_lookup(saved_env, continuation)?,
            Unop {
                operator,
                continuation,
            } => self.get_hash_components_unop(operator, continuation)?,
            Binop {
                operator,
                saved_env,
                unevaled_args,
                continuation,
            } => {
                self.get_hash_components_binop(operator, saved_env, unevaled_args, continuation)?
            }
            Binop2 {
                operator,
                evaled_arg,
                continuation,
            } => self.get_hash_components_binop2(operator, evaled_arg, continuation)?,
            If {
                unevaled_args,
                continuation,
            } => self.get_hash_components_if(unevaled_args, continuation)?,
            Let {
                var,
                body,
                saved_env,
                continuation,
            } => self.get_hash_components_let(var, body, saved_env, continuation)?,
            LetRec {
                var,
                body,
                saved_env,
                continuation,
            } => self.get_hash_components_let_rec(var, body, saved_env, continuation)?,
            Emit { continuation } => self.get_hash_components_emit(continuation)?,
        };

        Some([
            hash[0][0], hash[0][1], hash[1][0], hash[1][1], hash[2][0], hash[2][1], hash[3][0],
            hash[3][1],
        ])
    }

    fn get_hash_components_let_rec(
        &self,
        var: &Ptr<F>,
        body: &Ptr<F>,
        saved_env: &Ptr<F>,
        cont: &ContPtr<F>,
    ) -> Option<[[F; 2]; 4]> {
        let var = self.get_expr_hash(var)?.into_hash_components();
        let body = self.get_expr_hash(body)?.into_hash_components();
        let saved_env = self.get_expr_hash(saved_env)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([var, body, saved_env, cont])
    }

    fn get_hash_components_let(
        &self,
        var: &Ptr<F>,
        body: &Ptr<F>,
        saved_env: &Ptr<F>,
        cont: &ContPtr<F>,
    ) -> Option<[[F; 2]; 4]> {
        let var = self.get_expr_hash(var)?.into_hash_components();
        let body = self.get_expr_hash(body)?.into_hash_components();
        let saved_env = self.get_expr_hash(saved_env)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([var, body, saved_env, cont])
    }

    fn get_hash_components_if(
        &self,
        unevaled_args: &Ptr<F>,
        cont: &ContPtr<F>,
    ) -> Option<[[F; 2]; 4]> {
        let def = [F::zero(), F::zero()];
        let unevaled_args = self.get_expr_hash(unevaled_args)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([unevaled_args, cont, def, def])
    }

    fn get_hash_components_binop2(
        &self,
        op: &Op2,
        arg1: &Ptr<F>,
        cont: &ContPtr<F>,
    ) -> Option<[[F; 2]; 4]> {
        let def = [F::zero(), F::zero()];
        let op = [op.to_field(), F::zero()];
        let arg1 = self.get_expr_hash(arg1)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([op, arg1, cont, def])
    }

    fn get_hash_components_binop(
        &self,
        op: &Op2,
        saved_env: &Ptr<F>,
        unevaled_args: &Ptr<F>,
        cont: &ContPtr<F>,
    ) -> Option<[[F; 2]; 4]> {
        let op = [op.to_field(), F::zero()];
        let saved_env = self.get_expr_hash(saved_env)?.into_hash_components();
        let unevaled_args = self.get_expr_hash(unevaled_args)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([op, saved_env, unevaled_args, cont])
    }

    fn get_hash_components_unop(&self, op: &Op1, cont: &ContPtr<F>) -> Option<[[F; 2]; 4]> {
        let def = [F::zero(), F::zero()];
        let op = [op.to_field(), F::zero()];
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([op, cont, def, def])
    }

    fn get_hash_components_lookup(
        &self,
        saved_env: &Ptr<F>,
        cont: &ContPtr<F>,
    ) -> Option<[[F; 2]; 4]> {
        let def = [F::zero(), F::zero()];
        let saved_env = self.get_expr_hash(saved_env)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([saved_env, cont, def, def])
    }

    fn get_hash_components_tail(
        &self,
        saved_env: &Ptr<F>,
        cont: &ContPtr<F>,
    ) -> Option<[[F; 2]; 4]> {
        let def = [F::zero(), F::zero()];
        let saved_env = self.get_expr_hash(saved_env)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([saved_env, cont, def, def])
    }

    fn get_hash_components_call0(
        &self,
        saved_env: &Ptr<F>,
        cont: &ContPtr<F>,
    ) -> Option<[[F; 2]; 4]> {
        let def = [F::zero(), F::zero()];

        let saved_env = self.get_expr_hash(saved_env)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();

        Some([saved_env, cont, def, def])
    }

    fn get_hash_components_call(
        &self,
        arg: &Ptr<F>,
        saved_env: &Ptr<F>,
        cont: &ContPtr<F>,
    ) -> Option<[[F; 2]; 4]> {
        let def = [F::zero(), F::zero()];
        let arg = self.get_expr_hash(arg)?.into_hash_components();
        let saved_env = self.get_expr_hash(saved_env)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();

        Some([saved_env, arg, cont, def])
    }

    fn get_hash_components_call2(
        &self,
        fun: &Ptr<F>,
        saved_env: &Ptr<F>,
        cont: &ContPtr<F>,
    ) -> Option<[[F; 2]; 4]> {
        let def = [F::zero(), F::zero()];
        let fun = self.get_expr_hash(fun)?.into_hash_components();
        let saved_env = self.get_expr_hash(saved_env)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([saved_env, fun, cont, def])
    }

    fn get_hash_components_emit(&self, cont: &ContPtr<F>) -> Option<[[F; 2]; 4]> {
        let def = [F::zero(), F::zero()];

        let cont = self.hash_cont(cont)?.into_hash_components();

        Some([cont, def, def, def])
    }

    pub fn get_hash_components_thunk(&self, thunk: &Thunk<F>) -> Option<[F; 4]> {
        let value_hash = self.get_expr_hash(&thunk.value)?.into_hash_components();
        let continuation_hash = self.hash_cont(&thunk.continuation)?.into_hash_components();

        Some([
            value_hash[0],
            value_hash[1],
            continuation_hash[0],
            continuation_hash[1],
        ])
    }

    pub fn hash_sym(&self, sym: Ptr<F>, mode: HashScalar) -> Option<ScalarPtr<F>> {
        if sym.is_opaque() {
            return self.opaque_map.get(&sym).map(|s| *s);
        }

        let s = self.fetch_sym(&sym)?;
        let sym_hash = self.hash_symbol(&s, mode);

        Some(self.scalar_ptr(sym, sym_hash, mode))
    }

    fn hash_str(&self, str: Ptr<F>, mode: HashScalar) -> Option<ScalarPtr<F>> {
        if str.is_opaque() {
            return self.opaque_map.get(&str).map(|s| *s);
        }

        let s = self.fetch_str(&str)?;
        Some(self.scalar_ptr(str, self.hash_string(s), mode))
    }

    fn hash_fun(&self, fun: Ptr<F>, mode: HashScalar) -> Option<ScalarPtr<F>> {
        if fun.is_opaque() {
            Some(
                *self
                    .opaque_map
                    .get(&fun)
                    .expect("ScalarPtr for opaque Fun missing"),
            )
        } else {
            let (arg, body, closed_env) = self.fetch_fun(&fun)?;
            Some(self.scalar_ptr(
                fun,
                self.hash_ptrs_3(&[*arg, *body, *closed_env], mode)?,
                mode,
            ))
        }
    }

    fn hash_cons(&self, cons: Ptr<F>, mode: HashScalar) -> Option<ScalarPtr<F>> {
        if cons.is_opaque() {
            return Some(
                *self
                    .opaque_map
                    .get(&cons)
                    .expect("ScalarPtr for opaque Cons missing"),
            );
        }

        let (car, cdr) = self.fetch_cons(&cons)?;
        Some(self.scalar_ptr(cons, self.hash_ptrs_2(&[*car, *cdr], mode)?, mode))
    }

    fn hash_comm(&self, comm: Ptr<F>, mode: HashScalar) -> Option<ScalarPtr<F>> {
        if comm.is_opaque() {
            return Some(
                *self
                    .opaque_map
                    .get(&comm)
                    .expect("ScalarPtr for opaque Comm missing"),
            );
        }

        let (secret, payload) = self.fetch_comm(&comm)?;

        let scalar_payload = self.hash_expr(payload)?;
        let hashed = self.commitment_hash(secret.0, scalar_payload);
        Some(self.scalar_ptr(comm, hashed, mode))
    }

    pub(crate) fn commitment_hash(&self, secret_scalar: F, payload: ScalarPtr<F>) -> F {
        let preimage = [secret_scalar, payload.0.to_field(), payload.1];
        self.poseidon_cache.hash3(&preimage)
    }

    fn hash_thunk(&self, ptr: Ptr<F>, mode: HashScalar) -> Option<ScalarPtr<F>> {
        let thunk = self.fetch_thunk(&ptr)?;
        let components = self.get_hash_components_thunk(thunk)?;
        Some(self.scalar_ptr(ptr, self.poseidon_cache.hash4(&components), mode))
    }

    fn hash_char(&self, ptr: Ptr<F>, mode: HashScalar) -> Option<ScalarPtr<F>> {
        let char_code = ptr.1 .0 .0 as u32;

        Some(self.scalar_ptr(ptr, F::from(char_code as u64), mode))
    }

    fn hash_num(&self, ptr: Ptr<F>, mode: HashScalar) -> Option<ScalarPtr<F>> {
        let n = self.fetch_num(&ptr)?;

        Some(self.scalar_ptr(ptr, n.into_scalar(), mode))
    }

    fn hash_uint(&self, ptr: Ptr<F>, mode: HashScalar) -> Option<ScalarPtr<F>> {
        let n = self.fetch_uint(&ptr)?;

        match n {
            UInt::U64(x) => Some(self.scalar_ptr(ptr, F::from_u64(x), mode)),
        }
    }

    fn hash_symbol(&self, s: &Sym, mode: HashScalar) -> F {
        if s.is_root() {
            return F::zero();
        }

        let path = s.path();
        assert!(!path.is_empty());

        let mut full_name_acc: Option<String> = None;
        let mut final_hash = None;
        for name in path.iter() {
            let name_str = self.get_str(name).unwrap();

            let (prev_full_name, full_name) = if let Some(x) = full_name_acc.clone() {
                // We need to quote the path segment when constructing the incremental full-name.
                // This is because when symbols are interned by full-name, the canonical name,
                // which includes any necessary quoting, is used.
                //
                // Eventually, we will remove symbol lookup by full-name, simplifying this.
                let name = crate::parser::maybe_quote_symbol_name_string(name).unwrap();

                if x.is_empty() {
                    let x: String = x;
                    (x, format!(".{name}"))
                } else if x.starts_with('.') {
                    let x: String = x;
                    (x.clone(), format!("{x}.{name}"))
                } else {
                    (x.clone(), format!(".{x}.{name}"))
                }
            } else {
                ("".to_string(), "".to_string())
            };

            let p = { self.get_sym_by_full_name(prev_full_name) };
            full_name_acc = Some(full_name);

            let hash = self.hash_ptrs_2(&[name_str, p], mode).unwrap();

            if let Some(prev_hash) = final_hash {
                self.scalar_ptr(p, prev_hash, mode);
            }
            final_hash = Some(hash);
        }

        let final_hash = final_hash.unwrap();
        if let Some(x) = full_name_acc {
            let p = self.get_sym_by_full_name(x);
            self.scalar_ptr(p, final_hash, mode);
        };

        final_hash
    }

    fn hash_string(&self, s: &str) -> F {
        if s.is_empty() {
            return F::zero();
        };
        let mut chars = s.chars();
        let char = chars.next().unwrap();
        let rest_string = chars.collect::<String>();
        let c = self.get_char(char);

        let rest = self.get_str(rest_string).expect("str missing from store");

        self.hash_ptrs_2(&[c, rest], HashScalar::Get).unwrap()
    }

    pub fn hash_string_mut<T: AsRef<str>>(&mut self, s: T) -> F {
        let s = s.as_ref();
        if s.is_empty() {
            return F::zero();
        };

        let initial_scalar_ptr = {
            let hash = F::zero();
            let ptr = self.intern_str_aux("");
            self.create_scalar_ptr(ptr, hash)
        };

        let all_hashes = self.all_hashes(s, initial_scalar_ptr);
        let v: VecDeque<char> = s.chars().collect();
        self.hash_string_mut_aux(v, all_hashes)
    }

    // All hashes of substrings, shortest to longest.
    fn all_hashes(&mut self, s: &str, initial_scalar_ptr: ScalarPtr<F>) -> Vec<F> {
        let chars = s.chars().rev();
        let mut hashes = Vec::with_capacity(s.len());

        chars.fold(initial_scalar_ptr, |acc, char| {
            let c_scalar: F = (u32::from(char) as u64).into();
            // This bypasses create_scalar_ptr but is okay because Chars are immediate and don't need to be indexed.
            let c = ScalarPtr::from_parts(ExprTag::Char, c_scalar);
            let hash = self.hash_scalar_ptrs_2(&[c, acc]);
            // This bypasses create_scalar_ptr but is okay because we will call it to correctly create each of these
            // ScalarPtrs below, in hash_string_mut_aux.
            let new_scalar_ptr = ScalarPtr::from_parts(ExprTag::Str, hash);
            hashes.push(hash);
            new_scalar_ptr
        });

        hashes
    }

    fn hash_string_mut_aux(&mut self, mut s: VecDeque<char>, all_hashes: Vec<F>) -> F {
        debug_assert_eq!(s.len(), all_hashes.len());

        let final_hash = all_hashes.last().unwrap();

        for hash in all_hashes.iter().rev() {
            let string = s.iter().collect::<String>();
            let ptr = self.intern_str_aux(&string);
            self.create_scalar_ptr(ptr, *hash);
            s.pop_front();
        }

        *final_hash
    }

    fn hash_ptrs_2(&self, ptrs: &[Ptr<F>; 2], mode: HashScalar) -> Option<F> {
        let scalar_ptrs = [
            self.hash_expr_aux(&ptrs[0], mode)?,
            self.hash_expr_aux(&ptrs[1], mode)?,
        ];
        Some(self.hash_scalar_ptrs_2(&scalar_ptrs))
    }

    fn hash_ptrs_3(&self, ptrs: &[Ptr<F>; 3], mode: HashScalar) -> Option<F> {
        let scalar_ptrs = [
            self.hash_expr_aux(&ptrs[0], mode)?,
            self.hash_expr_aux(&ptrs[1], mode)?,
            self.hash_expr_aux(&ptrs[2], mode)?,
        ];
        Some(self.hash_scalar_ptrs_3(&scalar_ptrs))
    }

    fn hash_scalar_ptrs_2(&self, ptrs: &[ScalarPtr<F>; 2]) -> F {
        let preimage = [
            ptrs[0].0.to_field::<F>(),
            ptrs[0].1,
            ptrs[1].0.to_field::<F>(),
            ptrs[1].1,
        ];
        self.poseidon_cache.hash4(&preimage)
    }

    fn hash_scalar_ptrs_3(&self, ptrs: &[ScalarPtr<F>; 3]) -> F {
        let preimage = [
            ptrs[0].0.to_field::<F>(),
            ptrs[0].1,
            ptrs[1].0.to_field::<F>(),
            ptrs[1].1,
            ptrs[2].0.to_field::<F>(),
            ptrs[2].1,
        ];
        self.poseidon_cache.hash6(&preimage)
    }

    pub fn hash_nil(&self, mode: HashScalar) -> Option<ScalarPtr<F>> {
        let nil = self.get_nil();

        self.hash_sym(nil, mode)
    }

    // An opaque Ptr is one for which we have the hash, but not the preimages.
    // So we cannot open or traverse the enclosed data, but we can manipulate
    // it atomically and include it in containing structures, etc.
    pub fn new_opaque_ptr(&mut self) -> Ptr<F> {
        // TODO: May need new tag for this.
        // Meanwhile, it is illegal to try to dereference/follow an opaque PTR.
        // So any tag and RawPtr are okay.
        Ptr(ExprTag::Nil, self.new_opaque_raw_ptr())
    }

    pub fn new_opaque_raw_ptr(&mut self) -> RawPtr<F> {
        self.opaque_raw_ptr_count += 1;
        let p = self.opaque_raw_ptr_count;

        RawPtr((p, true), Default::default())
    }

    pub fn ptr_eq(&self, a: &Ptr<F>, b: &Ptr<F>) -> Result<bool, Error> {
        // In order to compare Ptrs, we *must* resolve the hashes. Otherwise, we risk failing to recognize equality of
        // compound data with opaque data in either element's transitive closure.
        match (self.get_expr_hash(a), self.get_expr_hash(b)) {
            (Some(a_hash), Some(b_hash)) => Ok(a.0 == b.0 && a_hash == b_hash),
            _ => Err(Error(
                "one or more values missing when comparing Ptrs for equality".into(),
            )),
        }
    }

    pub fn cons_eq(&self, a: &Ptr<F>, b: &Ptr<F>) -> bool {
        assert_eq!(ExprTag::Cons, a.tag());
        assert_eq!(ExprTag::Cons, b.tag());

        let a_opaque = a.is_opaque();
        let b_opaque = b.is_opaque();

        if !a_opaque && !b_opaque {
            return a == b;
        }
        self.get_expr_hash(a) == self.get_expr_hash(b)
    }

    /// Fill the cache for Scalars. Only Ptrs which have been interned since last hydration will be hashed, so it is
    /// safe to call this incrementally. However, for best proving performance, we should call exactly once so all
    /// hashing can be batched, e.g. on the GPU.
    pub fn hydrate_scalar_cache(&mut self) {
        self.ensure_constants();

        self.dehydrated.par_iter().for_each(|ptr| {
            self.hash_expr(ptr).expect("failed to hash_expr");
        });

        self.dehydrated.truncate(0);

        self.dehydrated_cont.par_iter().for_each(|ptr| {
            self.hash_cont(ptr).expect("failed to hash_cont");
        });

        self.dehydrated_cont.truncate(0);

        self.dehydrated_cont.clear();
    }

    fn ensure_constants(&mut self) {
        // This will clobber whatever was there before.
        let _ = self.constants.set(NamedConstants::new(self));
    }

    pub fn get_constants(&self) -> &NamedConstants<F> {
        self.constants.get_or_init(|| NamedConstants::new(self))
    }
}

impl<F: LurkField> Expression<'_, F> {
    pub fn is_keyword_sym(&self) -> bool {
        match self {
            Expression::Sym(s) => s.is_keyword(),
            _ => false,
        }
    }

    pub const fn as_str(&self) -> Option<&str> {
        match self {
            Expression::Str(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_sym_str(&self) -> Option<String> {
        match self {
            Expression::Sym(s) => Some(s.full_name()),
            _ => None,
        }
    }

    pub const fn as_sym(&self) -> Option<&Sym> {
        match self {
            Expression::Sym(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_simple_keyword_string(&self) -> Option<String> {
        match self {
            Expression::Sym(s) => s.simple_keyword_name(),
            _ => None,
        }
    }

    pub const fn is_null(&self) -> bool {
        matches!(self, Self::Nil)
    }

    pub const fn is_cons(&self) -> bool {
        matches!(self, Self::Cons(_, _))
    }

    pub const fn is_list(&self) -> bool {
        self.is_null() || self.is_cons()
    }

    pub const fn is_sym(&self) -> bool {
        matches!(self, Self::Sym(_))
    }
    pub const fn is_fun(&self) -> bool {
        matches!(self, Self::Fun(_, _, _))
    }

    pub const fn is_num(&self) -> bool {
        matches!(self, Self::Num(_))
    }
    pub const fn is_str(&self) -> bool {
        matches!(self, Self::Str(_))
    }

    pub const fn is_thunk(&self) -> bool {
        matches!(self, Self::Thunk(_))
    }

    pub const fn is_opaque(&self) -> bool {
        matches!(self, Self::Opaque(_))
    }
}

#[derive(Copy, Clone, Debug)]
pub struct ConstantPtrs<F: LurkField>(Option<ScalarPtr<F>>, Ptr<F>);

impl<F: LurkField> ConstantPtrs<F> {
    pub fn value(&self) -> F {
        *self.scalar_ptr().value()
    }
    pub fn scalar_ptr(&self) -> ScalarPtr<F> {
        self.0
            .expect("ScalarPtr missing; hydrate_scalar_cache should have been called.")
    }
    pub const fn ptr(&self) -> Ptr<F> {
        self.1
    }
}

#[derive(Clone, Copy, Debug)]
pub struct NamedConstants<F: LurkField> {
    pub t: ConstantPtrs<F>,
    pub nil: ConstantPtrs<F>,
    pub lambda: ConstantPtrs<F>,
    pub quote: ConstantPtrs<F>,
    pub let_: ConstantPtrs<F>,
    pub letrec: ConstantPtrs<F>,
    pub cons: ConstantPtrs<F>,
    pub strcons: ConstantPtrs<F>,
    pub begin: ConstantPtrs<F>,
    pub car: ConstantPtrs<F>,
    pub cdr: ConstantPtrs<F>,
    pub atom: ConstantPtrs<F>,
    pub emit: ConstantPtrs<F>,
    pub sum: ConstantPtrs<F>,
    pub diff: ConstantPtrs<F>,
    pub product: ConstantPtrs<F>,
    pub quotient: ConstantPtrs<F>,
    pub modulo: ConstantPtrs<F>,
    pub num_equal: ConstantPtrs<F>,
    pub equal: ConstantPtrs<F>,
    pub less: ConstantPtrs<F>,
    pub less_equal: ConstantPtrs<F>,
    pub greater: ConstantPtrs<F>,
    pub greater_equal: ConstantPtrs<F>,
    pub current_env: ConstantPtrs<F>,
    pub if_: ConstantPtrs<F>,
    pub hide: ConstantPtrs<F>,
    pub commit: ConstantPtrs<F>,
    pub num: ConstantPtrs<F>,
    pub u64: ConstantPtrs<F>,
    pub comm: ConstantPtrs<F>,
    pub char: ConstantPtrs<F>,
    pub eval: ConstantPtrs<F>,
    pub open: ConstantPtrs<F>,
    pub secret: ConstantPtrs<F>,
    pub dummy: ConstantPtrs<F>,
}

impl<F: LurkField> NamedConstants<F> {
    pub fn new(store: &Store<F>) -> Self {
        let hash_sym = |name: &str| {
            let ptr = store.get_lurk_sym(name, true).unwrap();
            let maybe_scalar_ptr = store.hash_sym(ptr, HashScalar::Get);
            ConstantPtrs(maybe_scalar_ptr, ptr)
        };

        let t = hash_sym("t");
        let nil = ConstantPtrs(
            Some(store.hash_nil(HashScalar::Get).unwrap()),
            store.get_nil(),
        );
        let lambda = hash_sym("lambda");
        let quote = hash_sym("quote");
        let let_ = hash_sym("let");
        let letrec = hash_sym("letrec");
        let cons = hash_sym("cons");
        let strcons = hash_sym("strcons");
        let begin = hash_sym("begin");
        let car = hash_sym("car");
        let cdr = hash_sym("cdr");
        let atom = hash_sym("atom");
        let emit = hash_sym("emit");
        let sum = hash_sym("+");
        let diff = hash_sym("-");
        let product = hash_sym("*");
        let quotient = hash_sym("/");
        let modulo = hash_sym("%");
        let num_equal = hash_sym("=");
        let equal = hash_sym("eq");
        let less = hash_sym("<");
        let less_equal = hash_sym("<=");
        let greater = hash_sym(">");
        let greater_equal = hash_sym(">=");
        let current_env = hash_sym("current-env");
        let if_ = hash_sym("if");
        let hide = hash_sym("hide");
        let commit = hash_sym("commit");
        let num = hash_sym("num");
        let u64 = hash_sym("u64");
        let comm = hash_sym("comm");
        let char = hash_sym("char");
        let eval = hash_sym("eval");
        let open = hash_sym("open");
        let secret = hash_sym("secret");
        let dummy = hash_sym("_");

        Self {
            t,
            nil,
            lambda,
            quote,
            let_,
            letrec,
            cons,
            strcons,
            begin,
            car,
            cdr,
            atom,
            emit,
            sum,
            diff,
            product,
            quotient,
            modulo,
            num_equal,
            equal,
            less,
            less_equal,
            greater,
            greater_equal,
            current_env,
            if_,
            hide,
            commit,
            num,
            u64,
            comm,
            char,
            eval,
            open,
            secret,
            dummy,
        }
    }
}

#[cfg(test)]
pub mod test {
    use crate::eval::{empty_sym_env, Evaluator};
    use crate::num;
    use crate::writer::Write;
    use blstrs::Scalar as Fr;

    use super::*;

    use libipld::serde::from_ipld;
    use libipld::serde::to_ipld;
    use libipld::Ipld;

    proptest! {
      #[test]
      fn test_scalar_ptr_ipld(x in any::<ScalarPtr<Fr>>())  {
        let to_ipld = to_ipld(x).unwrap();
        let from_ipld = from_ipld(to_ipld).unwrap();
        assert_eq!(x, from_ipld);
      }

      #[test]
      fn prop_scalar_cont_ptr_ipld(x in any::<ScalarContPtr<Fr>>()) {
          let to_ipld = to_ipld(x).unwrap();
              let from_ipld = from_ipld(to_ipld).unwrap();
              assert_eq!(x, from_ipld);

      }
      #[test]
      fn prop_op1_ipld(x in any::<Op1>())  {
          let to_ipld = to_ipld(x).unwrap();
          let from_ipld = from_ipld(to_ipld).unwrap();
          assert_eq!(x, from_ipld);
      }
    }

    #[test]
    fn unit_op1_ipld() {
        assert_eq!(
            to_ipld(Op1::Car).unwrap(),
            Ipld::Integer(0b0010_0000_0000_0000_i128)
        );
    }

    proptest! {
      #[test]
      fn prop_op2_ipld(x in any::<Op1>())  {
          let to_ipld = to_ipld(x).unwrap();
          let from_ipld = from_ipld(to_ipld).unwrap();
          assert_eq!(x, from_ipld);
      }
    }

    #[test]
    fn unit_op2_ipld() {
        assert_eq!(
            to_ipld(Op2::Sum).unwrap(),
            Ipld::Integer(0b0011_0000_0000_0000_i128)
        );
    }

    #[test]
    fn test_print_num() {
        let mut store = Store::<Fr>::default();
        let num = store.num(5);
        let res = num.fmt_to_string(&store);
        assert_eq!(&res, &"5");
    }

    #[test]
    fn tag_vals() {
        assert_eq!(0, ExprTag::Nil as u64);
        assert_eq!(1, ExprTag::Cons as u64);
        assert_eq!(2, ExprTag::Sym as u64);
        assert_eq!(3, ExprTag::Fun as u64);
        assert_eq!(4, ExprTag::Num as u64);
        assert_eq!(5, ExprTag::Thunk as u64);
        assert_eq!(6, ExprTag::Str as u64);
        assert_eq!(7, ExprTag::Char as u64);
        assert_eq!(8, ExprTag::Comm as u64);
        assert_eq!(9, ExprTag::U64 as u64);
        assert_eq!(10, ExprTag::Key as u64);
    }

    #[test]
    fn cont_tag_vals() {
        use super::ContTag::*;

        assert_eq!(0b0001_0000_0000_0000, Outermost as u16);
        assert_eq!(0b0001_0000_0000_0001, Call0 as u16);
        assert_eq!(0b0001_0000_0000_0010, Call as u16);
        assert_eq!(0b0001_0000_0000_0011, Call2 as u16);
        assert_eq!(0b0001_0000_0000_0100, Tail as u16);
        assert_eq!(0b0001_0000_0000_0101, Error as u16);
        assert_eq!(0b0001_0000_0000_0110, Lookup as u16);
        assert_eq!(0b0001_0000_0000_0111, Unop as u16);
        assert_eq!(0b0001_0000_0000_1000, Binop as u16);
        assert_eq!(0b0001_0000_0000_1001, Binop2 as u16);
        assert_eq!(0b0001_0000_0000_1010, If as u16);
        assert_eq!(0b0001_0000_0000_1011, Let as u16);
        assert_eq!(0b0001_0000_0000_1100, LetRec as u16);
        assert_eq!(0b0001_0000_0000_1101, Dummy as u16);
        assert_eq!(0b0001_0000_0000_1110, Terminal as u16);
        assert_eq!(0b0001_0000_0000_1111, Emit as u16);
    }

    #[test]
    fn store() {
        let mut store = Store::<Fr>::default();

        let num_ptr = store.num(123);
        let num = store.fetch(&num_ptr).unwrap();
        let num_again = store.fetch(&num_ptr).unwrap();

        assert_eq!(num, num_again);
    }

    #[test]
    fn equality() {
        let mut store = Store::<Fr>::default();

        let (a, b) = (store.num(123), store.sym("pumpkin"));
        let cons1 = store.intern_cons(a, b);
        let (a, b) = (store.num(123), store.sym("pumpkin"));
        let cons2 = store.intern_cons(a, b);

        assert_eq!(cons1, cons2);
        assert_eq!(store.car(&cons1).unwrap(), store.car(&cons2).unwrap());
        assert_eq!(store.cdr(&cons1).unwrap(), store.cdr(&cons2).unwrap());

        let (a, d) = store.car_cdr(&cons1).unwrap();
        assert_eq!(store.car(&cons1).unwrap(), a);
        assert_eq!(store.cdr(&cons1).unwrap(), d);
    }

    #[test]
    fn opaque_fun() {
        let mut store = Store::<Fr>::default();

        let arg = store.sym("A");
        let body_form = store.num(123);
        let body2_form = store.num(987);
        let body = store.list(&[body_form]);
        let body2 = store.list(&[body2_form]);
        let empty_env = empty_sym_env(&store);
        let fun = store.intern_fun(arg, body, empty_env);
        let fun2 = store.intern_fun(arg, body2, empty_env);
        let fun_hash = store.hash_expr(&fun).unwrap();
        let fun_hash2 = store.hash_expr(&fun2).unwrap();
        let opaque_fun = store.intern_opaque_fun(*fun_hash.value());
        let opaque_fun2 = store.intern_opaque_fun(*fun_hash2.value());

        let eq = store.sym("eq");
        let t = store.sym("t");
        let nil = store.nil();
        let limit = 10;
        {
            let comparison_expr = store.list(&[eq, fun, opaque_fun]);
            println!("comparison_expr: {}", comparison_expr.fmt_to_string(&store));
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &mut store, limit)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, fun2, opaque_fun]);
            println!("comparison_expr: {}", comparison_expr.fmt_to_string(&store));
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &mut store, limit)
                .eval()
                .unwrap();
            assert_eq!(nil, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, fun2, opaque_fun2]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &mut store, limit)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
        {
            // This test is important. It demonstrates that we can handle opaque data in compound data being evaluated
            // without this affecting equality semantics.

            let n = store.num(123);
            let cons = store.sym("cons");
            let cons_expr1 = store.list(&[cons, fun, n]);
            let cons_expr2 = store.list(&[cons, opaque_fun, n]);

            let comparison_expr = store.list(&[eq, cons_expr1, cons_expr2]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &mut store, limit)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
    }

    #[test]
    fn opaque_sym() {
        let mut store = Store::<Fr>::default();

        let empty_env = empty_sym_env(&store);
        let sym = store.sym("sym");
        let sym2 = store.sym("sym2");
        let sym_hash = store.hash_expr(&sym).unwrap();
        let sym_hash2 = store.hash_expr(&sym2).unwrap();
        let opaque_sym = store.intern_opaque_sym(*sym_hash.value());
        let opaque_sym2 = store.intern_opaque_sym(*sym_hash2.value());

        let quote = store.sym("quote");
        let qsym = store.list(&[quote, sym]);
        let qsym2 = store.list(&[quote, sym2]);
        let qsym_opaque = store.list(&[quote, opaque_sym]);
        let qsym_opaque2 = store.list(&[quote, opaque_sym2]);

        let eq = store.sym("eq");
        let t = store.sym("t");
        let nil = store.nil();
        let limit = 10;

        // When an opaque sym is inserted into a store which contains the same sym, the store knows its identity.
        // Should we just immediately coalesce and never create an opaque version in that case? Probably not because
        // that may interact badly with explicit hiding to be implemented.
        // Let's defer any such considerations until we have a well-specified way of segreting secret/private data.
        //
        // If implemented, the following commented test would pass.
        // assert_eq!(sym.fmt_to_string(&store), opaque_sym.fmt_to_string(&store));

        // For now, all opaque data remains opaque, even if the Store has enough information to clarify it.
        assert!(sym.fmt_to_string(&store) != opaque_sym.fmt_to_string(&store));

        let mut other_store = Store::<Fr>::default();
        let other_opaque_sym = other_store.intern_opaque_sym(*sym_hash.value());

        let other_sym = other_store.sym("sym");
        // other_sym and other_opaque_sym are not equal, since the non-opaque symbol was inserted after the opaque one.
        // TODO: we could check for this and fix when inserting non-opaque syms. If we decide to clarify opaque data
        // when possible, we should do this too.
        assert!(
            other_sym.fmt_to_string(&other_store) != other_opaque_sym.fmt_to_string(&other_store)
        );

        let num = num::Num::from_scalar(*sym_hash.value());
        assert_eq!(
            format!(
                "<Opaque Sym {}>",
                Expression::Num(num).fmt_to_string(&store)
            ),
            other_opaque_sym.fmt_to_string(&other_store)
        );

        // We need to insert a few opaque syms in other_store, in order to acquire a raw_ptr that doesn't exist in
        // store. Use that to check for a malformed/missing opaque sym in store below.
        let _other_opaque_sym2 = other_store.intern_opaque_sym(*sym_hash.value());
        let other_opaque_sym3 = other_store.intern_opaque_sym(*sym_hash.value());

        // other_opaque_sym doesn't exist at all in store, but it is recognized as an opaque sym.
        // It still prints 'normally', but attempts to fetch its name detect this case.
        // This shouldn't actually happen. The test just exercise the code path which detects it.
        assert_eq!("<Opaque Sym>", other_opaque_sym3.fmt_to_string(&store));
        assert_eq!(
            Sym::new_opaque(false),
            store.fetch_sym(&other_opaque_sym3).unwrap()
        );

        {
            let comparison_expr = store.list(&[eq, qsym, qsym_opaque]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &mut store, limit)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, qsym2, qsym_opaque]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &mut store, limit)
                .eval()
                .unwrap();
            assert_eq!(nil, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, qsym2, qsym_opaque2]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &mut store, limit)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
        {
            // This test is important. It demonstrates that we can handle opaque data in compound data being evaluated
            // without this affecting equality semantics.

            let n = store.num(123);
            let cons = store.sym("cons");
            let cons_expr1 = store.list(&[cons, qsym, n]);
            let cons_expr2 = store.list(&[cons, qsym_opaque, n]);

            let comparison_expr = store.list(&[eq, cons_expr1, cons_expr2]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &mut store, limit)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
    }

    #[test]
    fn opaque_cons() {
        let mut store = Store::<Fr>::default();

        let num1 = store.num(123);
        let num2 = store.num(987);
        let empty_env = empty_sym_env(&store);
        let cons = store.intern_cons(num1, num2);
        let cons2 = store.intern_cons(num2, num1);
        let cons_hash = store.hash_expr(&cons).unwrap();
        let cons_hash2 = store.hash_expr(&cons2).unwrap();
        let opaque_cons = store.intern_opaque_cons(*cons_hash.value());
        let opaque_cons2 = store.intern_opaque_cons(*cons_hash2.value());

        let eq = store.sym("eq");
        let t = store.sym("t");
        let nil = store.nil();
        let limit = 10;
        let quote = store.sym("quote");
        let qcons = store.list(&[quote, cons]);
        let qcons2 = store.list(&[quote, cons2]);
        let qcons_opaque = store.list(&[quote, opaque_cons]);
        let qcons_opaque2 = store.list(&[quote, opaque_cons2]);

        let num = Expression::Num(num::Num::Scalar(*cons_hash.value()));
        assert_eq!(
            format!("<Opaque Cons {}>", num.fmt_to_string(&store)),
            opaque_cons.fmt_to_string(&store)
        );

        {
            let comparison_expr = store.list(&[eq, qcons, qcons_opaque]);
            // FIXME: need to implement Write for opaque data.
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &mut store, limit)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, qcons2, qcons_opaque]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &mut store, limit)
                .eval()
                .unwrap();
            assert_eq!(nil, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, qcons2, qcons_opaque2]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &mut store, limit)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
        {
            // This test is important. It demonstrates that we can handle opaque data in compound data being evaluated
            // without this affecting equality semantics.

            let n = store.num(123);
            let n2 = store.num(321);
            let cons_sym = store.sym("cons");
            let cons_expr1 = store.list(&[cons_sym, qcons, n]);
            let cons_expr2 = store.list(&[cons_sym, qcons_opaque, n]);
            let cons_expr3 = store.list(&[cons_sym, qcons_opaque, n2]);

            let comparison_expr = store.list(&[eq, cons_expr1, cons_expr2]);
            let comparison_expr2 = store.list(&[eq, cons_expr1, cons_expr3]);
            {
                let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &mut store, limit)
                    .eval()
                    .unwrap();
                assert_eq!(t, result.expr);
            }
            {
                let (result, _, _) = Evaluator::new(comparison_expr2, empty_env, &mut store, limit)
                    .eval()
                    .unwrap();
                assert_eq!(nil, result.expr);
            }
        }
    }

    fn make_maybe_opaque_cons(store: &mut Store<Fr>, car: u64, cdr: u64) -> Ptr<Fr> {
        let num1 = store.num(Num::<Fr>::from(car));
        let num2 = store.num(Num::<Fr>::from(cdr));
        let cons = store.intern_cons(num1, num2);
        let cons_hash = store.hash_expr(&cons).unwrap();

        store.intern_maybe_opaque_cons(*cons_hash.value())
    }

    fn make_opaque_cons(store: &mut Store<Fr>) -> Ptr<Fr> {
        store.intern_opaque_cons(12345.into())
    }

    #[test]
    #[should_panic]
    fn opaque_cons_car() {
        let mut store = Store::<Fr>::default();

        let opaque_cons = make_opaque_cons(&mut store);
        store.car(&opaque_cons).unwrap();
    }
    #[test]
    #[should_panic]
    fn opaque_cons_cdr() {
        let mut store = Store::<Fr>::default();

        let opaque_cons = make_opaque_cons(&mut store);
        store.cdr(&opaque_cons).unwrap();
    }

    #[test]
    fn maybe_opaque_cons_car() {
        let mut store = Store::<Fr>::default();

        let opaque_cons = make_maybe_opaque_cons(&mut store, 123, 987);
        store.car(&opaque_cons).unwrap();
    }
    #[test]
    fn maybe_opaque_cons_cdr() {
        let mut store = Store::<Fr>::default();

        let opaque_cons = make_maybe_opaque_cons(&mut store, 123, 987);
        store.cdr(&opaque_cons).unwrap();
    }

    #[test]
    fn sym_and_key_hashes() {
        let s = &mut Store::<Fr>::default();

        let sym = s.root_sym("orange", false);
        let key = s.key("orange");

        let sym_ptr = s.get_expr_hash(&sym).unwrap();
        let key_ptr = s.hash_expr(&key).unwrap();
        let sym_hash = sym_ptr.1;
        let key_hash = key_ptr.1;

        let sym_expr = s.fetch_sym(&sym);
        let key_expr = s.fetch_sym(&key);

        dbg!(&sym_expr, &key_expr);

        assert_eq!(sym_hash, key_hash);
        assert!(sym_ptr != key_ptr);
    }

    #[test]
    fn sym_in_list() {
        let s = &mut Store::<Fr>::default();

        let expr = s.read("(foo)").unwrap();
        let sym = s.read("foo").unwrap();
        let sym1 = s.car(&expr).unwrap();
        let sss = s.fetch_sym(&sym);
        let hash = s.get_expr_hash(&sym);
        dbg!(&sym1, &sss, &hash);

        assert_eq!(sym, sym1);
    }

    #[test]
    fn empty_sym_tag_hash() {
        let s = &mut Store::<Fr>::default();

        let sym = s.sym("");
        let sym_tag = s.get_expr_hash(&sym).unwrap().0;
        // let sym_hash = s.get_expr_hash(&sym).unwrap().1;

        assert_eq!(ExprTag::Sym, sym_tag);

        // FIXME: What should this be? Should this even be allowed?
        // assert_eq!(Fr::from(0), sym_hash)
    }

    #[test]
    fn str_car_cdr_hashes() {
        let s = &mut Store::<Fr>::default();

        let str = s.read(r#" "ORANGE" "#).unwrap();
        let str2 = s.cdr(&str).unwrap();
        let c = s.car(&str).unwrap();

        let str_hash = s.hash_expr(&str).unwrap().1;

        let str_again = s.cons(c, str2);
        let str_again_hash = s.hash_expr(&str_again).unwrap().1;

        assert_eq!(str_hash, str_again_hash);
    }

    fn str_inner_fetch_aux(str: &str, hydrate: bool) {
        let s = &mut Store::<Fr>::default();

        let str = s.read(str).unwrap();
        let str2 = s.cdr(&str).unwrap();

        // Unless the cache is hydrated, the inner destructuring will not map the ScalarPtr to corresponding Ptr.
        if hydrate {
            s.hydrate_scalar_cache();
        };

        let str2_scalar_ptr = s.get_expr_hash(&str2).unwrap();

        let str2_again = s.fetch_scalar(&str2_scalar_ptr).unwrap();

        assert_eq!(str2, str2_again);
    }

    #[test]
    fn str_inner_fetch_hydrated() {
        str_inner_fetch_aux(r#" "ORANGE" "#, true);
    }

    #[test]
    fn str_inner_fetch_unhydrated() {
        str_inner_fetch_aux(r#" "ORANGE" "#, false);
    }

    fn empty_str_fetch_aux(hydrate: bool) {
        let s = &mut Store::<Fr>::default();

        let str = s.read(r#" "" "#).unwrap();

        // Unless the cache is hydrated, the inner destructuring will not map the ScalarPtr to corresponding Ptr.
        if hydrate {
            s.hydrate_scalar_cache();
        };

        let str_scalar_ptr = s.get_expr_hash(&str).unwrap();

        let str_again = s.fetch_scalar(&str_scalar_ptr).unwrap();

        assert_eq!(str, str_again);
    }
    #[test]
    fn empty_str_fetch_hydrated() {
        empty_str_fetch_aux(true);
    }

    #[test]
    fn empty_str_fetch_unhydrated() {
        empty_str_fetch_aux(false);
    }

    #[test]
    fn opaque_comm_fmt() {
        let s = &mut Store::<Fr>::default();

        let scalar = Fr::from(123);
        let opaque_comm = s.intern_opaque_comm(Fr::from(123));
        let expr = s.fetch(&opaque_comm).unwrap();

        let num = num::Num::from_scalar(scalar);
        assert_eq!(
            format!("<Opaque Comm {}>", Expression::Num(num).fmt_to_string(s)),
            opaque_comm.fmt_to_string(s),
        );

        assert_eq!(opaque_comm.fmt_to_string(s), expr.fmt_to_string(s));
    }
}
