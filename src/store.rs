use blstrs::Scalar;
use ff::{Field, PrimeField};
use itertools::Itertools;
use neptune::Poseidon;
use std::fmt;
use std::hash::Hash;
use string_interner::symbol::{Symbol, SymbolUsize};

use generic_array::typenum::{U10, U11, U16, U2, U3, U4, U5, U6, U7, U8, U9};
use neptune::{hash_type::HashType, poseidon::PoseidonConstants, Strength};
use rayon::prelude::*;

use crate::Num;

lazy_static::lazy_static! {
    pub static ref POSEIDON_CONSTANTS_2: PoseidonConstants::<Scalar, U2> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_3: PoseidonConstants::<Scalar, U3> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_4: PoseidonConstants::<Scalar, U4> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_5: PoseidonConstants::<Scalar, U5> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_6: PoseidonConstants::<Scalar, U6> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_7: PoseidonConstants::<Scalar, U7> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_8: PoseidonConstants::<Scalar, U8> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_9: PoseidonConstants::<Scalar, U9> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_10: PoseidonConstants::<Scalar, U10> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_11: PoseidonConstants::<Scalar, U11> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_16: PoseidonConstants::<Scalar, U16> = PoseidonConstants::new();
    pub static ref POSEIDON_CONSTANTS_VARIABLE: PoseidonConstants::<Scalar, U16> =
        PoseidonConstants::new_with_strength_and_type(Strength::Standard, HashType::VariableLength);
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
pub struct Store {
    cons_store: IndexSet<(Ptr, Ptr)>,
    sym_store: StringSet,
    // Other sparse storage format without hashing is likely more efficient
    num_store: IndexSet<Num>,
    fun_store: IndexSet<(Ptr, Ptr, Ptr)>,
    str_store: StringSet,
    thunk_store: IndexSet<Thunk>,

    simple_store: IndexSet<ContPtr>,
    call_store: IndexSet<(Ptr, Ptr, ContPtr)>,
    call2_store: IndexSet<(Ptr, Ptr, ContPtr)>,
    tail_store: IndexSet<(Ptr, ContPtr)>,
    lookup_store: IndexSet<(Ptr, ContPtr)>,
    unop_store: IndexSet<(Op1, ContPtr)>,
    binop_store: IndexSet<(Op2, Ptr, Ptr, ContPtr)>,
    binop2_store: IndexSet<(Op2, Ptr, ContPtr)>,
    relop_store: IndexSet<(Rel2, Ptr, Ptr, ContPtr)>,
    relop2_store: IndexSet<(Rel2, Ptr, ContPtr)>,
    if_store: IndexSet<(Ptr, ContPtr)>,
    let_star_store: IndexSet<(Ptr, Ptr, Ptr, ContPtr)>,
    let_rec_star_store: IndexSet<(Ptr, Ptr, Ptr, ContPtr)>,

    /// Holds a mapping of ScalarPtr -> Ptr for reverse lookups
    scalar_ptr_map: dashmap::DashMap<ScalarPtr, Ptr, ahash::RandomState>,
    /// Holds a mapping of ScalarPtr -> ContPtr for reverse lookups
    scalar_ptr_cont_map: dashmap::DashMap<ScalarContPtr, ContPtr, ahash::RandomState>,

    /// Caches poseidon hashes
    poseidon_cache: PoseidonCache,
}

#[derive(Default, Debug)]
struct PoseidonCache {
    a4: dashmap::DashMap<CacheKey<4>, Scalar, ahash::RandomState>,
    a6: dashmap::DashMap<CacheKey<6>, Scalar, ahash::RandomState>,
    a8: dashmap::DashMap<CacheKey<8>, Scalar, ahash::RandomState>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct CacheKey<const N: usize>([Scalar; N]);

#[allow(clippy::derive_hash_xor_eq)]
impl<const N: usize> Hash for CacheKey<N> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for el in &self.0 {
            el.to_repr().hash(state);
        }
    }
}

impl PoseidonCache {
    fn hash4(&self, preimage: &[Scalar; 4]) -> Scalar {
        let hash = self
            .a4
            .entry(CacheKey(*preimage))
            .or_insert_with(|| Poseidon::new_with_preimage(preimage, &POSEIDON_CONSTANTS_4).hash());
        *hash
    }

    fn hash6(&self, preimage: &[Scalar; 6]) -> Scalar {
        let hash = self
            .a6
            .entry(CacheKey(*preimage))
            .or_insert_with(|| Poseidon::new_with_preimage(preimage, &POSEIDON_CONSTANTS_6).hash());
        *hash
    }

    fn hash8(&self, preimage: &[Scalar; 8]) -> Scalar {
        let hash = self
            .a8
            .entry(CacheKey(*preimage))
            .or_insert_with(|| Poseidon::new_with_preimage(preimage, &POSEIDON_CONSTANTS_8).hash());
        *hash
    }
}

pub trait Object: fmt::Debug + Copy + Clone + PartialEq {
    type Pointer: Pointer;
}

pub trait Pointer: fmt::Debug + Copy + Clone + PartialEq + Hash {
    type Tag: Into<u64>;
    type ScalarPointer: ScalarPointer;

    fn tag(&self) -> Self::Tag;
    fn tag_field<F: From<u64> + ff::Field>(&self) -> F {
        F::from(self.tag().into())
    }
}

pub trait ScalarPointer: fmt::Debug + Copy + Clone + PartialEq + Hash {
    fn from_parts(tag: Scalar, value: Scalar) -> Self;
    fn tag(&self) -> &Scalar;
    fn value(&self) -> &Scalar;
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Ptr(Tag, RawPtr);

impl Ptr {
    pub const fn is_nil(&self) -> bool {
        matches!(self.0, Tag::Nil)
    }
}

impl Pointer for Ptr {
    type Tag = Tag;
    type ScalarPointer = ScalarPtr;

    fn tag(&self) -> Tag {
        self.0
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ScalarPtr(Scalar, Scalar);

#[allow(clippy::derive_hash_xor_eq)]
impl Hash for ScalarPtr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_repr().hash(state);
        self.1.to_repr().hash(state);
    }
}

impl ScalarPointer for ScalarPtr {
    fn from_parts(tag: Scalar, value: Scalar) -> Self {
        ScalarPtr(tag, value)
    }

    fn tag(&self) -> &Scalar {
        &self.0
    }

    fn value(&self) -> &Scalar {
        &self.1
    }
}

pub trait IntoHashComponents {
    fn into_hash_components(self) -> [Scalar; 2];
}

impl IntoHashComponents for [Scalar; 2] {
    fn into_hash_components(self) -> [Scalar; 2] {
        self
    }
}

impl IntoHashComponents for ScalarPtr {
    fn into_hash_components(self) -> [Scalar; 2] {
        [self.0, self.1]
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ScalarContPtr(Scalar, Scalar);

#[allow(clippy::derive_hash_xor_eq)]
impl Hash for ScalarContPtr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_repr().hash(state);
        self.1.to_repr().hash(state);
    }
}

impl ScalarPointer for ScalarContPtr {
    fn from_parts(tag: Scalar, value: Scalar) -> Self {
        ScalarContPtr(tag, value)
    }
    fn tag(&self) -> &Scalar {
        &self.0
    }

    fn value(&self) -> &Scalar {
        &self.1
    }
}

impl IntoHashComponents for ScalarContPtr {
    fn into_hash_components(self) -> [Scalar; 2] {
        [self.0, self.1]
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ContPtr(ContTag, RawPtr);

impl Pointer for ContPtr {
    type Tag = ContTag;
    type ScalarPointer = ScalarContPtr;

    fn tag(&self) -> Self::Tag {
        self.0
    }
}

impl ContPtr {
    pub const fn is_error(&self) -> bool {
        matches!(self.0, ContTag::Error)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct RawPtr(usize);

// Expressions, Continuations, Op1, Op2, and Rel2 occupy the same namespace in
// their encoding.
// As a 16bit integer their representation is as follows
//    [typ] [value       ]
// 0b 0000_ 0000_0000_0000
//
// where typ is
// - `0b0000` for Tag
// - `0b0001` for ContTag
// - `0b0010` for Op1
// - `0b0011` for Op2
// - `0b0100` for Rel2

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Expression<'a> {
    Nil,
    Cons(Ptr, Ptr),
    Sym(&'a str),
    /// arg, body, closed env
    Fun(Ptr, Ptr, Ptr),
    Num(Num),
    Str(&'a str),
    Thunk(Thunk),
}
impl Object for Expression<'_> {
    type Pointer = Ptr;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Thunk {
    pub(crate) value: Ptr,
    pub(crate) continuation: ContPtr,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Continuation {
    Outermost,
    Simple(ContPtr),
    /// The unevaluated argument and the saved env.
    Call(Ptr, Ptr, ContPtr),
    /// The function and the saved env.
    Call2(Ptr, Ptr, ContPtr),
    /// The saved env.
    Tail(Ptr, ContPtr),
    Error,
    /// The saved env.
    Lookup(Ptr, ContPtr),
    Unop(Op1, ContPtr),
    /// The saved env and unevaluated argument.
    Binop(Op2, Ptr, Ptr, ContPtr),
    /// First argument.
    Binop2(Op2, Ptr, ContPtr),
    /// The saved env and unevaluated arguments.
    Relop(Rel2, Ptr, Ptr, ContPtr),
    /// The first argument.
    Relop2(Rel2, Ptr, ContPtr),
    /// Unevaluated arguments.
    If(Ptr, ContPtr),
    /// The var, the body, and the saved env.
    LetStar(Ptr, Ptr, Ptr, ContPtr),
    /// The var, the saved env, and the body.
    LetRecStar(Ptr, Ptr, Ptr, ContPtr),
    Dummy,
    Terminal,
}

impl Object for Continuation {
    type Pointer = ContPtr;
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
#[repr(u16)]
pub enum Op1 {
    Car = 0b0010_0000_0000_0000,
    Cdr,
    Atom,
}

impl fmt::Display for Op1 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Op1::Car => write!(f, "Car"),
            Op1::Cdr => write!(f, "Cdr"),
            Op1::Atom => write!(f, "Atom"),
        }
    }
}

impl Op1 {
    pub fn as_field<F: From<u64> + ff::Field>(&self) -> F {
        F::from(*self as u64)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
#[repr(u16)]
pub enum Op2 {
    Sum = 0b0011_0000_0000_0000,
    Diff,
    Product,
    Quotient,
    Cons,
}

impl Op2 {
    pub fn as_field<F: From<u64> + ff::Field>(&self) -> F {
        F::from(*self as u64)
    }
}

impl fmt::Display for Op2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Op2::Sum => write!(f, "Sum"),
            Op2::Diff => write!(f, "Diff"),
            Op2::Product => write!(f, "Product"),
            Op2::Quotient => write!(f, "Quotient"),
            Op2::Cons => write!(f, "Cons"),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
#[repr(u16)]
pub enum Rel2 {
    Equal = 0b0100_0000_0000_0000,
    NumEqual,
}

impl Rel2 {
    pub fn as_field<F: From<u64> + ff::Field>(&self) -> F {
        F::from(*self as u64)
    }
}

impl fmt::Display for Rel2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rel2::Equal => write!(f, "Equal"),
            Rel2::NumEqual => write!(f, "NumEqual"),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum Tag {
    Nil = 0b0000_0000_0000_0000,
    Cons,
    Sym,
    Fun,
    Num,
    Thunk,
    Str,
}

impl From<Tag> for u64 {
    fn from(t: Tag) -> Self {
        t as u64
    }
}

impl Tag {
    pub fn as_field<F: From<u64> + ff::Field>(&self) -> F {
        F::from(*self as u64)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum ContTag {
    Outermost = 0b0001_0000_0000_0000,
    Simple,
    Call,
    Call2,
    Tail,
    Error,
    Lookup,
    Unop,
    Binop,
    Binop2,
    Relop,
    Relop2,
    If,
    LetStar,
    LetRecStar,
    Dummy,
    Terminal,
}

impl From<ContTag> for u64 {
    fn from(t: ContTag) -> Self {
        t as u64
    }
}

impl ContTag {
    pub fn as_field<F: From<u64> + ff::Field>(&self) -> F {
        F::from(*self as u64)
    }
}

// Expressions

const NIL: Expression = Expression::Nil;

// Continuations

const OUTERMOST: Continuation = Continuation::Outermost;
const ERROR: Continuation = Continuation::Error;
const DUMMY: Continuation = Continuation::Dummy;
const TERMINAL: Continuation = Continuation::Terminal;

impl Default for Store {
    fn default() -> Self {
        let mut store = Store {
            cons_store: Default::default(),
            sym_store: Default::default(),
            num_store: Default::default(),
            fun_store: Default::default(),
            str_store: Default::default(),
            thunk_store: Default::default(),
            simple_store: Default::default(),
            call_store: Default::default(),
            call2_store: Default::default(),
            tail_store: Default::default(),
            lookup_store: Default::default(),
            unop_store: Default::default(),
            binop_store: Default::default(),
            binop2_store: Default::default(),
            relop_store: Default::default(),
            relop2_store: Default::default(),
            if_store: Default::default(),
            let_star_store: Default::default(),
            let_rec_star_store: Default::default(),
            scalar_ptr_map: Default::default(),
            scalar_ptr_cont_map: Default::default(),
            poseidon_cache: Default::default(),
        };

        // insert some well known symbols
        for sym in &[
            "nil",
            "t",
            "quote",
            "lambda",
            "_",
            "let*",
            "letrec*",
            "car",
            "cdr",
            "atom",
            "+",
            "-",
            "*",
            "/",
            "=",
            "eq",
            "current-env",
            "if",
            "terminal",
            "dummy",
            "outermost",
            "error",
        ] {
            store.sym(sym);
        }

        store
    }
}

/// These methods provide a more ergonomic means of constructing and manipulating Lurk data.
/// They can be thought of as a minimal DSL for working with Lurk data in Rust code.
/// Prefer these methods when constructing literal data or assembling program fragments in
/// tests or during evaluation, etc.
impl Store {
    pub fn nil(&mut self) -> Ptr {
        self.intern_nil()
    }

    pub fn t(&mut self) -> Ptr {
        self.sym("T")
    }

    pub fn cons(&mut self, car: Ptr, cdr: Ptr) -> Ptr {
        self.intern_cons(car, cdr)
    }

    pub fn list(&mut self, elts: &[Ptr]) -> Ptr {
        self.intern_list(elts)
    }

    pub fn num<T: Into<Num>>(&mut self, num: T) -> Ptr {
        self.intern_num(num)
    }

    pub fn sym<T: AsRef<str>>(&mut self, name: T) -> Ptr {
        self.intern_sym_with_case_conversion(name)
    }

    pub fn car(&self, expr: &Ptr) -> Ptr {
        self.car_cdr(expr).0
    }

    pub fn cdr(&self, expr: &Ptr) -> Ptr {
        self.car_cdr(expr).1
    }
}

impl Store {
    pub fn new() -> Self {
        Store::default()
    }

    pub fn intern_nil(&mut self) -> Ptr {
        self.sym("nil")
    }

    pub fn get_nil(&self) -> Ptr {
        self.get_sym("nil", true).expect("missing NIL")
    }

    pub fn get_t(&self) -> Ptr {
        self.get_sym("t", true).expect("missing T")
    }

    pub fn intern_cons(&mut self, car: Ptr, cdr: Ptr) -> Ptr {
        let (ptr, _) = self.cons_store.insert_full((car, cdr));
        Ptr(Tag::Cons, RawPtr(ptr))
    }

    /// Helper to allocate a list, instead of manually using `cons`.
    pub fn intern_list(&mut self, elts: &[Ptr]) -> Ptr {
        elts.iter()
            .rev()
            .fold(self.sym("nil"), |acc, elt| self.cons(*elt, acc))
    }

    pub fn intern_sym_with_case_conversion<T: AsRef<str>>(&mut self, name: T) -> Ptr {
        let mut name = name.as_ref().to_string();
        Self::convert_sym_case(&mut name);

        self.intern_sym(name)
    }

    pub fn intern_sym<T: AsRef<str>>(&mut self, name: T) -> Ptr {
        let name = name.as_ref().to_string();

        let tag = if name == "NIL" { Tag::Nil } else { Tag::Sym };
        let ptr = self.sym_store.0.get_or_intern(name);

        Ptr(tag, RawPtr(ptr.to_usize()))
    }

    pub fn get_sym<T: AsRef<str>>(&self, name: T, convert_case: bool) -> Option<Ptr> {
        // TODO: avoid allocation
        let mut name = name.as_ref().to_string();
        if convert_case {
            Self::convert_sym_case(&mut name);
        }

        let tag = if name == "NIL" { Tag::Nil } else { Tag::Sym };
        self.sym_store
            .0
            .get(name)
            .map(|raw| Ptr(tag, RawPtr(raw.to_usize())))
    }

    pub fn intern_num<T: Into<Num>>(&mut self, num: T) -> Ptr {
        let (ptr, _) = self.num_store.insert_full(num.into());
        Ptr(Tag::Num, RawPtr(ptr))
    }

    pub fn intern_str<T: AsRef<str>>(&mut self, name: T) -> Ptr {
        let ptr = self.str_store.0.get_or_intern(name);
        Ptr(Tag::Str, RawPtr(ptr.to_usize()))
    }

    pub fn get_str<T: AsRef<str>>(&self, name: T) -> Option<Ptr> {
        let ptr = self.str_store.0.get(name)?;
        Some(Ptr(Tag::Str, RawPtr(ptr.to_usize())))
    }

    pub fn intern_fun(&mut self, arg: Ptr, body: Ptr, closed_env: Ptr) -> Ptr {
        // TODO: closed_env must be an env
        assert!(matches!(arg.0, Tag::Sym), "ARG must be a symbol");

        let (ptr, _) = self.fun_store.insert_full((arg, body, closed_env));
        Ptr(Tag::Fun, RawPtr(ptr))
    }

    pub fn intern_thunk(&mut self, thunk: Thunk) -> Ptr {
        let (ptr, _) = self.thunk_store.insert_full(thunk);
        Ptr(Tag::Thunk, RawPtr(ptr))
    }

    pub fn intern_cont_outermost(&self) -> ContPtr {
        self.get_cont_outermost()
    }

    pub fn get_cont_outermost(&self) -> ContPtr {
        let ptr = self.sym_store.0.get("OUTERMOST").expect("pre stored");
        ContPtr(ContTag::Outermost, RawPtr(ptr.to_usize()))
    }

    pub fn intern_cont_call(&mut self, a: Ptr, b: Ptr, c: ContPtr) -> ContPtr {
        let (ptr, _) = self.call_store.insert_full((a, b, c));
        ContPtr(ContTag::Call, RawPtr(ptr))
    }

    pub fn intern_cont_call2(&mut self, a: Ptr, b: Ptr, c: ContPtr) -> ContPtr {
        let (ptr, _) = self.call2_store.insert_full((a, b, c));
        ContPtr(ContTag::Call2, RawPtr(ptr))
    }

    pub fn intern_cont_error(&self) -> ContPtr {
        self.get_cont_error()
    }

    pub fn get_cont_error(&self) -> ContPtr {
        let ptr = self.sym_store.0.get("ERROR").expect("pre stored");
        ContPtr(ContTag::Error, RawPtr(ptr.to_usize()))
    }

    pub fn intern_cont_terminal(&self) -> ContPtr {
        self.get_cont_terminal()
    }

    pub fn get_cont_terminal(&self) -> ContPtr {
        let ptr = self.sym_store.0.get("TERMINAL").expect("pre stored");
        ContPtr(ContTag::Terminal, RawPtr(ptr.to_usize()))
    }

    pub fn intern_cont_dummy(&self) -> ContPtr {
        self.get_cont_dummy()
    }

    pub fn get_cont_dummy(&self) -> ContPtr {
        let ptr = self.sym_store.0.get("DUMMY").expect("pre stored");
        ContPtr(ContTag::Dummy, RawPtr(ptr.to_usize()))
    }

    pub fn intern_cont_lookup(&mut self, a: Ptr, b: ContPtr) -> ContPtr {
        let (ptr, _) = self.lookup_store.insert_full((a, b));
        ContPtr(ContTag::Lookup, RawPtr(ptr))
    }

    pub fn intern_cont_let_star(&mut self, a: Ptr, b: Ptr, c: Ptr, d: ContPtr) -> ContPtr {
        let (ptr, _) = self.let_star_store.insert_full((a, b, c, d));
        ContPtr(ContTag::LetStar, RawPtr(ptr))
    }

    pub fn intern_cont_let_rec_star(&mut self, a: Ptr, b: Ptr, c: Ptr, d: ContPtr) -> ContPtr {
        let (ptr, _) = self.let_rec_star_store.insert_full((a, b, c, d));
        ContPtr(ContTag::LetRecStar, RawPtr(ptr))
    }

    pub fn intern_cont_unop(&mut self, op: Op1, a: ContPtr) -> ContPtr {
        let (ptr, _) = self.unop_store.insert_full((op, a));
        ContPtr(ContTag::Unop, RawPtr(ptr))
    }

    pub fn intern_cont_binop(&mut self, op: Op2, a: Ptr, b: Ptr, c: ContPtr) -> ContPtr {
        let (ptr, _) = self.binop_store.insert_full((op, a, b, c));
        ContPtr(ContTag::Binop, RawPtr(ptr))
    }

    pub fn intern_cont_binop2(&mut self, op: Op2, a: Ptr, b: ContPtr) -> ContPtr {
        let (ptr, _) = self.binop2_store.insert_full((op, a, b));
        ContPtr(ContTag::Binop2, RawPtr(ptr))
    }

    pub fn intern_cont_relop(&mut self, op: Rel2, a: Ptr, b: Ptr, c: ContPtr) -> ContPtr {
        let (ptr, _) = self.relop_store.insert_full((op, a, b, c));
        ContPtr(ContTag::Relop, RawPtr(ptr))
    }

    pub fn intern_cont_relop2(&mut self, op: Rel2, a: Ptr, b: ContPtr) -> ContPtr {
        let (ptr, _) = self.relop2_store.insert_full((op, a, b));
        ContPtr(ContTag::Relop2, RawPtr(ptr))
    }

    pub fn intern_cont_if(&mut self, a: Ptr, b: ContPtr) -> ContPtr {
        let (ptr, _) = self.if_store.insert_full((a, b));
        ContPtr(ContTag::If, RawPtr(ptr))
    }

    pub fn intern_cont_tail(&mut self, a: Ptr, b: ContPtr) -> ContPtr {
        let (ptr, _) = self.tail_store.insert_full((a, b));
        ContPtr(ContTag::Tail, RawPtr(ptr))
    }

    pub fn scalar_from_parts(&self, tag: Scalar, value: Scalar) -> Option<ScalarPtr> {
        let scalar_ptr = ScalarPtr(tag, value);
        if self.scalar_ptr_map.contains_key(&scalar_ptr) {
            return Some(scalar_ptr);
        }

        None
    }

    pub fn scalar_from_parts_cont(&self, tag: Scalar, value: Scalar) -> Option<ScalarContPtr> {
        let scalar_ptr = ScalarContPtr(tag, value);
        if self.scalar_ptr_cont_map.contains_key(&scalar_ptr) {
            return Some(scalar_ptr);
        }
        None
    }

    pub fn fetch_scalar(&self, scalar_ptr: &ScalarPtr) -> Option<Ptr> {
        self.scalar_ptr_map.get(scalar_ptr).map(|p| *p)
    }

    pub fn fetch_scalar_cont(&self, scalar_ptr: &ScalarContPtr) -> Option<ContPtr> {
        self.scalar_ptr_cont_map.get(scalar_ptr).map(|p| *p)
    }

    fn fetch_sym(&self, ptr: &Ptr) -> Option<&str> {
        debug_assert!(matches!(ptr.0, Tag::Sym) | matches!(ptr.0, Tag::Nil));
        if ptr.0 == Tag::Nil {
            return Some("NIL");
        }

        self.sym_store
            .0
            .resolve(SymbolUsize::try_from_usize(ptr.1 .0).unwrap())
    }

    fn fetch_str(&self, ptr: &Ptr) -> Option<&str> {
        debug_assert!(matches!(ptr.0, Tag::Str));
        let symbol = SymbolUsize::try_from_usize(ptr.1 .0).expect("invalid pointer");
        self.str_store.0.resolve(symbol)
    }

    fn fetch_fun(&self, ptr: &Ptr) -> Option<&(Ptr, Ptr, Ptr)> {
        debug_assert!(matches!(ptr.0, Tag::Fun));
        self.fun_store.get_index(ptr.1 .0)
    }

    fn fetch_cons(&self, ptr: &Ptr) -> Option<&(Ptr, Ptr)> {
        debug_assert!(matches!(ptr.0, Tag::Cons));
        self.cons_store.get_index(ptr.1 .0)
    }

    fn fetch_num(&self, ptr: &Ptr) -> Option<&Num> {
        debug_assert!(matches!(ptr.0, Tag::Num));
        self.num_store.get_index(ptr.1 .0)
    }

    fn fetch_thunk(&self, ptr: &Ptr) -> Option<&Thunk> {
        debug_assert!(matches!(ptr.0, Tag::Thunk));
        self.thunk_store.get_index(ptr.1 .0)
    }

    pub fn fetch(&self, ptr: &Ptr) -> Option<Expression> {
        match ptr.0 {
            Tag::Nil => Some(NIL),
            Tag::Cons => self.fetch_cons(ptr).map(|(a, b)| Expression::Cons(*a, *b)),
            Tag::Sym => self.fetch_sym(ptr).map(Expression::Sym),
            Tag::Num => self.fetch_num(ptr).map(|num| Expression::Num(*num)),
            Tag::Fun => self
                .fetch_fun(ptr)
                .map(|(a, b, c)| Expression::Fun(*a, *b, *c)),
            Tag::Thunk => self.fetch_thunk(ptr).map(|thunk| Expression::Thunk(*thunk)),
            Tag::Str => self.fetch_str(ptr).map(Expression::Str),
        }
    }

    pub fn fetch_cont(&self, ptr: &ContPtr) -> Option<Continuation> {
        use ContTag::*;
        match ptr.0 {
            Outermost => Some(OUTERMOST),
            Simple => self
                .simple_store
                .get_index(ptr.1 .0)
                .map(|a| Continuation::Simple(*a)),
            Call => self
                .call_store
                .get_index(ptr.1 .0)
                .map(|(a, b, c)| Continuation::Call(*a, *b, *c)),
            Call2 => self
                .call2_store
                .get_index(ptr.1 .0)
                .map(|(a, b, c)| Continuation::Call2(*a, *b, *c)),
            Tail => self
                .tail_store
                .get_index(ptr.1 .0)
                .map(|(a, b)| Continuation::Tail(*a, *b)),
            Error => Some(ERROR),
            Lookup => self
                .lookup_store
                .get_index(ptr.1 .0)
                .map(|(a, b)| Continuation::Lookup(*a, *b)),
            Unop => self
                .unop_store
                .get_index(ptr.1 .0)
                .map(|(a, b)| Continuation::Unop(*a, *b)),
            Binop => self
                .binop_store
                .get_index(ptr.1 .0)
                .map(|(a, b, c, d)| Continuation::Binop(*a, *b, *c, *d)),
            Binop2 => self
                .binop2_store
                .get_index(ptr.1 .0)
                .map(|(a, b, c)| Continuation::Binop2(*a, *b, *c)),
            Relop => self
                .relop_store
                .get_index(ptr.1 .0)
                .map(|(a, b, c, d)| Continuation::Relop(*a, *b, *c, *d)),
            Relop2 => self
                .relop2_store
                .get_index(ptr.1 .0)
                .map(|(a, b, c)| Continuation::Relop2(*a, *b, *c)),
            If => self
                .if_store
                .get_index(ptr.1 .0)
                .map(|(a, b)| Continuation::If(*a, *b)),
            LetStar => self
                .let_star_store
                .get_index(ptr.1 .0)
                .map(|(a, b, c, d)| Continuation::LetStar(*a, *b, *c, *d)),
            LetRecStar => self
                .let_rec_star_store
                .get_index(ptr.1 .0)
                .map(|(a, b, c, d)| Continuation::LetRecStar(*a, *b, *c, *d)),
            Dummy => Some(DUMMY),
            Terminal => Some(TERMINAL),
        }
    }

    pub fn car_cdr(&self, ptr: &Ptr) -> (Ptr, Ptr) {
        match ptr.0 {
            Tag::Nil => (self.get_nil(), self.get_nil()),
            Tag::Cons => match self.fetch(ptr) {
                Some(Expression::Cons(car, cdr)) => (car, cdr),
                _ => unreachable!(),
            },
            _ => panic!("Can only extract car_cdr from Cons"),
        }
    }

    pub fn hash_expr(&self, ptr: &Ptr) -> Option<ScalarPtr> {
        use Tag::*;
        match ptr.tag() {
            Nil => self.hash_nil(),
            Cons => self.hash_cons(*ptr),
            Sym => self.hash_sym(*ptr),
            Fun => self.hash_fun(*ptr),
            Num => self.hash_num(*ptr),
            Str => self.hash_str(*ptr),
            Thunk => self.hash_thunk(*ptr),
        }
    }

    pub fn hash_cont(&self, ptr: &ContPtr) -> Option<ScalarContPtr> {
        let components = self.get_hash_components_cont(ptr)?;
        let hash = self.poseidon_cache.hash8(&components);

        Some(self.create_cont_scalar_ptr(*ptr, hash))
    }

    /// The only places that `ScalarPtr`s for `Ptr`s should be created, to
    /// ensure that they are cached properly
    fn create_scalar_ptr(&self, ptr: Ptr, hash: Scalar) -> ScalarPtr {
        let scalar_ptr = ScalarPtr(ptr.tag_field(), hash);
        self.scalar_ptr_map.entry(scalar_ptr).or_insert(ptr);
        scalar_ptr
    }

    /// The only places that `ScalarContPtr`s for `ContPtr`s should be created, to
    /// ensure that they are cached properly
    fn create_cont_scalar_ptr(&self, ptr: ContPtr, hash: Scalar) -> ScalarContPtr {
        let scalar_ptr = ScalarContPtr(ptr.tag_field(), hash);
        self.scalar_ptr_cont_map.entry(scalar_ptr).or_insert(ptr);

        scalar_ptr
    }

    fn get_hash_components_default(&self) -> [[Scalar; 2]; 4] {
        let def = [Scalar::zero(), Scalar::zero()];
        [def, def, def, def]
    }

    fn get_hash_components_simple(&self, cont: &ContPtr) -> Option<[[Scalar; 2]; 4]> {
        let def = [Scalar::zero(), Scalar::zero()];
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([cont, def, def, def])
    }

    pub fn get_hash_components_cont(&self, ptr: &ContPtr) -> Option<[Scalar; 8]> {
        use Continuation::*;

        let cont = self.fetch_cont(ptr)?;

        let hash = match &cont {
            Outermost | Dummy | Terminal | Error => self.get_hash_components_default(),
            Simple(ref cont) => self.get_hash_components_simple(cont)?,
            Call(arg, saved_env, cont) => self.get_hash_components_call(arg, saved_env, cont)?,
            Call2(fun, saved_env, cont) => self.get_hash_components_call2(fun, saved_env, cont)?,
            Tail(saved_env, cont) => self.get_hash_components_tail(saved_env, cont)?,
            Lookup(saved_env, cont) => self.get_hash_components_lookup(saved_env, cont)?,
            Unop(op, cont) => self.get_hash_components_unop(op, cont)?,
            Binop(op, saved_env, unevaled_args, cont) => {
                self.get_hash_components_binop(op, saved_env, unevaled_args, cont)?
            }
            Binop2(op, arg1, cont) => self.get_hash_components_binop2(op, arg1, cont)?,
            Relop(rel, saved_env, unevaled_args, cont) => {
                self.get_hash_components_relop(rel, saved_env, unevaled_args, cont)?
            }
            Relop2(rel, arg1, cont) => self.get_hash_components_relop2(rel, arg1, cont)?,
            If(unevaled_args, cont) => self.get_hash_components_if(unevaled_args, cont)?,
            LetStar(var, body, saved_env, cont) => {
                self.get_hash_components_let_star(var, body, saved_env, cont)?
            }
            LetRecStar(var, body, saved_env, cont) => {
                self.get_hash_components_let_rec_star(var, body, saved_env, cont)?
            }
        };

        Some([
            hash[0][0], hash[0][1], hash[1][0], hash[1][1], hash[2][0], hash[2][1], hash[3][0],
            hash[3][1],
        ])
    }

    fn get_hash_components_let_rec_star(
        &self,
        var: &Ptr,
        body: &Ptr,
        saved_env: &Ptr,
        cont: &ContPtr,
    ) -> Option<[[Scalar; 2]; 4]> {
        let var = self.hash_expr(var)?.into_hash_components();
        let body = self.hash_expr(body)?.into_hash_components();
        let saved_env = self.hash_expr(saved_env)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([var, body, saved_env, cont])
    }

    fn get_hash_components_let_star(
        &self,
        var: &Ptr,
        body: &Ptr,
        saved_env: &Ptr,
        cont: &ContPtr,
    ) -> Option<[[Scalar; 2]; 4]> {
        let var = self.hash_expr(var)?.into_hash_components();
        let body = self.hash_expr(body)?.into_hash_components();
        let saved_env = self.hash_expr(saved_env)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([var, body, saved_env, cont])
    }

    fn get_hash_components_if(
        &self,
        unevaled_args: &Ptr,
        cont: &ContPtr,
    ) -> Option<[[Scalar; 2]; 4]> {
        let def = [Scalar::zero(), Scalar::zero()];
        let unevaled_args = self.hash_expr(unevaled_args)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([unevaled_args, cont, def, def])
    }

    fn get_hash_components_relop2(
        &self,
        rel: &Rel2,
        arg1: &Ptr,
        cont: &ContPtr,
    ) -> Option<[[Scalar; 2]; 4]> {
        let def = [Scalar::zero(), Scalar::zero()];
        let rel = self.hash_rel2(rel).into_hash_components();
        let arg1 = self.hash_expr(arg1)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([rel, arg1, cont, def])
    }

    fn get_hash_components_relop(
        &self,
        rel: &Rel2,
        saved_env: &Ptr,
        unevaled_args: &Ptr,
        cont: &ContPtr,
    ) -> Option<[[Scalar; 2]; 4]> {
        let rel = self.hash_rel2(rel).into_hash_components();
        let saved_env = self.hash_expr(saved_env)?.into_hash_components();
        let unevaled_args = self.hash_expr(unevaled_args)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([rel, saved_env, unevaled_args, cont])
    }

    fn get_hash_components_binop2(
        &self,
        op: &Op2,
        arg1: &Ptr,
        cont: &ContPtr,
    ) -> Option<[[Scalar; 2]; 4]> {
        let def = [Scalar::zero(), Scalar::zero()];
        let op = self.hash_op2(op).into_hash_components();
        let arg1 = self.hash_expr(arg1)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([op, arg1, cont, def])
    }

    fn get_hash_components_binop(
        &self,
        op: &Op2,
        saved_env: &Ptr,
        unevaled_args: &Ptr,
        cont: &ContPtr,
    ) -> Option<[[Scalar; 2]; 4]> {
        let op = self.hash_op2(op).into_hash_components();
        let saved_env = self.hash_expr(saved_env)?.into_hash_components();
        let unevaled_args = self.hash_expr(unevaled_args)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([op, saved_env, unevaled_args, cont])
    }

    fn get_hash_components_unop(&self, op: &Op1, cont: &ContPtr) -> Option<[[Scalar; 2]; 4]> {
        let def = [Scalar::zero(), Scalar::zero()];
        let op = self.hash_op1(op).into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([op, cont, def, def])
    }

    fn get_hash_components_lookup(
        &self,
        saved_env: &Ptr,
        cont: &ContPtr,
    ) -> Option<[[Scalar; 2]; 4]> {
        let def = [Scalar::zero(), Scalar::zero()];
        let saved_env = self.hash_expr(saved_env)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([saved_env, cont, def, def])
    }

    fn get_hash_components_tail(
        &self,
        saved_env: &Ptr,
        cont: &ContPtr,
    ) -> Option<[[Scalar; 2]; 4]> {
        let def = [Scalar::zero(), Scalar::zero()];
        let saved_env = self.hash_expr(saved_env)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([saved_env, cont, def, def])
    }

    fn get_hash_components_call2(
        &self,
        fun: &Ptr,
        saved_env: &Ptr,
        cont: &ContPtr,
    ) -> Option<[[Scalar; 2]; 4]> {
        let def = [Scalar::zero(), Scalar::zero()];
        let fun = self.hash_expr(fun)?.into_hash_components();
        let saved_env = self.hash_expr(saved_env)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();
        Some([saved_env, fun, cont, def])
    }

    fn get_hash_components_call(
        &self,
        arg: &Ptr,
        saved_env: &Ptr,
        cont: &ContPtr,
    ) -> Option<[[Scalar; 2]; 4]> {
        let def = [Scalar::zero(), Scalar::zero()];

        let arg = self.hash_expr(arg)?.into_hash_components();
        let saved_env = self.hash_expr(saved_env)?.into_hash_components();
        let cont = self.hash_cont(cont)?.into_hash_components();

        Some([saved_env, arg, cont, def])
    }

    pub fn get_hash_components_thunk(&self, thunk: &Thunk) -> Option<[Scalar; 4]> {
        let value_hash = self.hash_expr(&thunk.value)?.into_hash_components();
        let continuation_hash = self.hash_cont(&thunk.continuation)?.into_hash_components();

        Some([
            value_hash[0],
            value_hash[1],
            continuation_hash[0],
            continuation_hash[1],
        ])
    }

    pub fn hash_sym(&self, sym: Ptr) -> Option<ScalarPtr> {
        let s = self.fetch_sym(&sym)?;
        Some(self.create_scalar_ptr(sym, self.hash_string(s)))
    }

    fn hash_str(&self, sym: Ptr) -> Option<ScalarPtr> {
        let s = self.fetch_str(&sym)?;
        Some(self.create_scalar_ptr(sym, self.hash_string(s)))
    }

    fn hash_fun(&self, fun: Ptr) -> Option<ScalarPtr> {
        let (arg, body, closed_env) = self.fetch_fun(&fun)?;
        Some(self.create_scalar_ptr(fun, self.hash_ptrs_3(&[*arg, *body, *closed_env])?))
    }

    fn hash_cons(&self, cons: Ptr) -> Option<ScalarPtr> {
        let (car, cdr) = self.fetch_cons(&cons)?;
        Some(self.create_scalar_ptr(cons, self.hash_ptrs_2(&[*car, *cdr])?))
    }

    fn hash_thunk(&self, ptr: Ptr) -> Option<ScalarPtr> {
        let thunk = self.fetch_thunk(&ptr)?;
        let components = self.get_hash_components_thunk(thunk)?;
        Some(self.create_scalar_ptr(ptr, self.poseidon_cache.hash4(&components)))
    }

    fn hash_num(&self, ptr: Ptr) -> Option<ScalarPtr> {
        let n = self.fetch_num(&ptr)?;
        Some(self.create_scalar_ptr(ptr, Scalar::from(*n)))
    }

    fn hash_string(&self, s: &str) -> Scalar {
        // We should use HashType::VariableLength, once supported.
        // The following is just quick and dirty, but should be unique.
        let mut preimage = [Scalar::zero(); 8];
        let mut x = Scalar::from(s.len() as u64);
        s.chars()
            .map(|c| Scalar::from(c as u64))
            .chunks(7)
            .into_iter()
            .for_each(|mut chunk| {
                preimage[0] = x;
                for item in preimage.iter_mut().skip(1).take(7) {
                    if let Some(c) = chunk.next() {
                        *item = c
                    };
                }
                x = self.poseidon_cache.hash8(&preimage)
            });
        x
    }

    fn hash_ptrs_2(&self, ptrs: &[Ptr; 2]) -> Option<Scalar> {
        let scalar_ptrs = [self.hash_expr(&ptrs[0])?, self.hash_expr(&ptrs[1])?];
        Some(self.hash_scalar_ptrs_2(&scalar_ptrs))
    }

    fn hash_ptrs_3(&self, ptrs: &[Ptr; 3]) -> Option<Scalar> {
        let scalar_ptrs = [
            self.hash_expr(&ptrs[0])?,
            self.hash_expr(&ptrs[1])?,
            self.hash_expr(&ptrs[2])?,
        ];
        Some(self.hash_scalar_ptrs_3(&scalar_ptrs))
    }

    fn hash_scalar_ptrs_2(&self, ptrs: &[ScalarPtr; 2]) -> Scalar {
        let preimage = [ptrs[0].0, ptrs[0].1, ptrs[1].0, ptrs[1].1];
        self.poseidon_cache.hash4(&preimage)
    }

    fn hash_scalar_ptrs_3(&self, ptrs: &[ScalarPtr; 3]) -> Scalar {
        let preimage = [
            ptrs[0].0, ptrs[0].1, ptrs[1].0, ptrs[1].1, ptrs[2].0, ptrs[2].1,
        ];
        self.poseidon_cache.hash6(&preimage)
    }

    pub fn hash_nil(&self) -> Option<ScalarPtr> {
        let nil = self.get_nil();
        self.hash_sym(nil)
    }

    fn hash_op1(&self, op: &Op1) -> ScalarPtr {
        ScalarPtr(op.as_field(), Scalar::zero())
    }

    fn hash_op2(&self, op: &Op2) -> ScalarPtr {
        ScalarPtr(op.as_field(), Scalar::zero())
    }

    fn hash_rel2(&self, op: &Rel2) -> ScalarPtr {
        ScalarPtr(op.as_field(), Scalar::zero())
    }

    /// Fill the cache for Scalars.
    pub fn hydrate_scalar_cache(&self) {
        println!("hydrating scalar cache");

        self.cons_store.par_iter().for_each(|(car, cdr)| {
            self.hash_ptrs_2(&[*car, *cdr]);
        });

        self.sym_store.0.into_iter().for_each(|(_, sym)| {
            self.hash_string(sym);
        });

        // Nums are not hashed, they are their own hash.

        self.fun_store
            .par_iter()
            .for_each(|(arg, body, closed_env)| {
                self.hash_ptrs_3(&[*arg, *body, *closed_env]);
            });

        self.str_store.0.into_iter().for_each(|(_, name)| {
            self.hash_string(name);
        });

        self.thunk_store.par_iter().for_each(|thunk| {
            if let Some(components) = self.get_hash_components_thunk(thunk) {
                self.poseidon_cache.hash4(&components);
            }
        });

        // Continuations are all 8 components
        let simple = self
            .simple_store
            .par_iter()
            .filter_map(|c| self.get_hash_components_simple(c));
        let call = self
            .call_store
            .par_iter()
            .filter_map(|(a, b, c)| self.get_hash_components_call(a, b, c));
        let call2 = self
            .call2_store
            .par_iter()
            .filter_map(|(a, b, c)| self.get_hash_components_call2(a, b, c));

        let tail = self
            .tail_store
            .par_iter()
            .filter_map(|(a, b)| self.get_hash_components_tail(a, b));

        let lookup = self
            .lookup_store
            .par_iter()
            .filter_map(|(a, b)| self.get_hash_components_lookup(a, b));

        let unop = self
            .unop_store
            .par_iter()
            .filter_map(|(a, b)| self.get_hash_components_unop(a, b));

        let binop = self
            .binop_store
            .par_iter()
            .filter_map(|(a, b, c, d)| self.get_hash_components_binop(a, b, c, d));

        let binop2 = self
            .binop2_store
            .par_iter()
            .filter_map(|(a, b, c)| self.get_hash_components_binop2(a, b, c));

        let relop = self
            .relop_store
            .par_iter()
            .filter_map(|(a, b, c, d)| self.get_hash_components_relop(a, b, c, d));

        let relop2 = self
            .relop2_store
            .par_iter()
            .filter_map(|(a, b, c)| self.get_hash_components_relop2(a, b, c));

        let ifi = self
            .if_store
            .par_iter()
            .filter_map(|(a, b)| self.get_hash_components_if(a, b));

        let let_star = self
            .let_star_store
            .par_iter()
            .filter_map(|(a, b, c, d)| self.get_hash_components_let_star(a, b, c, d));

        let let_rec_star = self
            .let_rec_star_store
            .par_iter()
            .filter_map(|(a, b, c, d)| self.get_hash_components_let_rec_star(a, b, c, d));

        let chain = simple
            .chain(call)
            .chain(call2)
            .chain(tail)
            .chain(lookup)
            .chain(unop)
            .chain(binop)
            .chain(binop2)
            .chain(relop)
            .chain(relop2)
            .chain(ifi)
            .chain(let_star)
            .chain(let_rec_star);

        chain.for_each(|el| {
            self.poseidon_cache.hash8(&[
                el[0][0], el[0][1], el[1][0], el[1][1], el[2][0], el[2][1], el[3][0], el[3][1],
            ]);
        });

        println!("cache hydrated");
    }
}

impl Expression<'_> {
    pub fn is_keyword_sym(&self) -> bool {
        match self {
            Expression::Sym(s) => s.starts_with(':'),
            _ => false,
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Expression::Str(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_sym_str(&self) -> Option<&str> {
        match self {
            Expression::Sym(s) => Some(s),
            _ => None,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::writer::Write;

    use super::*;

    #[test]
    fn test_print_num() {
        let mut store = Store::default();
        let num = store.num(5);
        let res = num.fmt_to_string(&store);
        assert_eq!(&res, &"Num(0x5)");
    }

    #[test]
    fn tag_vals() {
        assert_eq!(0, Tag::Nil as u64);
        assert_eq!(1, Tag::Cons as u64);
        assert_eq!(2, Tag::Sym as u64);
        assert_eq!(3, Tag::Fun as u64);
        assert_eq!(4, Tag::Num as u64);
        assert_eq!(5, Tag::Thunk as u64);
        assert_eq!(6, Tag::Str as u64);
    }

    #[test]
    fn cont_tag_vals() {
        use super::ContTag::*;

        assert_eq!(0b0001_0000_0000_0000, Outermost as u16);
        assert_eq!(0b0001_0000_0000_0001, Simple as u16);
        assert_eq!(0b0001_0000_0000_0010, Call as u16);
        assert_eq!(0b0001_0000_0000_0011, Call2 as u16);
        assert_eq!(0b0001_0000_0000_0100, Tail as u16);
        assert_eq!(0b0001_0000_0000_0101, Error as u16);
        assert_eq!(0b0001_0000_0000_0110, Lookup as u16);
        assert_eq!(0b0001_0000_0000_0111, Unop as u16);
        assert_eq!(0b0001_0000_0000_1000, Binop as u16);
        assert_eq!(0b0001_0000_0000_1001, Binop2 as u16);
        assert_eq!(0b0001_0000_0000_1010, Relop as u16);
        assert_eq!(0b0001_0000_0000_1011, Relop2 as u16);
        assert_eq!(0b0001_0000_0000_1100, If as u16);
        assert_eq!(0b0001_0000_0000_1101, LetStar as u16);
        assert_eq!(0b0001_0000_0000_1110, LetRecStar as u16);
        assert_eq!(0b0001_0000_0000_1111, Dummy as u16);
        assert_eq!(0b0001_0000_0001_0000, Terminal as u16);
    }

    #[test]
    fn store() {
        let mut store = Store::default();

        let num_ptr = store.num(123);
        let num = store.fetch(&num_ptr).unwrap();
        let num_again = store.fetch(&num_ptr).unwrap();

        assert_eq!(num, num_again);
    }

    #[test]
    fn equality() {
        let mut store = Store::default();

        let (a, b) = (store.num(123), store.sym("pumpkin"));
        let cons1 = store.intern_cons(a, b);
        let (a, b) = (store.num(123), store.sym("pumpkin"));
        let cons2 = store.intern_cons(a, b);

        assert_eq!(cons1, cons2);
        assert_eq!(store.car(&cons1), store.car(&cons2));
        assert_eq!(store.cdr(&cons1), store.cdr(&cons2));

        let (a, d) = store.car_cdr(&cons1);
        assert_eq!(store.car(&cons1), a);
        assert_eq!(store.cdr(&cons1), d);
    }
}
