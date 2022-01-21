use blstrs::Scalar;
use ff::{Field, PrimeField};
use indexmap::Equivalent;
use itertools::Itertools;
use neptune::Poseidon;
use std::borrow::Borrow;
use std::fmt::{self, Display};
use std::hash::Hash;
use std::rc::Rc;

use generic_array::typenum::{U10, U11, U16, U2, U3, U4, U5, U6, U7, U8, U9};
use neptune::{hash_type::HashType, poseidon::PoseidonConstants, Strength};
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

#[derive(Debug, Default)]
pub struct Pool {
    cons_pool: IndexSet<(Ptr, Ptr)>,
    sym_pool: IndexSet<Str>,
    // Other sparse storage format without hashing is likely more efficient
    num_pool: IndexSet<u64>,
    fun_pool: IndexSet<(Ptr, Ptr, Ptr)>,
    str_pool: IndexSet<Str>,
    thunk_pool: IndexSet<Thunk>,

    simple_pool: IndexSet<ContPtr>,
    call_pool: IndexSet<(Ptr, Ptr, ContPtr)>,
    call2_pool: IndexSet<(Ptr, Ptr, ContPtr)>,
    tail_pool: IndexSet<(Ptr, ContPtr)>,
    lookup_pool: IndexSet<(Ptr, ContPtr)>,
    unop_pool: IndexSet<(Op1, ContPtr)>,
    binop_pool: IndexSet<(Op2, Ptr, Ptr, ContPtr)>,
    binop2_pool: IndexSet<(Op2, Ptr, ContPtr)>,
    relop_pool: IndexSet<(Rel2, Ptr, Ptr, ContPtr)>,
    relop2_pool: IndexSet<(Rel2, Ptr, ContPtr)>,
    if_pool: IndexSet<(Ptr, ContPtr)>,
    let_star_pool: IndexSet<(Ptr, Ptr, Ptr, ContPtr)>,
    let_rec_star_pool: IndexSet<(Ptr, Ptr, Ptr, ContPtr)>,

    /// Holds a mapping of ScalarPtr -> Ptr for reverese lookups
    scalar_ptr_map: ahash::AHashMap<ScalarPtr, Ptr>,
    /// Holds a mapping of ScalarPtr -> ContPtr for reverese lookups
    scalar_ptr_cont_map: ahash::AHashMap<ScalarPtr, ContPtr>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Ptr(Tag, RawPtr);

impl Ptr {
    pub const fn is_nil(&self) -> bool {
        matches!(self.0, Tag::Nil)
    }

    pub const fn tag(&self) -> Tag {
        self.0
    }

    pub fn tag_field<F: From<u64> + ff::Field>(&self) -> F {
        self.0.as_field()
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

impl ScalarPtr {
    pub(crate) const fn tag(&self) -> &Scalar {
        &self.0
    }

    pub(crate) const fn value(&self) -> &Scalar {
        &self.1
    }

    pub(crate) const fn from_parts(tag: Scalar, value: Scalar) -> Self {
        ScalarPtr(tag, value)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ContPtr(ContTag, RawPtr);

impl ContPtr {
    pub const fn is_error(&self) -> bool {
        matches!(self.0, ContTag::Error)
    }

    pub const fn tag(&self) -> ContTag {
        self.0
    }

    pub fn tag_field<F: From<u64> + ff::Field>(&self) -> F {
        self.0.as_field()
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct RawPtr(usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expression {
    Nil,
    Cons(Ptr, Ptr),
    Sym(Str),
    Fun(Ptr, Ptr, Ptr),
    Num(u64),
    Str(Str),
    Thunk(Thunk),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Thunk {
    pub(crate) value: Ptr,
    pub(crate) continuation: ContPtr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Continuation {
    Outermost,
    Simple(ContPtr),
    Call(Ptr, Ptr, ContPtr),
    Call2(Ptr, Ptr, ContPtr),
    Tail(Ptr, ContPtr),
    Error,
    Lookup(Ptr, ContPtr),
    Unop(Op1, ContPtr),
    Binop(Op2, Ptr, Ptr, ContPtr),
    Binop2(Op2, Ptr, ContPtr),
    Relop(Rel2, Ptr, Ptr, ContPtr),
    Relop2(Rel2, Ptr, ContPtr),
    If(Ptr, ContPtr),
    LetStar(Ptr, Ptr, Ptr, ContPtr),
    LetRecStar(Ptr, Ptr, Ptr, ContPtr),
    Dummy,
    Terminal,
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
pub enum Op1 {
    Car,
    Cdr,
    Atom,
}

impl fmt::Display for Op1 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Op1::Car => write!(f, "Car"),
            Op1::Cdr => write!(f, "Cddr"),
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
pub enum Op2 {
    Sum,
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
pub enum Rel2 {
    Equal,
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

/// Custom String type, that has cheap clone, to avoid duplicating strings.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Str(Rc<String>);

impl Display for Str {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.as_ref().fmt(f)
    }
}

impl From<String> for Str {
    fn from(s: String) -> Str {
        Str(Rc::new(s))
    }
}

impl From<&str> for Str {
    fn from(s: &str) -> Self {
        Str(Rc::new(s.to_string()))
    }
}

impl AsRef<str> for Str {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl Borrow<str> for Str {
    fn borrow(&self) -> &str {
        self.0.as_ref()
    }
}

pub trait ToStr {
    fn to_str(self) -> Str;
}

impl ToStr for Str {
    fn to_str(self) -> Str {
        self
    }
}

impl ToStr for &Str {
    fn to_str(self) -> Str {
        self.clone()
    }
}

impl ToStr for &str {
    fn to_str(self) -> Str {
        Str(Rc::new(self.to_string()))
    }
}

impl ToStr for String {
    fn to_str(self) -> Str {
        Str(Rc::new(self))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Tag {
    Nil,
    Cons,
    Sym,
    Fun,
    Num,
    Thunk,
    Str,
}

impl Tag {
    pub fn as_field<F: From<u64> + ff::Field>(&self) -> F {
        F::from(*self as u64)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ContTag {
    Outermost,
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

// For now, partition ContinuationTags into thunks and conts.
// If never used, we can collapse.
// We will likely want both if we ever make continuations (including
// thunks) first-class expressions, though.
impl ContTag {
    pub fn cont_tag_val(&self) -> u64 {
        2 * *self as u64
    }

    #[allow(dead_code)]
    fn thunk_tag_val(&self) -> u64 {
        1 + self.cont_tag_val()
    }

    pub fn as_field<F: From<u64> + ff::Field>(&self) -> F {
        F::from(*self as u64)
    }
}

// Expressions

const NIL: Expression = Expression::Nil;
const NIL_PTR: Ptr = Ptr(Tag::Nil, RawPtr(0));

// Continuations

const OUTERMOST: Continuation = Continuation::Outermost;
const OUTERMOST_PTR: ContPtr = ContPtr(ContTag::Outermost, RawPtr(0));

const ERROR: Continuation = Continuation::Error;
const ERROR_PTR: ContPtr = ContPtr(ContTag::Error, RawPtr(0));

const DUMMY: Continuation = Continuation::Dummy;
const DUMMY_PTR: ContPtr = ContPtr(ContTag::Dummy, RawPtr(0));

const TERMINAL: Continuation = Continuation::Terminal;
const TERMINAL_PTR: ContPtr = ContPtr(ContTag::Terminal, RawPtr(0));

impl Pool {
    pub fn new() -> Self {
        Pool::default()
    }

    pub const fn alloc_nil(&self) -> Ptr {
        NIL_PTR
    }

    pub const fn get_nil(&self) -> Ptr {
        NIL_PTR
    }

    pub fn alloc_cons(&mut self, car: Ptr, cdr: Ptr) -> Ptr {
        let (ptr, _) = self.cons_pool.insert_full((car, cdr));
        Ptr(Tag::Cons, RawPtr(ptr))
    }

    /// Helper to allocate a list, instead of manually using `cons`.
    pub fn alloc_list(&mut self, elts: &[Ptr]) -> Ptr {
        elts.iter()
            .rev()
            .fold(NIL_PTR, |acc, elt| self.alloc_cons(*elt, acc))
    }

    pub fn alloc_sym(&mut self, name: impl ToStr) -> Ptr {
        let mut name = name.to_str();
        if name.as_ref().eq_ignore_ascii_case("NIL") {
            return NIL_PTR;
        }

        // symbols are upper case
        Rc::get_mut(&mut name.0).unwrap().make_ascii_uppercase();

        let (ptr, _) = self.sym_pool.insert_full(name);
        Ptr(Tag::Sym, RawPtr(ptr))
    }

    pub fn get_sym(&self, name: impl ToStr) -> Ptr {
        // TODO: avoid allocation
        let mut name = name.to_str();
        if name.as_ref().eq_ignore_ascii_case("NIL") {
            return NIL_PTR;
        }

        // symbols are upper case
        Rc::get_mut(&mut name.0).unwrap().make_ascii_uppercase();
        self.find_sym(&name).expect("sym not found")
    }

    pub fn alloc_num(&mut self, num: u64) -> Ptr {
        let (ptr, _) = self.num_pool.insert_full(num);
        Ptr(Tag::Num, RawPtr(ptr))
    }

    pub fn alloc_str(&mut self, name: impl ToStr) -> Ptr {
        let (ptr, _) = self.str_pool.insert_full(name.to_str());
        Ptr(Tag::Str, RawPtr(ptr))
    }

    pub fn alloc_fun(&mut self, arg: Ptr, body: Ptr, closed_env: Ptr) -> Ptr {
        // TODO: closed_env must be an env
        assert!(matches!(arg.0, Tag::Sym), "ARG must be a symbol");

        let (ptr, _) = self.fun_pool.insert_full((arg, body, closed_env));
        Ptr(Tag::Fun, RawPtr(ptr))
    }

    pub fn alloc_thunk(&mut self, thunk: Thunk) -> Ptr {
        let (ptr, _) = self.thunk_pool.insert_full(thunk);
        Ptr(Tag::Thunk, RawPtr(ptr))
    }

    pub const fn alloc_cont_outermost(&self) -> ContPtr {
        OUTERMOST_PTR
    }

    pub const fn get_cont_outermost(&self) -> ContPtr {
        OUTERMOST_PTR
    }

    pub fn alloc_cont_call(&mut self, a: Ptr, b: Ptr, c: ContPtr) -> ContPtr {
        let (ptr, _) = self.call_pool.insert_full((a, b, c));
        ContPtr(ContTag::Call, RawPtr(ptr))
    }

    pub fn alloc_cont_call2(&mut self, a: Ptr, b: Ptr, c: ContPtr) -> ContPtr {
        let (ptr, _) = self.call2_pool.insert_full((a, b, c));
        ContPtr(ContTag::Call2, RawPtr(ptr))
    }

    pub const fn alloc_cont_error(&self) -> ContPtr {
        ERROR_PTR
    }

    pub const fn get_cont_error(&self) -> ContPtr {
        ERROR_PTR
    }

    pub const fn alloc_cont_terminal(&self) -> ContPtr {
        TERMINAL_PTR
    }

    pub const fn get_cont_terminal(&self) -> ContPtr {
        TERMINAL_PTR
    }

    pub const fn alloc_cont_dummy(&self) -> ContPtr {
        DUMMY_PTR
    }

    pub const fn get_cont_dummy(&self) -> ContPtr {
        DUMMY_PTR
    }

    pub fn alloc_cont_lookup(&mut self, a: Ptr, b: ContPtr) -> ContPtr {
        let (ptr, _) = self.lookup_pool.insert_full((a, b));
        ContPtr(ContTag::Lookup, RawPtr(ptr))
    }

    pub fn alloc_cont_let_star(&mut self, a: Ptr, b: Ptr, c: Ptr, d: ContPtr) -> ContPtr {
        let (ptr, _) = self.let_star_pool.insert_full((a, b, c, d));
        ContPtr(ContTag::LetStar, RawPtr(ptr))
    }

    pub fn alloc_cont_let_rec_star(&mut self, a: Ptr, b: Ptr, c: Ptr, d: ContPtr) -> ContPtr {
        let (ptr, _) = self.let_rec_star_pool.insert_full((a, b, c, d));
        ContPtr(ContTag::LetRecStar, RawPtr(ptr))
    }

    pub fn alloc_cont_unop(&mut self, op: Op1, a: ContPtr) -> ContPtr {
        let (ptr, _) = self.unop_pool.insert_full((op, a));
        ContPtr(ContTag::Unop, RawPtr(ptr))
    }

    pub fn alloc_cont_binop(&mut self, op: Op2, a: Ptr, b: Ptr, c: ContPtr) -> ContPtr {
        let (ptr, _) = self.binop_pool.insert_full((op, a, b, c));
        ContPtr(ContTag::Binop, RawPtr(ptr))
    }

    pub fn alloc_cont_binop2(&mut self, op: Op2, a: Ptr, b: ContPtr) -> ContPtr {
        let (ptr, _) = self.binop2_pool.insert_full((op, a, b));
        ContPtr(ContTag::Binop2, RawPtr(ptr))
    }

    pub fn alloc_cont_relop(&mut self, op: Rel2, a: Ptr, b: Ptr, c: ContPtr) -> ContPtr {
        let (ptr, _) = self.relop_pool.insert_full((op, a, b, c));
        ContPtr(ContTag::Relop, RawPtr(ptr))
    }

    pub fn alloc_cont_relop2(&mut self, op: Rel2, a: Ptr, b: ContPtr) -> ContPtr {
        let (ptr, _) = self.relop2_pool.insert_full((op, a, b));
        ContPtr(ContTag::Relop2, RawPtr(ptr))
    }

    pub fn alloc_cont_if(&mut self, a: Ptr, b: ContPtr) -> ContPtr {
        let (ptr, _) = self.if_pool.insert_full((a, b));
        ContPtr(ContTag::If, RawPtr(ptr))
    }

    pub fn alloc_cont_tail(&mut self, a: Ptr, b: ContPtr) -> ContPtr {
        let (ptr, _) = self.tail_pool.insert_full((a, b));
        ContPtr(ContTag::Tail, RawPtr(ptr))
    }

    pub fn find(&self, expr: &Expression) -> Option<Ptr> {
        match expr {
            Expression::Nil => Some(NIL_PTR),
            Expression::Cons(a, b) => self.find_cons(a, b),
            Expression::Sym(name) => self.find_sym(name),
            Expression::Str(name) => self.find_str(name),
            Expression::Thunk(thunk) => self.find_thunk(thunk),
            Expression::Fun(a, b, c) => self.find_fun(a, b, c),
            Expression::Num(num) => self.find_num(num),
        }
    }

    fn find_cons(&self, a: &Ptr, b: &Ptr) -> Option<Ptr> {
        self.cons_pool
            .get_index_of(&(*a, *b))
            .map(|raw| Ptr(Tag::Cons, RawPtr(raw)))
    }

    fn find_sym<Q: ?Sized>(&self, name: &Q) -> Option<Ptr>
    where
        Q: Hash + Equivalent<Str>,
    {
        self.sym_pool
            .get_index_of(name)
            .map(|raw| Ptr(Tag::Sym, RawPtr(raw)))
    }

    fn find_str<Q: ?Sized>(&self, name: &Q) -> Option<Ptr>
    where
        Q: Hash + Equivalent<Str>,
    {
        self.str_pool
            .get_index_of(name)
            .map(|raw| Ptr(Tag::Str, RawPtr(raw)))
    }

    fn find_num(&self, num: &u64) -> Option<Ptr> {
        self.num_pool
            .get_index_of(num)
            .map(|raw| Ptr(Tag::Num, RawPtr(raw)))
    }

    fn find_fun(&self, a: &Ptr, b: &Ptr, c: &Ptr) -> Option<Ptr> {
        self.fun_pool
            .get_index_of(&(*a, *b, *c))
            .map(|raw| Ptr(Tag::Fun, RawPtr(raw)))
    }

    fn find_thunk(&self, thunk: &Thunk) -> Option<Ptr> {
        self.thunk_pool
            .get_index_of(thunk)
            .map(|raw| Ptr(Tag::Thunk, RawPtr(raw)))
    }

    pub fn fetch_scalar(&self, scalar_ptr: &ScalarPtr) -> Option<Expression> {
        // TODO: insert values into the scalar_ptr_map on hashing!
        let ptr = self.scalar_ptr_map.get(scalar_ptr)?;
        self.fetch(ptr)
    }

    pub fn fetch_scalar_cont(&self, scalar_ptr: &ScalarPtr) -> Option<Continuation> {
        // TODO: insert values into the scalar_ptr_map on hashing!
        let ptr = self.scalar_ptr_cont_map.get(scalar_ptr)?;
        self.fetch_cont(ptr)
    }

    pub fn fetch(&self, ptr: &Ptr) -> Option<Expression> {
        match ptr.0 {
            Tag::Nil => Some(NIL),
            Tag::Cons => self
                .cons_pool
                .get_index(ptr.1 .0)
                .map(|(a, b)| Expression::Cons(*a, *b)),
            Tag::Sym => self
                .sym_pool
                .get_index(ptr.1 .0)
                .map(|name| Expression::Sym(name.clone())),
            Tag::Num => self
                .num_pool
                .get_index(ptr.1 .0)
                .map(|num| Expression::Num(*num)),
            Tag::Fun => self
                .fun_pool
                .get_index(ptr.1 .0)
                .map(|(a, b, c)| Expression::Fun(*a, *b, *c)),
            Tag::Thunk => self
                .thunk_pool
                .get_index(ptr.1 .0)
                .map(|thunk| Expression::Thunk(*thunk)),
            Tag::Str => self
                .str_pool
                .get_index(ptr.1 .0)
                .map(|name| Expression::Str(name.clone())),
        }
    }

    pub fn fetch_cont(&self, ptr: &ContPtr) -> Option<Continuation> {
        use ContTag::*;
        match ptr.0 {
            Outermost => Some(OUTERMOST),
            Simple => self
                .simple_pool
                .get_index(ptr.1 .0)
                .map(|a| Continuation::Simple(*a)),
            Call => self
                .call_pool
                .get_index(ptr.1 .0)
                .map(|(a, b, c)| Continuation::Call(*a, *b, *c)),
            Call2 => self
                .call2_pool
                .get_index(ptr.1 .0)
                .map(|(a, b, c)| Continuation::Call2(*a, *b, *c)),
            Tail => self
                .tail_pool
                .get_index(ptr.1 .0)
                .map(|(a, b)| Continuation::Tail(*a, *b)),
            Error => Some(ERROR),
            Lookup => self
                .lookup_pool
                .get_index(ptr.1 .0)
                .map(|(a, b)| Continuation::Lookup(*a, *b)),
            Unop => self
                .unop_pool
                .get_index(ptr.1 .0)
                .map(|(a, b)| Continuation::Unop(*a, *b)),
            Binop => self
                .binop_pool
                .get_index(ptr.1 .0)
                .map(|(a, b, c, d)| Continuation::Binop(*a, *b, *c, *d)),
            Binop2 => self
                .binop2_pool
                .get_index(ptr.1 .0)
                .map(|(a, b, c)| Continuation::Binop2(*a, *b, *c)),
            Relop => self
                .relop_pool
                .get_index(ptr.1 .0)
                .map(|(a, b, c, d)| Continuation::Relop(*a, *b, *c, *d)),
            Relop2 => self
                .relop2_pool
                .get_index(ptr.1 .0)
                .map(|(a, b, c)| Continuation::Relop2(*a, *b, *c)),
            If => self
                .if_pool
                .get_index(ptr.1 .0)
                .map(|(a, b)| Continuation::If(*a, *b)),
            LetStar => self
                .let_star_pool
                .get_index(ptr.1 .0)
                .map(|(a, b, c, d)| Continuation::LetStar(*a, *b, *c, *d)),
            LetRecStar => self
                .let_rec_star_pool
                .get_index(ptr.1 .0)
                .map(|(a, b, c, d)| Continuation::LetRecStar(*a, *b, *c, *d)),
            Dummy => Some(DUMMY),
            Terminal => Some(TERMINAL),
        }
    }

    pub fn car_cdr(&self, ptr: &Ptr) -> (Ptr, Ptr) {
        match ptr.0 {
            Tag::Nil => (NIL_PTR, NIL_PTR),
            Tag::Cons => match self.fetch(ptr) {
                Some(Expression::Cons(car, cdr)) => (car, cdr),
                _ => unreachable!(),
            },
            _ => panic!("Can only extract car_cdr from Cons"),
        }
    }

    pub fn car(&self, expr: &Ptr) -> Ptr {
        self.car_cdr(expr).0
    }

    pub fn cdr(&self, expr: &Ptr) -> Ptr {
        self.car_cdr(expr).1
    }

    pub fn hash_expr(&self, ptr: &Ptr) -> Option<ScalarPtr> {
        use Expression::*;

        let expr = self.fetch(ptr)?;
        match expr {
            Nil => self.hash_sym("NIL"),
            Cons(car, cdr) => self.hash_cons(car, cdr),
            Sym(name) => self.hash_str(name.as_ref()),
            Fun(arg, body, closed_env) => self.hash_fun(arg, body, closed_env),
            Num(n) => self.hash_num(n),
            Str(name) => self.hash_str(name.as_ref()),
            Thunk(thunk) => self.hash_thunk(&thunk),
        }
    }

    pub fn hash_cont(&self, ptr: &ContPtr) -> Option<ScalarPtr> {
        let components = self.get_hash_components_cont(ptr)?;
        let hash = self.hash_scalar_ptrs_4(&components);

        Some(ScalarPtr(ptr.tag_field(), hash))
    }

    pub fn get_hash_components_cont(&self, ptr: &ContPtr) -> Option<[ScalarPtr; 4]> {
        use Continuation::*;

        let cont = self.fetch_cont(ptr)?;
        let nil = self.hash_nil();

        let hash = match cont {
            Outermost | Dummy | Terminal | Error => [nil, nil, nil, nil],
            Simple(cont) => {
                let cont = self.hash_cont(&cont)?;
                [cont, nil, nil, nil]
            }
            Call(arg, saved_env, cont) => {
                let arg = self.hash_expr(&arg)?;
                let saved_env = self.hash_expr(&saved_env)?;
                let cont = self.hash_cont(&cont)?;
                [saved_env, arg, cont, nil]
            }
            Call2(fun, saved_env, cont) => {
                let fun = self.hash_expr(&fun)?;
                let saved_env = self.hash_expr(&saved_env)?;
                let cont = self.hash_cont(&cont)?;
                [saved_env, fun, cont, nil]
            }
            Tail(saved_env, cont) => {
                let saved_env = self.hash_expr(&saved_env)?;
                let cont = self.hash_cont(&cont)?;
                [saved_env, cont, nil, nil]
            }
            Lookup(saved_env, cont) => {
                let saved_env = self.hash_expr(&saved_env)?;
                let cont = self.hash_cont(&cont)?;
                [saved_env, cont, nil, nil]
            }
            Unop(op, cont) => {
                let op = self.hash_op1(&op);
                let cont = self.hash_cont(&cont)?;
                [op, cont, nil, nil]
            }
            Binop(op, saved_env, unevaled_args, cont) => {
                let op = self.hash_op2(&op);
                let saved_env = self.hash_expr(&saved_env)?;
                let unevaled_args = self.hash_expr(&unevaled_args)?;
                let cont = self.hash_cont(&cont)?;
                [op, saved_env, unevaled_args, cont]
            }
            Binop2(op, arg1, cont) => {
                let op = self.hash_op2(&op);
                let arg1 = self.hash_expr(&arg1)?;
                let cont = self.hash_cont(&cont)?;
                [op, arg1, cont, nil]
            }
            Relop(rel, saved_env, unevaled_args, cont) => {
                let rel = self.hash_rel2(&rel);
                let saved_env = self.hash_expr(&saved_env)?;
                let unevaled_args = self.hash_expr(&unevaled_args)?;
                let cont = self.hash_cont(&cont)?;
                [rel, saved_env, unevaled_args, cont]
            }
            Relop2(rel, arg1, cont) => {
                let rel = self.hash_rel2(&rel);
                let arg1 = self.hash_expr(&arg1)?;
                let cont = self.hash_cont(&cont)?;
                [rel, arg1, cont, nil]
            }
            If(unevaled_args, cont) => {
                let unevaled_args = self.hash_expr(&unevaled_args)?;
                let cont = self.hash_cont(&cont)?;
                [unevaled_args, cont, nil, nil]
            }
            LetStar(var, body, saved_env, cont) => {
                let var = self.hash_expr(&var)?;
                let body = self.hash_expr(&body)?;
                let saved_env = self.hash_expr(&saved_env)?;
                let cont = self.hash_cont(&cont)?;
                [var, body, saved_env, cont]
            }
            LetRecStar(var, body, saved_env, cont) => {
                let var = self.hash_expr(&var)?;
                let body = self.hash_expr(&body)?;
                let saved_env = self.hash_expr(&saved_env)?;
                let cont = self.hash_cont(&cont)?;
                [var, body, saved_env, cont]
            }
        };
        Some(hash)
    }

    pub fn get_hash_components_thunk(&self, thunk: &Thunk) -> Option<[ScalarPtr; 2]> {
        let value_hash = self.hash_expr(&thunk.value)?;
        let continuation_hash = self.hash_cont(&thunk.continuation)?;

        Some([value_hash, continuation_hash])
    }

    fn hash_sym(&self, sym: &str) -> Option<ScalarPtr> {
        Some(ScalarPtr(Tag::Sym.as_field(), self.hash_string(sym)))
    }

    fn hash_str(&self, s: &str) -> Option<ScalarPtr> {
        Some(ScalarPtr(Tag::Str.as_field(), self.hash_string(s)))
    }

    fn hash_fun(&self, arg: Ptr, body: Ptr, closed_env: Ptr) -> Option<ScalarPtr> {
        Some(ScalarPtr(
            Tag::Fun.as_field(),
            self.hash_ptrs_3(&[arg, body, closed_env])?,
        ))
    }

    fn hash_cons(&self, car: Ptr, cdr: Ptr) -> Option<ScalarPtr> {
        Some(ScalarPtr(
            Tag::Cons.as_field(),
            self.hash_ptrs_2(&[car, cdr])?,
        ))
    }

    fn hash_thunk(&self, thunk: &Thunk) -> Option<ScalarPtr> {
        let components = self.get_hash_components_thunk(thunk)?;
        Some(ScalarPtr(
            Tag::Thunk.as_field(),
            self.hash_scalar_ptrs_2(&components),
        ))
    }

    fn hash_num(&self, n: u64) -> Option<ScalarPtr> {
        Some(ScalarPtr(Tag::Num.as_field(), Scalar::from(n)))
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
                x = Poseidon::new_with_preimage(&preimage, &POSEIDON_CONSTANTS_8).hash()
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
        Poseidon::new_with_preimage(&preimage, &POSEIDON_CONSTANTS_4).hash()
    }

    fn hash_scalar_ptrs_3(&self, ptrs: &[ScalarPtr; 3]) -> Scalar {
        let preimage = [
            ptrs[0].0, ptrs[0].1, ptrs[1].0, ptrs[1].1, ptrs[2].0, ptrs[2].1,
        ];
        Poseidon::new_with_preimage(&preimage, &POSEIDON_CONSTANTS_6).hash()
    }

    fn hash_scalar_ptrs_4(&self, ptrs: &[ScalarPtr; 4]) -> Scalar {
        let preimage = [
            ptrs[0].0, ptrs[0].1, ptrs[1].0, ptrs[1].1, ptrs[2].0, ptrs[2].1, ptrs[3].0, ptrs[3].1,
        ];
        Poseidon::new_with_preimage(&preimage, &POSEIDON_CONSTANTS_8).hash()
    }

    pub fn hash_nil(&self) -> ScalarPtr {
        ScalarPtr(Tag::Nil.as_field(), Scalar::zero())
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
}

impl Expression {
    pub fn is_keyword_sym(&self) -> bool {
        match self {
            Expression::Sym(s) => s.as_ref().starts_with(':'),
            _ => false,
        }
    }

    pub fn as_sym_str(&self) -> Option<&str> {
        match self {
            Expression::Sym(s) => Some(s.as_ref()),
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
        let mut pool = Pool::default();
        let num = pool.alloc_num(5);
        let res = num.fmt_to_string(&pool);
        assert_eq!(&res, &"Fr(0x5)");
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

        assert_eq!(0, Outermost.cont_tag_val());
        assert_eq!(1, Outermost.thunk_tag_val());
        assert_eq!(2, Simple.cont_tag_val());
        assert_eq!(3, Simple.thunk_tag_val());
        assert_eq!(4, Call.cont_tag_val());
        assert_eq!(5, Call.thunk_tag_val());
        assert_eq!(6, Call2.cont_tag_val());
        assert_eq!(7, Call2.thunk_tag_val());
        assert_eq!(8, Tail.cont_tag_val());
        assert_eq!(9, Tail.thunk_tag_val());
        assert_eq!(10, Error.cont_tag_val());
        assert_eq!(11, Error.thunk_tag_val());
        assert_eq!(12, Lookup.cont_tag_val());
        assert_eq!(13, Lookup.thunk_tag_val());
        assert_eq!(14, Unop.cont_tag_val());
        assert_eq!(15, Unop.thunk_tag_val());
        assert_eq!(16, Binop.cont_tag_val());
        assert_eq!(17, Binop.thunk_tag_val());
        assert_eq!(18, Binop2.cont_tag_val());
        assert_eq!(19, Binop2.thunk_tag_val());
        assert_eq!(20, Relop.cont_tag_val());
        assert_eq!(21, Relop.thunk_tag_val());
        assert_eq!(22, Relop2.cont_tag_val());
        assert_eq!(23, Relop2.thunk_tag_val());
        assert_eq!(24, If.cont_tag_val());
        assert_eq!(25, If.thunk_tag_val());
        assert_eq!(26, LetStar.cont_tag_val());
        assert_eq!(27, LetStar.thunk_tag_val());
        assert_eq!(28, LetRecStar.cont_tag_val());
        assert_eq!(29, LetRecStar.thunk_tag_val());
        assert_eq!(30, Dummy.cont_tag_val());
        assert_eq!(31, Dummy.thunk_tag_val());
        assert_eq!(32, Terminal.cont_tag_val());
        assert_eq!(33, Terminal.thunk_tag_val());
    }

    #[test]
    fn pool() {
        let mut pool = Pool::default();

        let num_ptr = pool.alloc_num(123);
        let num = pool.fetch(&num_ptr).unwrap();
        let num_again = pool.fetch(&num_ptr).unwrap();

        assert_eq!(num, num_again);
    }

    #[test]
    fn equality() {
        let mut pool = Pool::default();

        let (a, b) = (pool.alloc_num(123), pool.alloc_sym("pumpkin"));
        let cons1 = pool.alloc_cons(a, b);
        let (a, b) = (pool.alloc_num(123), pool.alloc_sym("pumpkin"));
        let cons2 = pool.alloc_cons(a, b);

        assert_eq!(cons1, cons2);
        assert_eq!(pool.car(&cons1), pool.car(&cons2));
        assert_eq!(pool.cdr(&cons1), pool.cdr(&cons2));

        let (a, d) = pool.car_cdr(&cons1);
        assert_eq!(pool.car(&cons1), a);
        assert_eq!(pool.cdr(&cons1), d);
    }
}
