use anyhow::{bail, Context, Result};
use bellpepper::util_cs::witness_cs::SizedWitness;
use elsa::sync::FrozenMap;
use match_opt::match_opt;
use neptune::Poseidon;
use nom::{sequence::preceded, Parser};

use crate::{
    field::{FWrap, LurkField},
    hash::{InversePoseidonCache, PoseidonCache},
    lem::{
        pointers::{IVal, Ptr, ZPtr},
        store_core::{StoreCore, StoreHasher},
        Tag,
    },
    parser::{syntax, Error, Span},
    state::{lurk_sym, user_sym, State, StateRcCell},
    symbol::Symbol,
    syntax::Syntax,
    tag::ContTag::{
        self, Binop, Binop2, Call, Call0, Call2, Dummy, Emit, If, Let, LetRec, Lookup, Outermost,
        StreamDispatch, StreamPause, StreamStart, Tail, Terminal, Unop,
    },
    tag::ExprTag::{
        Char, Comm, Cons, Cproc, Env, Fun, Key, Nil, Num, Prov, Rec, Str, Sym, Thunk, U64,
    },
};

impl<F: LurkField> StoreHasher<Tag, FWrap<F>> for PoseidonCache<F> {
    fn hash_ptrs(&self, mut ptrs: Vec<ZPtr<F>>) -> FWrap<F> {
        match ptrs.len() {
            2 => {
                let (b_tag, b_hash) = ptrs.pop().unwrap().into_parts();
                let (a_tag, a_hash) = ptrs.pop().unwrap().into_parts();
                FWrap(self.hash4(&[a_tag.to_field(), a_hash.0, b_tag.to_field(), b_hash.0]))
            }
            3 => {
                let (c_tag, c_hash) = ptrs.pop().unwrap().into_parts();
                let (b_tag, b_hash) = ptrs.pop().unwrap().into_parts();
                let (a_tag, a_hash) = ptrs.pop().unwrap().into_parts();
                FWrap(self.hash6(&[
                    a_tag.to_field(),
                    a_hash.0,
                    b_tag.to_field(),
                    b_hash.0,
                    c_tag.to_field(),
                    c_hash.0,
                ]))
            }
            4 => {
                let (d_tag, d_hash) = ptrs.pop().unwrap().into_parts();
                let (c_tag, c_hash) = ptrs.pop().unwrap().into_parts();
                let (b_tag, b_hash) = ptrs.pop().unwrap().into_parts();
                let (a_tag, a_hash) = ptrs.pop().unwrap().into_parts();
                FWrap(self.hash8(&[
                    a_tag.to_field(),
                    a_hash.0,
                    b_tag.to_field(),
                    b_hash.0,
                    c_tag.to_field(),
                    c_hash.0,
                    d_tag.to_field(),
                    d_hash.0,
                ]))
            }
            _ => unimplemented!(),
        }
    }

    fn hash_commitment(&self, secret: FWrap<F>, payload: ZPtr<F>) -> FWrap<F> {
        let (tag, hash) = payload.into_parts();
        FWrap(self.hash3(&[secret.0, tag.to_field(), hash.0]))
    }

    fn hash_compact(&self, d1: FWrap<F>, t2: Tag, d2: FWrap<F>, d3: FWrap<F>) -> FWrap<F> {
        FWrap(self.hash4(&[d1.0, t2.to_field(), d2.0, d3.0]))
    }
}

/// Uses `StoreCore` to intern Lurk data and perform hashing with `PoseidonCache`
#[derive(Debug)]
pub struct Store<F: LurkField> {
    pub core: StoreCore<Tag, FWrap<F>, PoseidonCache<F>>,

    // cached data to speed up interning
    string_ptr_cache: FrozenMap<String, Box<Ptr>>,
    symbol_ptr_cache: FrozenMap<Symbol, Box<Ptr>>,

    // cached data to speed up fetching
    ptr_string_cache: FrozenMap<Ptr, String>,
    ptr_symbol_cache: FrozenMap<Ptr, Box<Symbol>>,

    /// A data structure for the trie coprocessor
    // TODO: factor this out
    pub inverse_poseidon_cache: InversePoseidonCache<F>,

    // cached indices for the hashes of 3, 4, 6 and 8 padded zeros
    pub hash3zeros_idx: usize,
    pub hash4zeros_idx: usize,
    pub hash6zeros_idx: usize,
    pub hash8zeros_idx: usize,
}

/// `WithStore` provides a distinct type for coupling a store with a value of another type.
pub struct WithStore<'a, F: LurkField, T>(pub T, pub &'a Store<F>);

impl<'a, F: LurkField, T> WithStore<'a, F, T> {
    pub fn store(&self) -> &Store<F> {
        self.1
    }

    pub fn inner(&self) -> &T {
        &self.0
    }

    pub fn to_inner(self) -> T {
        self.0
    }
}

impl<F: LurkField> Default for Store<F> {
    fn default() -> Self {
        let core: StoreCore<Tag, FWrap<F>, PoseidonCache<F>> = StoreCore::default();
        let hash3zeros = core.hasher.hash3(&[F::ZERO; 3]);
        let hash4zeros = core.hasher.hash4(&[F::ZERO; 4]);
        let hash6zeros = core.hasher.hash6(&[F::ZERO; 6]);
        let hash8zeros = core.hasher.hash8(&[F::ZERO; 8]);

        let hash3zeros_idx = core.intern_digest(FWrap(hash3zeros));
        let hash4zeros_idx = core.intern_digest(FWrap(hash4zeros));
        let hash6zeros_idx = core.intern_digest(FWrap(hash6zeros));
        let hash8zeros_idx = core.intern_digest(FWrap(hash8zeros));

        Self {
            core,
            string_ptr_cache: Default::default(),
            symbol_ptr_cache: Default::default(),
            ptr_string_cache: Default::default(),
            ptr_symbol_cache: Default::default(),
            inverse_poseidon_cache: Default::default(),
            hash3zeros_idx,
            hash4zeros_idx,
            hash6zeros_idx,
            hash8zeros_idx,
        }
    }
}

// Handling to the core
impl<F: LurkField> Store<F> {
    #[inline]
    pub fn intern_f(&self, f: F) -> usize {
        self.core.intern_digest(FWrap(f))
    }

    pub fn intern_atom(&self, tag: Tag, f: F) -> Ptr {
        self.core.intern_atom(tag, FWrap(f))
    }

    #[inline]
    pub fn fetch_f(&self, idx: usize) -> Option<&F> {
        self.core.fetch_digest(idx).map(|fw| &fw.0)
    }

    #[inline]
    pub fn expect_f(&self, idx: usize) -> &F {
        self.core.expect_digest(idx).get()
    }

    #[inline]
    pub fn fetch_f_by_val(&self, ptr_val: &IVal) -> Option<&F> {
        ptr_val.get_atom_idx().and_then(|idx| self.fetch_f(idx))
    }

    #[inline]
    pub fn intern_tuple2(&self, ptrs: [Ptr; 2], tag: Tag, hash: Option<F>) -> Ptr {
        self.core.intern_tuple2(ptrs, tag, hash.map(FWrap))
    }

    #[inline]
    pub fn fetch_tuple2(&self, idx: usize) -> Option<&[Ptr; 2]> {
        self.core.fetch_tuple2(idx)
    }

    #[inline]
    pub fn expect_tuple2(&self, idx: usize) -> &[Ptr; 2] {
        self.core.expect_tuple2(idx)
    }

    #[inline]
    pub fn intern_tuple3(&self, ptrs: [Ptr; 3], tag: Tag, hash: Option<F>) -> Ptr {
        self.core.intern_tuple3(ptrs, tag, hash.map(FWrap))
    }

    #[inline]
    pub fn fetch_tuple3(&self, idx: usize) -> Option<&[Ptr; 3]> {
        self.core.fetch_tuple3(idx)
    }

    #[inline]
    pub fn expect_tuple3(&self, idx: usize) -> &[Ptr; 3] {
        self.core.expect_tuple3(idx)
    }

    #[inline]
    pub fn intern_tuple4(&self, ptrs: [Ptr; 4], tag: Tag, hash: Option<F>) -> Ptr {
        self.core.intern_tuple4(ptrs, tag, hash.map(FWrap))
    }

    #[inline]
    pub fn fetch_tuple4(&self, idx: usize) -> Option<&[Ptr; 4]> {
        self.core.fetch_tuple4(idx)
    }

    #[inline]
    pub fn expect_tuple4(&self, idx: usize) -> &[Ptr; 4] {
        self.core.expect_tuple4(idx)
    }

    #[inline]
    pub fn intern_compact(&self, ptrs: [Ptr; 3], tag: Tag, hash: Option<F>) -> Ptr {
        self.core.intern_compact(ptrs, tag, hash.map(FWrap))
    }

    #[inline]
    fn fetch_compact(&self, ptr: &Ptr) -> Option<&[Ptr; 3]> {
        self.core.fetch_compact_by_val(ptr.val())
    }

    #[inline]
    pub fn opaque(&self, z: ZPtr<F>) -> Ptr {
        self.core.opaque(z)
    }

    #[inline]
    pub fn add_comm(&self, hash: F, secret: F, payload: Ptr) {
        self.core.add_comm(FWrap(hash), FWrap(secret), payload)
    }

    #[inline]
    pub fn hide_and_return_z_payload(&self, secret: F, payload: Ptr) -> (F, ZPtr<F>) {
        let (digest, z_ptr) = self.core.hide(FWrap(secret), payload);
        (digest.0, z_ptr)
    }

    #[inline]
    pub fn open(&self, hash: F) -> Option<&(FWrap<F>, Ptr)> {
        self.core.open(&FWrap(hash))
    }

    #[inline]
    pub fn hydrate_z_cache(&self) {
        self.core.hydrate_z_cache()
    }

    #[inline]
    pub fn hash_ptr_val(&self, ptr_val: &IVal) -> FWrap<F> {
        self.core.hash_ptr_val(ptr_val)
    }

    #[inline]
    pub fn hash_ptr(&self, ptr: &Ptr) -> ZPtr<F> {
        self.core.hash_ptr(ptr)
    }

    #[inline]
    pub fn ptr_eq(&self, a: &Ptr, b: &Ptr) -> bool {
        self.core.ptr_eq(a, b)
    }

    #[inline]
    pub fn to_ptr_val(&self, hash: &FWrap<F>) -> IVal {
        self.core.to_ptr_val(hash)
    }

    #[inline]
    pub fn to_ptr(&self, z_ptr: &ZPtr<F>) -> Ptr {
        self.core.to_ptr(z_ptr)
    }
}

// Implementations that are particular to `Store`
impl<F: LurkField> Store<F> {
    /// Cost of poseidon hash with arity 3, including the input
    #[inline]
    pub fn hash3_cost(&self) -> usize {
        Poseidon::new(self.core.hasher.constants.c3()).num_aux() + 1
    }

    /// Cost of poseidon hash with arity 4, including the input
    #[inline]
    pub fn hash4_cost(&self) -> usize {
        Poseidon::new(self.core.hasher.constants.c4()).num_aux() + 1
    }

    /// Cost of poseidon hash with arity 6, including the input
    #[inline]
    pub fn hash6_cost(&self) -> usize {
        Poseidon::new(self.core.hasher.constants.c6()).num_aux() + 1
    }

    /// Cost of poseidon hash with arity 8, including the input
    #[inline]
    pub fn hash8_cost(&self) -> usize {
        Poseidon::new(self.core.hasher.constants.c8()).num_aux() + 1
    }

    /// Retrieves the hash of 3 padded zeros
    #[inline]
    pub fn hash3zeros(&self) -> &F {
        self.expect_f(self.hash3zeros_idx)
    }

    /// Retrieves the hash of 4 padded zeros
    #[inline]
    pub fn hash4zeros(&self) -> &F {
        self.expect_f(self.hash4zeros_idx)
    }

    /// Retrieves the hash of 6 padded zeros
    #[inline]
    pub fn hash6zeros(&self) -> &F {
        self.expect_f(self.hash6zeros_idx)
    }

    /// Retrieves the hash of 8 padded zeros
    #[inline]
    pub fn hash8zeros(&self) -> &F {
        self.expect_f(self.hash8zeros_idx)
    }

    #[inline]
    pub fn push_binding(&self, sym: Ptr, v: Ptr, env: Ptr) -> Ptr {
        assert_eq!(sym.tag(), &Tag::Expr(Sym));
        assert_eq!(env.tag(), &Tag::Expr(Env));
        self.core
            .intern_compact([sym, v, env], Tag::Expr(Env), None)
    }

    #[inline]
    pub fn pop_binding(&self, env: &Ptr) -> Option<&[Ptr; 3]> {
        assert_eq!(env.tag(), &Tag::Expr(Env));
        let ptrs = self.fetch_compact(env)?;
        assert_eq!(ptrs[0].tag(), &Tag::Expr(Sym));
        assert_eq!(ptrs[2].tag(), &Tag::Expr(Env));
        Some(ptrs)
    }

    #[inline]
    pub fn intern_provenance(&self, query: Ptr, val: Ptr, deps: Ptr) -> Ptr {
        assert_eq!(query.tag(), &Tag::Expr(Cons));
        // TODO: Deps must be a single Prov or a list (later, an N-ary tuple), but we discard the type tag. This is
        // arguably okay, but it means that in order to recover the preimage we will need to know the expected arity
        // based on the query.
        assert!(matches!(deps.tag(), Tag::Expr(Prov | Cons | Nil)));
        self.core
            .intern_compact([query, val, deps], Tag::Expr(Prov), None)
    }

    #[inline]
    pub fn deconstruct_provenance(&self, prov: &Ptr) -> Option<&[Ptr; 3]> {
        assert_eq!(prov.tag(), &Tag::Expr(Prov));
        self.fetch_compact(prov)
    }

    #[inline]
    pub fn intern_empty_env(&self) -> Ptr {
        self.intern_atom(Tag::Expr(Env), F::ZERO)
    }

    #[inline]
    pub fn num(&self, f: F) -> Ptr {
        self.intern_atom(Tag::Expr(Num), f)
    }

    #[inline]
    pub fn fetch_num(&self, ptr: &Ptr) -> Option<&F> {
        match_opt!(ptr.tag(), Tag::Expr(Num) => self.fetch_f_by_val(ptr.val())?)
    }

    #[inline]
    pub fn num_u64(&self, u: u64) -> Ptr {
        self.intern_atom(Tag::Expr(Num), F::from_u64(u))
    }

    #[inline]
    pub fn u64(&self, u: u64) -> Ptr {
        self.intern_atom(Tag::Expr(U64), F::from_u64(u))
    }

    #[inline]
    pub fn fetch_u64(&self, ptr: &Ptr) -> Option<u64> {
        match_opt!(ptr.tag(), Tag::Expr(U64) => self.fetch_f_by_val(ptr.val()).and_then(F::to_u64)?)
    }

    #[inline]
    pub fn char(&self, c: char) -> Ptr {
        self.intern_atom(Tag::Expr(Char), F::from_char(c))
    }

    #[inline]
    pub fn fetch_char(&self, ptr: &Ptr) -> Option<char> {
        match_opt!(ptr.tag(), Tag::Expr(Char) => self.fetch_f_by_val(ptr.val()).and_then(F::to_char)?)
    }

    #[inline]
    pub fn comm(&self, hash: F) -> Ptr {
        self.intern_atom(Tag::Expr(Comm), hash)
    }

    #[inline]
    pub fn zero(&self, tag: Tag) -> Ptr {
        self.core.intern_atom(tag, FWrap(F::ZERO))
    }

    pub fn is_zero(&self, raw: &IVal) -> bool {
        match raw {
            IVal::Atom(idx) => self.fetch_f(*idx) == Some(&F::ZERO),
            _ => false,
        }
    }

    #[inline]
    pub fn dummy(&self) -> Ptr {
        self.zero(Tag::Expr(Nil))
    }

    pub fn intern_string(&self, s: &str) -> Ptr {
        if let Some(ptr) = self.string_ptr_cache.get(s) {
            *ptr
        } else {
            let empty_str = self.zero(Tag::Expr(Str));
            let ptr = s.chars().rev().fold(empty_str, |acc, c| {
                self.core
                    .intern_tuple2([self.char(c), acc], Tag::Expr(Str), None)
            });
            self.string_ptr_cache.insert(s.to_string(), Box::new(ptr));
            self.ptr_string_cache.insert(ptr, s.to_string());
            ptr
        }
    }

    pub fn fetch_string(&self, ptr: &Ptr) -> Option<String> {
        if let Some(str) = self.ptr_string_cache.get(ptr) {
            Some(str.to_string())
        } else {
            let mut string = String::new();
            let mut ptr = *ptr;
            if *ptr.tag() != Tag::Expr(Str) {
                return None;
            }
            loop {
                match *ptr.val() {
                    IVal::Atom(idx) => {
                        if self.fetch_f(idx)? == &F::ZERO {
                            self.ptr_string_cache.insert(ptr, string.clone());
                            return Some(string);
                        } else {
                            return None;
                        }
                    }
                    IVal::Tuple2(idx) => {
                        let [car, cdr] = self.core.fetch_tuple2(idx)?;
                        assert_eq!(car.tag(), &Tag::Expr(Char));
                        assert_eq!(cdr.tag(), &Tag::Expr(Str));
                        match car.val() {
                            IVal::Atom(idx) => {
                                let f = self.fetch_f(*idx)?;
                                string.push(f.to_char().expect("malformed char pointer"));
                                ptr = *cdr;
                            }
                            _ => return None,
                        }
                    }
                    _ => return None,
                }
            }
        }
    }

    pub fn intern_symbol_path(&self, path: &[String]) -> Ptr {
        let zero_sym = self.zero(Tag::Expr(Sym));
        path.iter().fold(zero_sym, |acc, s| {
            self.core
                .intern_tuple2([self.intern_string(s), acc], Tag::Expr(Sym), None)
        })
    }

    pub fn intern_symbol(&self, sym: &Symbol) -> Ptr {
        if let Some(ptr) = self.symbol_ptr_cache.get(sym) {
            *ptr
        } else {
            let path_ptr = self.intern_symbol_path(sym.path());
            let sym_ptr = if sym == &lurk_sym("nil") {
                Ptr::new(Tag::Expr(Nil), *path_ptr.val())
            } else if sym.is_keyword() {
                Ptr::new(Tag::Expr(Key), *path_ptr.val())
            } else {
                path_ptr
            };
            self.symbol_ptr_cache.insert(sym.clone(), Box::new(sym_ptr));
            self.ptr_symbol_cache.insert(sym_ptr, Box::new(sym.clone()));
            sym_ptr
        }
    }

    /// Fetches a symbol path whose interning returned the provided `idx`
    fn fetch_symbol_path(&self, mut idx: usize) -> Option<Vec<String>> {
        let mut path = vec![];
        loop {
            let [car, cdr] = self.core.fetch_tuple2(idx)?;
            assert_eq!(car.tag(), &Tag::Expr(Str));
            assert_eq!(cdr.tag(), &Tag::Expr(Sym));
            let string = self.fetch_string(car)?;

            path.push(string);
            match cdr.val() {
                IVal::Atom(idx) => {
                    if self.fetch_f(*idx)? == &F::ZERO {
                        path.reverse();
                        return Some(path);
                    } else {
                        return None;
                    }
                }
                IVal::Tuple2(idx_cdr) => idx = *idx_cdr,
                _ => return None,
            }
        }
    }

    pub fn fetch_symbol(&self, ptr: &Ptr) -> Option<Symbol> {
        if let Some(sym) = self.ptr_symbol_cache.get(ptr) {
            Some(sym.clone())
        } else {
            match (ptr.tag(), ptr.val()) {
                (Tag::Expr(Sym), IVal::Atom(idx)) => {
                    if self.fetch_f(*idx)? == &F::ZERO {
                        let sym = Symbol::root_sym();
                        self.ptr_symbol_cache.insert(*ptr, Box::new(sym.clone()));
                        Some(sym)
                    } else {
                        None
                    }
                }
                (Tag::Expr(Key), IVal::Atom(idx)) => {
                    if self.fetch_f(*idx)? == &F::ZERO {
                        let key = Symbol::root_key();
                        self.ptr_symbol_cache.insert(*ptr, Box::new(key.clone()));
                        Some(key)
                    } else {
                        None
                    }
                }
                (Tag::Expr(Sym | Nil), IVal::Tuple2(idx)) => {
                    let path = self.fetch_symbol_path(*idx)?;
                    let sym = Symbol::sym_from_vec(path);
                    self.ptr_symbol_cache.insert(*ptr, Box::new(sym.clone()));
                    Some(sym)
                }
                (Tag::Expr(Key), IVal::Tuple2(idx)) => {
                    let path = self.fetch_symbol_path(*idx)?;
                    let key = Symbol::key_from_vec(path);
                    self.ptr_symbol_cache.insert(*ptr, Box::new(key.clone()));
                    Some(key)
                }
                _ => None,
            }
        }
    }

    #[inline]
    pub fn fetch_sym(&self, ptr: &Ptr) -> Option<Symbol> {
        match_opt!(ptr.tag(), Tag::Expr(Sym) => self.fetch_symbol(ptr)?)
    }

    #[inline]
    pub fn fetch_key(&self, ptr: &Ptr) -> Option<Symbol> {
        match_opt!(ptr.tag(), Tag::Expr(Key) => self.fetch_symbol(ptr)?)
    }

    #[inline]
    pub fn intern_lurk_symbol(&self, name: &str) -> Ptr {
        self.intern_symbol(&lurk_sym(name))
    }

    #[inline]
    pub fn intern_nil(&self) -> Ptr {
        self.intern_lurk_symbol("nil")
    }

    #[inline]
    pub fn intern_t(&self) -> Ptr {
        self.intern_lurk_symbol("t")
    }

    #[inline]
    pub fn intern_user_symbol(&self, name: &str) -> Ptr {
        self.intern_symbol(&user_sym(name))
    }

    #[inline]
    pub fn key(&self, name: &str) -> Ptr {
        self.intern_symbol(&Symbol::key(&[name.to_string()]))
    }

    #[inline]
    pub fn hide(&self, secret: F, payload: Ptr) -> Ptr {
        self.comm(self.hide_and_return_z_payload(secret, payload).0)
    }

    #[inline]
    pub fn commit(&self, payload: Ptr) -> Ptr {
        self.hide(F::NON_HIDING_COMMITMENT_SECRET, payload)
    }

    #[inline]
    pub fn cons(&self, car: Ptr, cdr: Ptr) -> Ptr {
        self.core.intern_tuple2([car, cdr], Tag::Expr(Cons), None)
    }

    #[inline]
    pub fn intern_fun(&self, args: Ptr, body: Ptr, env: Ptr) -> Ptr {
        self.core
            .intern_tuple4([args, body, env, self.dummy()], Tag::Expr(Fun), None)
    }

    #[inline]
    fn cont_atom(&self, cont_tag: ContTag) -> Ptr {
        Ptr::new(Tag::Cont(cont_tag), IVal::Atom(self.hash8zeros_idx))
    }

    #[inline]
    pub fn cont_outermost(&self) -> Ptr {
        self.cont_atom(Outermost)
    }

    #[inline]
    pub fn cont_error(&self) -> Ptr {
        self.cont_atom(ContTag::Error)
    }

    #[inline]
    pub fn cont_terminal(&self) -> Ptr {
        self.cont_atom(Terminal)
    }

    #[inline]
    pub fn cont_stream_start(&self) -> Ptr {
        self.cont_atom(StreamStart)
    }

    #[inline]
    pub fn cont_stream_pause(&self) -> Ptr {
        self.cont_atom(StreamPause)
    }

    /// Function specialized on deconstructing `Cons` pointers into their car/cdr
    pub fn fetch_cons(&self, ptr: &Ptr) -> Option<(&Ptr, &Ptr)> {
        match_opt!((ptr.tag(), ptr.val()), (Tag::Expr(Cons), IVal::Tuple2(idx)) => {
            let [car, cdr] = self.core.expect_tuple2(*idx);
            (car, cdr)
        })
    }

    /// Deconstruct a cons-like pointer such that:
    /// * If applied on `nil`, returns `(nil, nil)`
    /// * If applied on a pair `(a . b)`, returns `(a, b)`
    /// * If applied on the empty string, returns `(nil, "")`
    /// * If applied on a string `"abc..."`, returns `('a', "bc...")`
    pub fn car_cdr(&self, ptr: &Ptr) -> Result<(Ptr, Ptr)> {
        match (ptr.tag(), *ptr.val()) {
            (Tag::Expr(Nil), _) => {
                let nil = self.intern_nil();
                Ok((nil, nil))
            }
            (Tag::Expr(Str), IVal::Atom(idx)) => {
                if self.fetch_f(idx) == Some(&F::ZERO) {
                    let empty_str = self.zero(Tag::Expr(Str));
                    Ok((self.intern_nil(), empty_str))
                } else {
                    bail!("Invalid empty string pointer")
                }
            }
            (Tag::Expr(Cons | Str), IVal::Tuple2(idx)) => {
                let [car, cdr] = self
                    .core
                    .fetch_tuple2(idx)
                    .context("couldn't fetch car/cdr")?;
                Ok((*car, *cdr))
            }
            _ => bail!("invalid pointer to extract car/cdr from"),
        }
    }

    /// Simpler version of `car_cdr` that doesn't deconstruct strings
    pub fn car_cdr_simple(&self, ptr: &Ptr) -> Result<(Ptr, Ptr)> {
        match (ptr.tag(), ptr.val()) {
            (Tag::Expr(Nil), _) => {
                let nil = self.intern_nil();
                Ok((nil, nil))
            }
            (Tag::Expr(Cons), IVal::Tuple2(idx)) => {
                let [car, cdr] = self
                    .core
                    .fetch_tuple2(*idx)
                    .context("couldn't fetch car/cdr")?;
                Ok((*car, *cdr))
            }
            _ => bail!("invalid pointer to extract car/cdr (simple) from"),
        }
    }

    /// Interns a sequence of pointers as a cons-list. The terminating element
    /// defaults to `nil` if `last` is `None`
    fn intern_list<I: IntoIterator<Item = Ptr>>(&self, elts: I, last: Option<Ptr>) -> Ptr
    where
        <I as IntoIterator>::IntoIter: DoubleEndedIterator,
    {
        elts.into_iter()
            .rev()
            .fold(last.unwrap_or_else(|| self.intern_nil()), |acc, elt| {
                self.cons(elt, acc)
            })
    }

    /// Interns a sequence of pointers as a proper (`nil`-terminated) cons-list
    #[inline]
    pub fn list<I: IntoIterator<Item = Ptr>>(&self, elts: I) -> Ptr
    where
        <I as IntoIterator>::IntoIter: DoubleEndedIterator,
    {
        self.intern_list(elts, None)
    }

    /// Interns a sequence of pointers as an improper cons-list whose last
    /// element is `last`
    #[inline]
    pub fn improper_list(&self, elts: Vec<Ptr>, last: Ptr) -> Ptr {
        self.intern_list(elts, Some(last))
    }

    /// Fetches a cons list that was interned. Panics if the list is improper.
    pub fn fetch_proper_list(&self, ptr: &Ptr) -> Option<Vec<Ptr>> {
        self.fetch_list(ptr).map(|(list, tail)| {
            assert!(tail.is_none(), "improper list when proper list expected");
            list
        })
    }

    /// Fetches a cons list that was interned. If the list is improper, the second
    /// element of the returned pair will carry the improper terminating value
    pub fn fetch_list(&self, ptr: &Ptr) -> Option<(Vec<Ptr>, Option<Ptr>)> {
        if *ptr == self.intern_nil() {
            return Some((vec![], None));
        }
        match (ptr.tag(), ptr.val()) {
            (Tag::Expr(Nil), _) => panic!("Malformed nil expression"),
            (Tag::Expr(Cons), IVal::Tuple2(mut idx)) => {
                let mut list = vec![];
                let mut last = None;
                while let Some([car, cdr]) = self.core.fetch_tuple2(idx) {
                    list.push(*car);
                    match cdr.tag() {
                        Tag::Expr(Nil) => break,
                        Tag::Expr(Cons) => {
                            idx = cdr.get_tuple2_idx()?;
                        }
                        _ => {
                            last = Some(*cdr);
                            break;
                        }
                    }
                }
                Some((list, last))
            }
            _ => None,
        }
    }

    /// Fetches an environment
    pub fn fetch_env(&self, ptr: &Ptr) -> Option<Vec<(Ptr, Ptr)>> {
        if ptr.tag() != &Tag::Expr(Env) {
            return None;
        }
        if ptr == &self.intern_empty_env() {
            return Some(vec![]);
        }

        let mut env_val_mut = ptr.val();
        let mut list = vec![];
        let empty_env_val = *self.intern_empty_env().val();
        while let Some([sym, v, env]) = self.core.fetch_compact_by_val(env_val_mut) {
            list.push((*sym, *v));
            let env_val = env.val();
            if env_val == &empty_env_val {
                break;
            }
            env_val_mut = env_val;
        }
        Some(list)
    }

    /// Fetches a provenance
    pub fn fetch_provenance(&self, ptr: &Ptr) -> Option<(Ptr, Ptr, Ptr)> {
        if ptr.tag() != &Tag::Expr(Prov) {
            return None;
        }

        self.core
            .fetch_compact_by_val(ptr.val())
            .map(|[query, v, deps]| {
                let nil = self.intern_nil();
                let deps_val = deps.val();
                let deps = if deps_val == nil.val() {
                    nil
                } else {
                    Ptr::new(Tag::Expr(Prov), *deps_val)
                };

                (*query, *v, deps)
            })
    }

    pub fn intern_syntax(&self, syn: Syntax<F>) -> Ptr {
        match syn {
            Syntax::Num(_, x) => self.num(x.into_scalar()),
            Syntax::UInt(_, x) => self.u64(x.into()),
            Syntax::Char(_, x) => self.char(x),
            Syntax::Symbol(_, x) => self.intern_symbol(&x),
            Syntax::String(_, x) => self.intern_string(&x),
            Syntax::Quote(_, x) => self.list(vec![
                self.intern_symbol(&lurk_sym("quote")),
                self.intern_syntax(*x),
            ]),
            Syntax::List(_, xs) => self.list(xs.into_iter().map(|x| self.intern_syntax(x))),
            Syntax::Improper(_, xs, y) => self.improper_list(
                xs.into_iter().map(|x| self.intern_syntax(x)).collect(),
                self.intern_syntax(*y),
            ),
        }
    }

    pub fn read(&self, state: StateRcCell, input: &str) -> Result<Ptr> {
        match preceded(
            syntax::parse_space,
            syntax::parse_syntax(state, false, false),
        )
        .parse(Span::new(input))
        {
            Ok((_, x)) => Ok(self.intern_syntax(x)),
            Err(e) => bail!("{}", e),
        }
    }

    pub fn read_maybe_meta<'a>(
        &self,
        state: StateRcCell,
        input: &'a str,
    ) -> Result<(usize, Span<'a>, Ptr, bool), Error> {
        match preceded(syntax::parse_space, syntax::parse_maybe_meta(state, false))
            .parse(input.into())
        {
            Ok((i, Some((is_meta, x)))) => {
                let from_offset = x
                    .get_pos()
                    .get_from_offset()
                    .expect("Parsed syntax should have its Pos set");
                Ok((from_offset, i, self.intern_syntax(x), is_meta))
            }
            Ok((_, None)) => Err(Error::NoInput),
            Err(e) => Err(Error::Syntax(format!("{}", e))),
        }
    }

    #[inline]
    pub fn read_with_default_state(&self, input: &str) -> Result<Ptr> {
        self.read(State::init_lurk_state().rccell(), input)
    }

    /// Constructs a vector of scalars that correspond to tags and hashes computed
    /// from a slice of `Ptr`s turned into `ZPtr`s
    pub fn to_scalar_vector(&self, ptrs: &[Ptr]) -> Vec<F> {
        ptrs.iter()
            .fold(Vec::with_capacity(2 * ptrs.len()), |mut acc, ptr| {
                let z_ptr = self.hash_ptr(ptr);
                let tag = z_ptr.tag().to_field();
                let payload = z_ptr.val().0;
                acc.push(tag);
                acc.push(payload);
                acc
            })
    }
}

impl Ptr {
    pub fn fmt_to_string<F: LurkField>(&self, store: &Store<F>, state: &State) -> String {
        match self.tag() {
            Tag::Expr(t) => match t {
                Nil => {
                    let Some(sym) = store.fetch_symbol(self) else {
                        return "<Opaque Nil>".into();
                    };
                    state.fmt_to_string(&sym.into())
                }
                Sym => {
                    let Some(sym) = store.fetch_sym(self) else {
                        return "<Opaque Sym>".into();
                    };
                    state.fmt_to_string(&sym.into())
                }
                Key => {
                    let Some(key) = store.fetch_key(self) else {
                        return "<Opaque Key>".into();
                    };
                    state.fmt_to_string(&key.into())
                }
                Str => {
                    let Some(str) = store.fetch_string(self) else {
                        return "<Opaque Str>".into();
                    };
                    format!("\"{str}\"")
                }
                Char => {
                    if let Some(c) = store.fetch_f_by_val(self.val()).and_then(F::to_char) {
                        format!("\'{c}\'")
                    } else {
                        "<Malformed Char>".into()
                    }
                }
                Cons => {
                    let Some((list, non_nil)) = store.fetch_list(self) else {
                        return "<Opaque Cons>".into();
                    };
                    let list = list
                        .iter()
                        .map(|p| p.fmt_to_string(store, state))
                        .collect::<Vec<_>>();
                    let Some(non_nil) = non_nil else {
                        return format!("({})", list.join(" "));
                    };
                    format!(
                        "({} . {})",
                        list.join(" "),
                        non_nil.fmt_to_string(store, state)
                    )
                }
                Num => {
                    let Some(f) = store.fetch_f_by_val(self.val()) else {
                        return "<Malformed Num>".into();
                    };
                    let Some(u) = f.to_u64() else {
                        return format!("0x{}", f.hex_digits());
                    };
                    u.to_string()
                }
                U64 => {
                    if let Some(u) = store.fetch_f_by_val(self.val()).and_then(F::to_u64) {
                        format!("{u}u64")
                    } else {
                        "<Malformed U64>".into()
                    }
                }
                Fun => {
                    let Some(idx) = self.val().get_tuple4_idx() else {
                        return "<Malformed Fun>".into();
                    };
                    let Some([vars, body, _, _]) = store.core.fetch_tuple4(idx) else {
                        return "<Opaque Fun>".into();
                    };
                    match vars.tag() {
                        Tag::Expr(Nil) => {
                            format!("<FUNCTION () {}>", body.fmt_to_string(store, state))
                        }
                        Tag::Expr(Cons) => {
                            format!(
                                "<FUNCTION {} {}>",
                                vars.fmt_to_string(store, state),
                                body.fmt_to_string(store, state)
                            )
                        }
                        _ => "<Malformed Fun>".into(),
                    }
                }
                Rec => {
                    let Some(idx) = self.val().get_tuple4_idx() else {
                        return "<Malformed Rec>".into();
                    };
                    let Some([vars, body, _, _]) = store.core.fetch_tuple4(idx) else {
                        return "<Opaque Rec>".into();
                    };
                    match vars.tag() {
                        Tag::Expr(Nil) => {
                            format!("<REC_FUNCTION () {}>", body.fmt_to_string(store, state))
                        }
                        Tag::Expr(Cons) => {
                            format!(
                                "<REC_FUNCTION {} {}>",
                                vars.fmt_to_string(store, state),
                                body.fmt_to_string(store, state)
                            )
                        }
                        _ => "<Malformed Rec>".into(),
                    }
                }
                Thunk => {
                    let Some(idx) = self.val().get_tuple2_idx() else {
                        return "<Malformed Thunk>".into();
                    };
                    let Some([val, cont]) = store.core.fetch_tuple2(idx) else {
                        return "<Opaque Thunk>".into();
                    };
                    format!(
                        "Thunk{{ value: {} => cont: {} }}",
                        val.fmt_to_string(store, state),
                        cont.fmt_to_string(store, state)
                    )
                }
                Comm => {
                    let Some(idx) = self.val().get_atom_idx() else {
                        return "<Malformed Comm>".into();
                    };
                    let f = store.expect_f(idx);
                    if store.core.can_open(&FWrap(*f)) {
                        format!("(comm 0x{})", f.hex_digits())
                    } else {
                        format!("<Opaque Comm 0x{}>", f.hex_digits())
                    }
                }
                Cproc => {
                    let Some(idx) = self.val().get_tuple2_idx() else {
                        return "<Malformed Cproc>".into();
                    };
                    let Some([cproc_name, args]) = store.core.fetch_tuple2(idx) else {
                        return "<Opaque Cproc>".into();
                    };
                    format!(
                        "<COPROC {} {}>",
                        cproc_name.fmt_to_string(store, state),
                        args.fmt_to_string(store, state)
                    )
                }
                Env => {
                    let Some(env) = store.fetch_env(self) else {
                        return "<Opaque Env>".into();
                    };
                    let list = env
                        .iter()
                        .map(|(sym, val)| {
                            format!(
                                "({} . {})",
                                sym.fmt_to_string(store, state),
                                val.fmt_to_string(store, state)
                            )
                        })
                        .collect::<Vec<_>>();
                    format!("<ENV ({})>", list.join(" "))
                }
                Prov => {
                    let Some((query, val, deps)) = store.fetch_provenance(self) else {
                        return "<Opaque Prov>".into();
                    };
                    let nil = store.intern_nil();
                    if store.ptr_eq(&deps, &nil) {
                        format!(
                            "<Prov ({} . {})>",
                            query.fmt_to_string(store, state),
                            val.fmt_to_string(store, state),
                        )
                    } else {
                        format!(
                            "<Prov ({} . {}) . {}>",
                            query.fmt_to_string(store, state),
                            val.fmt_to_string(store, state),
                            deps.fmt_to_string(store, state)
                        )
                    }
                }
            },
            Tag::Cont(t) => match t {
                Outermost => "Outermost".into(),
                Dummy => "Dummy".into(),
                ContTag::Error => "Error".into(),
                Terminal => "Terminal".into(),
                Call0 => self.fmt_cont2_to_string("Call0", "saved_env", store, state),
                Call => {
                    self.fmt_cont3_to_string("Call", ("unevaled_arg", "saved_env"), store, state)
                }
                Call2 => self.fmt_cont3_to_string("Call2", ("function", "saved_env"), store, state),
                Tail => self.fmt_cont2_to_string("Tail", "saved_env", store, state),
                Lookup => self.fmt_cont2_to_string("Lookup", "saved_env", store, state),
                Unop => self.fmt_cont2_to_string("Unop", "saved_env", store, state),
                Binop => self.fmt_cont4_to_string(
                    "Binop",
                    ("operator", "saved_env", "unevaled_args"),
                    store,
                    state,
                ),
                Binop2 => {
                    self.fmt_cont3_to_string("Binop2", ("operator", "evaled_arg"), store, state)
                }
                If => self.fmt_cont2_to_string("If", "unevaled_args", store, state),
                Let => self.fmt_cont4_to_string("Let", ("var", "saved_env", "body"), store, state),
                LetRec => {
                    self.fmt_cont4_to_string("LetRec", ("var", "saved_env", "body"), store, state)
                }
                Emit => "Emit <CONTINUATION>".into(),
                ContTag::Cproc => self.fmt_cont4_to_string(
                    "Cproc",
                    ("name", "unevaled_args", "evaled_args"),
                    store,
                    state,
                ),
                StreamStart => "StreamStart".into(),
                StreamDispatch => "StreamDispatch".into(),
                StreamPause => "StreamPause".into(),
            },
            Tag::Op1(op) => op.to_string(),
            Tag::Op2(op) => op.to_string(),
        }
    }

    pub fn fmt_to_string_simple<F: LurkField>(&self, store: &Store<F>) -> String {
        self.fmt_to_string(store, crate::state::initial_lurk_state())
    }

    fn fmt_cont2_to_string<F: LurkField>(
        &self,
        name: &str,
        field: &str,
        store: &Store<F>,
        state: &State,
    ) -> String {
        {
            let Some(idx) = self.val().get_tuple4_idx() else {
                return format!("<Malformed {name}>");
            };
            let Some([a, cont, _, _]) = store.core.fetch_tuple4(idx) else {
                return format!("<Opaque {name}>");
            };
            format!(
                "{name}{{ {field}: {}, continuation: {} }}",
                a.fmt_to_string(store, state),
                cont.fmt_to_string(store, state)
            )
        }
    }

    fn fmt_cont3_to_string<F: LurkField>(
        &self,
        name: &str,
        fields: (&str, &str),
        store: &Store<F>,
        state: &State,
    ) -> String {
        {
            let Some(idx) = self.val().get_tuple4_idx() else {
                return format!("<Malformed {name}>");
            };
            let Some([a, b, cont, _]) = store.core.fetch_tuple4(idx) else {
                return format!("<Opaque {name}>");
            };
            let (fa, fb) = fields;
            format!(
                "{name}{{ {fa}: {}, {fb}: {}, continuation: {} }}",
                a.fmt_to_string(store, state),
                b.fmt_to_string(store, state),
                cont.fmt_to_string(store, state)
            )
        }
    }

    fn fmt_cont4_to_string<F: LurkField>(
        &self,
        name: &str,
        fields: (&str, &str, &str),
        store: &Store<F>,
        state: &State,
    ) -> String {
        {
            let Some(idx) = self.val().get_tuple4_idx() else {
                return format!("<Malformed {name}>");
            };
            let Some([a, b, c, cont]) = store.core.fetch_tuple4(idx) else {
                return format!("<Opaque {name}>");
            };
            let (fa, fb, fc) = fields;
            format!(
                "{name}{{ {fa}: {}, {fb}: {}, {fc}: {}, continuation: {} }}",
                a.fmt_to_string(store, state),
                b.fmt_to_string(store, state),
                c.fmt_to_string(store, state),
                cont.fmt_to_string(store, state)
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use expect_test::expect;
    use ff::Field;
    use halo2curves::bn256::Fr;
    use proptest::prelude::*;

    use crate::{
        field::LurkField,
        lem::{pointers::IVal, Tag},
        parser::position::Pos,
        state::{initial_lurk_state, lurk_sym},
        syntax::Syntax,
        tag::{ExprTag, Tag as TagTrait},
        Num, Symbol,
    };

    use super::{Ptr, Store};

    #[test]
    fn test_ptr_hashing_safety() {
        let string = String::from_utf8(vec![b'0'; 4096]).unwrap();
        let store = Store::<Fr>::default();
        let ptr = store.intern_string(&string);
        // `hash_ptr_val_unsafe` would overflow the stack, whereas `hash_ptr_val` works
        let x = store.core.hash_ptr_val(ptr.val());

        let store = Store::<Fr>::default();
        let ptr = store.intern_string(&string);
        store.hydrate_z_cache();
        // but `hash_ptr_val_unsafe` works just fine after manual hydration
        let y = store.core.hash_ptr_val_unsafe(ptr.val());

        // and, of course, `y` and `x` should be equal
        assert_eq!(x, y);
    }

    #[test]
    fn test_car_cdr() {
        let store = Store::<Fr>::default();

        // empty list
        let nil = store.intern_nil();
        let (car, cdr) = store.car_cdr(&nil).unwrap();
        assert_eq!((&car, &cdr), (&nil, &nil));
        let (car, cdr) = store.car_cdr_simple(&nil).unwrap();
        assert_eq!((&car, &cdr), (&nil, &nil));

        // regular cons
        let one = store.num_u64(1);
        let a = store.char('a');
        let one_a = store.cons(one, a);
        let (car, cdr) = store.car_cdr(&one_a).unwrap();
        assert_eq!((&one, &a), (&car, &cdr));
        let (car, cdr) = store.car_cdr_simple(&one_a).unwrap();
        assert_eq!((&one, &a), (&car, &cdr));

        // string
        let abc = store.intern_string("abc");
        let bc = store.intern_string("bc");
        let (car, cdr) = store.car_cdr(&abc).unwrap();
        assert_eq!((&a, &bc), (&car, &cdr));

        // empty string
        let empty_str = store.intern_string("");
        let (car, cdr) = store.car_cdr(&empty_str).unwrap();
        assert_eq!((&nil, &empty_str), (&car, &cdr));
    }

    #[test]
    fn test_list() {
        let store = Store::<Fr>::default();
        let state = initial_lurk_state();

        // empty list
        let list = store.list(vec![]);
        let nil = store.intern_nil();
        assert_eq!(&list, &nil);
        let (elts, non_nil) = store.fetch_list(&list).unwrap();
        assert!(elts.is_empty());
        assert!(non_nil.is_none());

        // proper list
        let a = store.char('a');
        let b = store.char('b');
        let list = store.list(vec![a, b]);
        assert_eq!(list.fmt_to_string(&store, state), "('a' 'b')");
        let (elts, non_nil) = store.fetch_list(&list).unwrap();
        assert_eq!(elts.len(), 2);
        assert_eq!((&elts[0], &elts[1]), (&a, &b));
        assert!(non_nil.is_none());

        // improper list
        let c = store.char('c');
        let b_c = store.cons(b, c);
        let a_b_c = store.cons(a, b_c);
        let a_b_c_ = store.improper_list(vec![a, b], c);
        assert_eq!(a_b_c, a_b_c_);
        assert_eq!(a_b_c.fmt_to_string(&store, state), "('a' 'b' . 'c')");
        let (elts, non_nil) = store.fetch_list(&a_b_c).unwrap();
        assert_eq!(elts.len(), 2);
        assert_eq!((&elts[0], &elts[1]), (&a, &b));
        assert_eq!(non_nil, Some(c));
    }

    #[test]
    fn test_basic_hashing() {
        let store = Store::<Fr>::default();
        let zero = Fr::zero();
        let zero_tag = Tag::try_from(0).unwrap();
        let foo = store.intern_atom(zero_tag, zero);

        let z_foo = store.hash_ptr(&foo);
        assert_eq!(z_foo.tag(), &zero_tag);
        assert_eq!(z_foo.val().0, zero);

        let comm = store.hide(zero, foo);
        assert_eq!(comm.tag(), &Tag::Expr(ExprTag::Comm));
        assert_eq!(
            store.expect_f(comm.get_atom_idx().unwrap()),
            &store.core.hasher.hash3(&[zero; 3])
        );

        let ptr2 = store.core.intern_tuple2([foo, foo], zero_tag, None);
        let z_ptr2 = store.hash_ptr(&ptr2);
        assert_eq!(z_ptr2.tag(), &zero_tag);
        assert_eq!(z_ptr2.val().0, store.core.hasher.hash4(&[zero; 4]));

        let ptr3 = store.core.intern_tuple3([foo, foo, foo], zero_tag, None);
        let z_ptr3 = store.hash_ptr(&ptr3);
        assert_eq!(z_ptr3.tag(), &zero_tag);
        assert_eq!(z_ptr3.val().0, store.core.hasher.hash6(&[zero; 6]));

        let ptr4 = store
            .core
            .intern_tuple4([foo, foo, foo, foo], zero_tag, None);
        let z_ptr4 = store.hash_ptr(&ptr4);
        assert_eq!(z_ptr4.tag(), &zero_tag);
        assert_eq!(z_ptr4.val().0, store.core.hasher.hash8(&[zero; 8]));
    }

    #[test]
    fn test_display_opaque_knowledge() {
        // bob creates a list
        let store = Store::<Fr>::default();
        let one = store.num_u64(1);
        let two = store.num_u64(2);
        let one_two = store.cons(one, two);
        let hi = store.intern_string("hi");
        let z1 = store.hash_ptr(&hi);
        let z2 = store.hash_ptr(&one_two);
        let list = store.list(vec![one_two, hi]);
        let z_list = store.hash_ptr(&list);

        // alice uses the hashed elements of the list to show that she
        // can produce the same hash as the original z_list
        let store = Store::<Fr>::default();
        let a1 = store.opaque(z1);
        let a2 = store.opaque(z2);
        let list1 = store.list(vec![a1, a2]);
        let list2 = store.list(vec![a2, a1]);
        let z_list1 = store.hash_ptr(&list1);
        let z_list2 = store.hash_ptr(&list2);

        // one of those lists should match the original
        assert!(z_list == z_list1 || z_list == z_list2);
    }

    #[test]
    fn string_hashing() {
        let s = &Store::<Fr>::default();
        let hi_ptr = s.intern_string("hi");

        let hi_hash_manual = s.core.hasher.hash4(&[
            ExprTag::Char.to_field(),
            Fr::from_char('h'),
            ExprTag::Str.to_field(),
            s.core.hasher.hash4(&[
                ExprTag::Char.to_field(),
                Fr::from_char('i'),
                ExprTag::Str.to_field(),
                Fr::ZERO,
            ]),
        ]);

        let hi_hash = s.hash_ptr(&hi_ptr).val().0;
        assert_eq!(hi_hash, hi_hash_manual);
    }

    #[test]
    fn symbol_hashing() {
        let s = &Store::<Fr>::default();
        let foo_ptr = s.intern_string("foo");
        let bar_ptr = s.intern_string("bar");
        let foo_bar_ptr = s.intern_symbol(&Symbol::sym_from_vec(vec!["foo".into(), "bar".into()]));

        let foo_z_ptr = s.hash_ptr(&foo_ptr);
        let bar_z_ptr = s.hash_ptr(&bar_ptr);

        let foo_bar_hash_manual = s.core.hasher.hash4(&[
            ExprTag::Str.to_field(),
            bar_z_ptr.val().0,
            ExprTag::Sym.to_field(),
            s.core.hasher.hash4(&[
                ExprTag::Str.to_field(),
                foo_z_ptr.val().0,
                ExprTag::Sym.to_field(),
                Fr::ZERO,
            ]),
        ]);

        let foo_bar_hash = s.hash_ptr(&foo_bar_ptr).val().0;
        assert_eq!(foo_bar_hash, foo_bar_hash_manual);
    }

    // helper function to test syntax interning roundtrip
    fn fetch_syntax(ptr: Ptr, store: &Store<Fr>) -> Syntax<Fr> {
        match ptr.parts() {
            (Tag::Expr(ExprTag::Num), IVal::Atom(idx)) => {
                Syntax::Num(Pos::No, Num::Scalar(*store.expect_f(*idx)))
            }
            (Tag::Expr(ExprTag::Char), IVal::Atom(idx)) => {
                Syntax::Char(Pos::No, store.expect_f(*idx).to_char().unwrap())
            }
            (Tag::Expr(ExprTag::U64), IVal::Atom(idx)) => Syntax::UInt(
                Pos::No,
                crate::UInt::U64(store.expect_f(*idx).to_u64_unchecked()),
            ),
            (Tag::Expr(ExprTag::Sym | ExprTag::Key), IVal::Atom(_) | IVal::Tuple2(_)) => {
                Syntax::Symbol(Pos::No, store.fetch_symbol(&ptr).unwrap().into())
            }
            (Tag::Expr(ExprTag::Str), IVal::Atom(_) | IVal::Tuple2(_)) => {
                Syntax::String(Pos::No, store.fetch_string(&ptr).unwrap())
            }
            (Tag::Expr(ExprTag::Cons), IVal::Tuple2(_)) => {
                let (elts, last) = store.fetch_list(&ptr).unwrap();
                let elts = elts
                    .into_iter()
                    .map(|e| fetch_syntax(e, store))
                    .collect::<Vec<_>>();
                if let Some(last) = last {
                    Syntax::Improper(Pos::No, elts, fetch_syntax(last, store).into())
                } else {
                    Syntax::List(Pos::No, elts)
                }
            }
            (Tag::Expr(ExprTag::Nil), IVal::Tuple2(_)) => {
                Syntax::Symbol(Pos::No, lurk_sym("nil").into())
            }
            _ => unreachable!(),
        }
    }

    proptest! {
        #[test]
        fn syntax_roundtrip(x in any::<Syntax<Fr>>()) {
            let store = Store::<Fr>::default();
            let ptr1 = store.intern_syntax(x);
            let y = fetch_syntax(ptr1, &store);
            let ptr2 = store.intern_syntax(y);
            assert_eq!(ptr1, ptr2);
        }
    }

    #[test]
    fn comm_printing() {
        let store = Store::<Fr>::default();
        let ptr = store.num_u64(0);

        let opq_comm = ptr.cast(Tag::Expr(ExprTag::Comm));
        expect!["<Opaque Comm 0x0000000000000000000000000000000000000000000000000000000000000000>"]
            .assert_eq(&opq_comm.fmt_to_string_simple(&store));

        let comm = store.commit(ptr);
        expect!["(comm 0x1d501baeefe83acf0e7137180b091834f542a5059dbaf99ec82c5e19d3bb9201)"]
            .assert_eq(&comm.fmt_to_string_simple(&store));
    }
}
