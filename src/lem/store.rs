use anyhow::{bail, Context, Result};
use arc_swap::ArcSwap;
use bellpepper::util_cs::witness_cs::SizedWitness;
use elsa::{
    sync::index_set::FrozenIndexSet,
    sync::{FrozenMap, FrozenVec},
};
use indexmap::IndexSet;
use neptune::Poseidon;
use nom::{sequence::preceded, Parser};
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use std::{cell::RefCell, rc::Rc, sync::Arc};

use crate::{
    field::{FWrap, LurkField},
    hash::{InversePoseidonCache, PoseidonCache},
    lem::Tag,
    parser::{syntax, Error, Span},
    state::{lurk_sym, user_sym, State},
    symbol::Symbol,
    syntax::Syntax,
    tag::ContTag::{
        self, Binop, Binop2, Call, Call0, Call2, Dummy, Emit, If, Let, LetRec, Lookup, Outermost,
        Tail, Terminal, Unop,
    },
    tag::ExprTag::{Char, Comm, Cons, Cproc, Fun, Key, Nil, Num, Str, Sym, Thunk, U64},
    tag::Tag as TagTrait,
};

use super::pointers::{Ptr, RawPtr, ZPtr};

#[derive(Debug)]
pub struct Store<F: LurkField> {
    f_elts: FrozenIndexSet<Box<FWrap<F>>>,
    hash3: FrozenIndexSet<Box<[RawPtr; 3]>>,
    hash4: FrozenIndexSet<Box<[RawPtr; 4]>>,
    hash6: FrozenIndexSet<Box<[RawPtr; 6]>>,
    hash8: FrozenIndexSet<Box<[RawPtr; 8]>>,

    string_ptr_cache: FrozenMap<String, Box<Ptr>>,
    symbol_ptr_cache: FrozenMap<Symbol, Box<Ptr>>,

    ptr_string_cache: FrozenMap<Ptr, String>,
    ptr_symbol_cache: FrozenMap<Ptr, Box<Symbol>>,

    pub poseidon_cache: PoseidonCache<F>,
    pub inverse_poseidon_cache: InversePoseidonCache<F>,

    dehydrated: ArcSwap<FrozenVec<Box<RawPtr>>>,
    z_cache: FrozenMap<RawPtr, Box<FWrap<F>>>,
    inverse_z_cache: FrozenMap<FWrap<F>, Box<RawPtr>>,

    // cached indices for the hashes of 3, 4, 6 and 8 padded zeros
    pub hash3zeros_idx: usize,
    pub hash4zeros_idx: usize,
    pub hash6zeros_idx: usize,
    pub hash8zeros_idx: usize,
}

impl<F: LurkField> Default for Store<F> {
    fn default() -> Self {
        let poseidon_cache = PoseidonCache::default();
        let hash3zeros = poseidon_cache.hash3(&[F::ZERO; 3]);
        let hash4zeros = poseidon_cache.hash4(&[F::ZERO; 4]);
        let hash6zeros = poseidon_cache.hash6(&[F::ZERO; 6]);
        let hash8zeros = poseidon_cache.hash8(&[F::ZERO; 8]);

        let f_elts = FrozenIndexSet::default();
        let (hash3zeros_idx, _) = f_elts.insert_probe(FWrap(hash3zeros).into());
        let (hash4zeros_idx, _) = f_elts.insert_probe(FWrap(hash4zeros).into());
        let (hash6zeros_idx, _) = f_elts.insert_probe(FWrap(hash6zeros).into());
        let (hash8zeros_idx, _) = f_elts.insert_probe(FWrap(hash8zeros).into());

        Self {
            f_elts,
            hash3: Default::default(),
            hash4: Default::default(),
            hash6: Default::default(),
            hash8: Default::default(),
            string_ptr_cache: Default::default(),
            symbol_ptr_cache: Default::default(),
            ptr_string_cache: Default::default(),
            ptr_symbol_cache: Default::default(),
            poseidon_cache,
            inverse_poseidon_cache: Default::default(),
            dehydrated: Default::default(),
            z_cache: Default::default(),
            inverse_z_cache: Default::default(),
            hash3zeros_idx,
            hash4zeros_idx,
            hash6zeros_idx,
            hash8zeros_idx,
        }
    }
}

impl<F: LurkField> Store<F> {
    /// Cost of poseidon hash with arity 3, including the input
    #[inline]
    pub fn hash3_cost(&self) -> usize {
        Poseidon::new(self.poseidon_cache.constants.c3()).num_aux() + 1
    }

    /// Cost of poseidon hash with arity 4, including the input
    #[inline]
    pub fn hash4_cost(&self) -> usize {
        Poseidon::new(self.poseidon_cache.constants.c4()).num_aux() + 1
    }

    /// Cost of poseidon hash with arity 6, including the input
    #[inline]
    pub fn hash6_cost(&self) -> usize {
        Poseidon::new(self.poseidon_cache.constants.c6()).num_aux() + 1
    }

    /// Cost of poseidon hash with arity 8, including the input
    #[inline]
    pub fn hash8_cost(&self) -> usize {
        Poseidon::new(self.poseidon_cache.constants.c8()).num_aux() + 1
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

    // Since the `generic_const_exprs` feature is still unstable, we cannot substitute `N * 2`
    // for generic const `P` and remove it completely, so we must keep it and do a dynamic assertion
    // that it equals `N * 2`. This is not very ergonomic though, since we must add turbofishes
    // like `::<6, 3>` instead of the simpler `::<3>`. Could we maybe create a macro for these functions?
    #[inline]
    pub fn ptrs_to_raw_ptrs<const N: usize, const P: usize>(&self, ptrs: &[Ptr; P]) -> [RawPtr; N] {
        assert_eq!(P * 2, N);
        let mut raw_ptrs = [self.raw_zero(); N];
        for i in 0..P {
            raw_ptrs[2 * i] = self.tag(*ptrs[i].tag());
            raw_ptrs[2 * i + 1] = *ptrs[i].pay();
        }
        raw_ptrs
    }

    #[inline]
    pub fn raw_ptrs_to_ptrs<const N: usize, const P: usize>(
        &self,
        raw_ptrs: &[RawPtr; N],
    ) -> Option<[Ptr; P]> {
        assert_eq!(P * 2, N);
        let mut ptrs = [self.dummy(); P];
        for i in 0..P {
            let tag = self.fetch_tag(&raw_ptrs[2 * i])?;
            ptrs[i] = Ptr::new(tag, raw_ptrs[2 * i + 1])
        }
        Some(ptrs)
    }

    #[inline]
    pub fn intern_f(&self, f: F) -> (usize, bool) {
        self.f_elts.insert_probe(Box::new(FWrap(f)))
    }

    /// Creates an atom `RawPtr` which points to a cached element of the finite
    /// field `F`
    pub fn intern_raw_atom(&self, f: F) -> RawPtr {
        let (idx, _) = self.intern_f(f);
        RawPtr::Atom(idx)
    }

    pub fn intern_atom(&self, tag: Tag, f: F) -> Ptr {
        Ptr::new(tag, self.intern_raw_atom(f))
    }

    /// Creates a `RawPtr` that's a parent of `N` children
    pub fn intern_raw_ptrs<const N: usize>(&self, ptrs: [RawPtr; N]) -> RawPtr {
        let (ptr, inserted) = self.intern_raw_ptrs_internal::<N>(ptrs);
        if inserted {
            // this is for `hydrate_z_cache`
            self.dehydrated.load().push(Box::new(ptr));
        }
        ptr
    }

    /// Similar to `intern_raw_ptrs` but doesn't add the resulting pointer to
    /// `dehydrated`. This function is used when converting a `ZStore` to a
    /// `Store`.
    pub fn intern_raw_ptrs_hydrated<const N: usize>(
        &self,
        ptrs: [RawPtr; N],
        z: FWrap<F>,
    ) -> RawPtr {
        let (ptr, _) = self.intern_raw_ptrs_internal::<N>(ptrs);
        self.z_cache.insert(ptr, Box::new(z));
        self.inverse_z_cache.insert(z, Box::new(ptr));
        ptr
    }

    #[inline]
    fn intern_raw_ptrs_internal<const N: usize>(&self, ptrs: [RawPtr; N]) -> (RawPtr, bool) {
        macro_rules! intern {
            ($Hash:ident, $hash:ident, $n:expr) => {{
                let ptrs = unsafe { std::mem::transmute::<&[RawPtr; N], &[RawPtr; $n]>(&ptrs) };
                let (idx, inserted) = self.$hash.insert_probe(Box::new(*ptrs));
                (RawPtr::$Hash(idx), inserted)
            }};
        }
        match N {
            3 => intern!(Hash3, hash3, 3),
            4 => intern!(Hash4, hash4, 4),
            6 => intern!(Hash6, hash6, 6),
            8 => intern!(Hash8, hash8, 8),
            _ => unimplemented!(),
        }
    }

    /// Creates a `Ptr` that's a parent of `N` children
    pub fn intern_ptrs<const N: usize, const P: usize>(&self, tag: Tag, ptrs: [Ptr; P]) -> Ptr {
        let raw_ptrs = self.ptrs_to_raw_ptrs::<N, P>(&ptrs);
        let pay = self.intern_raw_ptrs::<N>(raw_ptrs);
        Ptr::new(tag, pay)
    }

    /// Similar to `intern_ptrs` but doesn't add the resulting pointer to
    /// `dehydrated`. This function is used when converting a `ZStore` to a
    /// `Store`.
    pub fn intern_ptrs_hydrated<const N: usize, const P: usize>(
        &self,
        tag: Tag,
        ptrs: [Ptr; P],
        z: FWrap<F>,
    ) -> Ptr {
        let raw_ptrs = self.ptrs_to_raw_ptrs::<N, P>(&ptrs);
        let pay = self.intern_raw_ptrs_hydrated::<N>(raw_ptrs, z);
        Ptr::new(tag, pay)
    }

    #[inline]
    pub fn fetch_f(&self, idx: usize) -> Option<&F> {
        self.f_elts.get_index(idx).map(|fw| &fw.0)
    }

    #[inline]
    pub fn fetch_raw_ptrs<const N: usize>(&self, idx: usize) -> Option<&[RawPtr; N]> {
        macro_rules! fetch {
            ($hash:ident, $n:expr) => {{
                let ptrs = self.$hash.get_index(idx)?;
                let ptrs = unsafe { std::mem::transmute::<&[RawPtr; $n], &[RawPtr; N]>(ptrs) };
                Some(ptrs)
            }};
        }
        match N {
            3 => fetch!(hash3, 3),
            4 => fetch!(hash4, 4),
            6 => fetch!(hash6, 6),
            8 => fetch!(hash8, 8),
            _ => unimplemented!(),
        }
    }

    #[inline]
    pub fn fetch_ptrs<const N: usize, const P: usize>(&self, idx: usize) -> Option<[Ptr; P]> {
        assert_eq!(P * 2, N);
        let raw_ptrs = self.fetch_raw_ptrs::<N>(idx)?;
        self.raw_ptrs_to_ptrs(raw_ptrs)
    }

    #[inline]
    pub fn expect_f(&self, idx: usize) -> &F {
        self.fetch_f(idx).expect("Index missing from f_elts")
    }

    #[inline]
    pub fn expect_raw_ptrs<const N: usize>(&self, idx: usize) -> &[RawPtr; N] {
        self.fetch_raw_ptrs::<N>(idx)
            .expect("Index missing from store")
    }

    #[inline]
    pub fn expect_ptrs<const N: usize, const P: usize>(&self, idx: usize) -> [Ptr; P] {
        self.fetch_ptrs::<N, P>(idx)
            .expect("Index missing from store")
    }

    // TODO eventually deprecate these functions
    #[inline]
    pub fn intern_2_ptrs(&self, tag: Tag, a: Ptr, b: Ptr) -> Ptr {
        self.intern_ptrs::<4, 2>(tag, [a, b])
    }
    #[inline]
    pub fn intern_3_ptrs(&self, tag: Tag, a: Ptr, b: Ptr, c: Ptr) -> Ptr {
        self.intern_ptrs::<6, 3>(tag, [a, b, c])
    }
    #[inline]
    pub fn intern_4_ptrs(&self, tag: Tag, a: Ptr, b: Ptr, c: Ptr, d: Ptr) -> Ptr {
        self.intern_ptrs::<8, 4>(tag, [a, b, c, d])
    }
    #[inline]
    pub fn intern_2_ptrs_hydrated(&self, tag: Tag, a: Ptr, b: Ptr, z: ZPtr<F>) -> Ptr {
        self.intern_ptrs_hydrated::<4, 2>(tag, [a, b], FWrap(*z.value()))
    }
    #[inline]
    pub fn intern_3_ptrs_hydrated(&self, tag: Tag, a: Ptr, b: Ptr, c: Ptr, z: ZPtr<F>) -> Ptr {
        self.intern_ptrs_hydrated::<6, 3>(tag, [a, b, c], FWrap(*z.value()))
    }
    #[inline]
    pub fn intern_4_ptrs_hydrated(
        &self,
        tag: Tag,
        a: Ptr,
        b: Ptr,
        c: Ptr,
        d: Ptr,
        z: ZPtr<F>,
    ) -> Ptr {
        self.intern_ptrs_hydrated::<8, 4>(tag, [a, b, c, d], FWrap(*z.value()))
    }
    #[inline]
    pub fn fetch_2_ptrs(&self, idx: usize) -> Option<[Ptr; 2]> {
        self.fetch_ptrs::<4, 2>(idx)
    }
    #[inline]
    pub fn fetch_3_ptrs(&self, idx: usize) -> Option<[Ptr; 3]> {
        self.fetch_ptrs::<6, 3>(idx)
    }
    #[inline]
    pub fn fetch_4_ptrs(&self, idx: usize) -> Option<[Ptr; 4]> {
        self.fetch_ptrs::<8, 4>(idx)
    }
    #[inline]
    pub fn expect_2_ptrs(&self, idx: usize) -> [Ptr; 2] {
        self.fetch_2_ptrs(idx).expect("Index missing from store")
    }
    #[inline]
    pub fn expect_3_ptrs(&self, idx: usize) -> [Ptr; 3] {
        self.fetch_3_ptrs(idx).expect("Index missing from store")
    }
    #[inline]
    pub fn expect_4_ptrs(&self, idx: usize) -> [Ptr; 4] {
        self.fetch_4_ptrs(idx).expect("Index missing from store")
    }

    #[inline]
    pub fn tag(&self, tag: Tag) -> RawPtr {
        self.intern_raw_atom(tag.to_field())
    }

    #[inline]
    pub fn fetch_tag(&self, ptr: &RawPtr) -> Option<Tag> {
        let idx = ptr.get_atom()?;
        let f = self.fetch_f(idx)?;
        TagTrait::from_field(f)
    }

    pub fn raw_to_ptr(&self, tag: &RawPtr, pay: &RawPtr) -> Option<Ptr> {
        let tag = self.fetch_tag(tag)?;
        Some(Ptr::new(tag, *pay))
    }

    #[inline]
    pub fn num(&self, f: F) -> Ptr {
        self.intern_atom(Tag::Expr(Num), f)
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
    pub fn char(&self, c: char) -> Ptr {
        self.intern_atom(Tag::Expr(Char), F::from_char(c))
    }

    #[inline]
    pub fn comm(&self, hash: F) -> Ptr {
        self.intern_atom(Tag::Expr(Comm), hash)
    }

    #[inline]
    pub fn raw_zero(&self) -> RawPtr {
        self.intern_raw_atom(F::ZERO)
    }

    #[inline]
    pub fn zero(&self, tag: Tag) -> Ptr {
        Ptr::new(tag, self.raw_zero())
    }

    pub fn is_zero(&self, ptr: &RawPtr) -> bool {
        match ptr {
            RawPtr::Atom(idx) => self.fetch_f(*idx) == Some(&F::ZERO),
            _ => false,
        }
    }

    #[inline]
    pub fn dummy(&self) -> Ptr {
        Ptr::new(Tag::Expr(Nil), self.raw_zero())
    }

    /// Creates an atom pointer from a `ZPtr`, with its hash. Hashing
    /// such pointer will result on the same original `ZPtr`
    #[inline]
    pub fn opaque(&self, z: FWrap<F>) -> RawPtr {
        self.intern_raw_atom(z.0)
    }

    pub fn intern_string(&self, s: &str) -> Ptr {
        if let Some(ptr) = self.string_ptr_cache.get(s) {
            *ptr
        } else {
            let nil_str = Ptr::new(Tag::Expr(Str), self.raw_zero());
            let ptr = s.chars().rev().fold(nil_str, |acc, c| {
                let ptrs = [self.char(c), acc];
                self.intern_ptrs::<4, 2>(Tag::Expr(Str), ptrs)
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
                match *ptr.pay() {
                    RawPtr::Atom(idx) => {
                        if self.fetch_f(idx)? == &F::ZERO {
                            self.ptr_string_cache.insert(ptr, string.clone());
                            return Some(string);
                        } else {
                            return None;
                        }
                    }
                    RawPtr::Hash4(idx) => {
                        let [car_tag, car, cdr_tag, cdr] = self.fetch_raw_ptrs(idx)?;
                        assert_eq!(*car_tag, self.tag(Tag::Expr(Char)));
                        assert_eq!(*cdr_tag, self.tag(Tag::Expr(Str)));
                        match car {
                            RawPtr::Atom(idx) => {
                                let f = self.fetch_f(*idx)?;
                                string.push(f.to_char().expect("malformed char pointer"));
                                ptr = Ptr::new(Tag::Expr(Str), *cdr)
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
        let zero_sym = Ptr::new(Tag::Expr(Sym), self.raw_zero());
        path.iter().fold(zero_sym, |acc, s| {
            let ptrs = [self.intern_string(s), acc];
            self.intern_ptrs::<4, 2>(Tag::Expr(Sym), ptrs)
        })
    }

    pub fn intern_symbol(&self, sym: &Symbol) -> Ptr {
        if let Some(ptr) = self.symbol_ptr_cache.get(sym) {
            *ptr
        } else {
            let path_ptr = self.intern_symbol_path(sym.path());
            let sym_ptr = if sym == &lurk_sym("nil") {
                Ptr::new(Tag::Expr(Nil), *path_ptr.pay())
            } else if sym.is_keyword() {
                Ptr::new(Tag::Expr(Key), *path_ptr.pay())
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
            let [car_tag, car, cdr_tag, cdr] = self.fetch_raw_ptrs(idx)?;
            assert_eq!(*car_tag, self.tag(Tag::Expr(Str)));
            assert_eq!(*cdr_tag, self.tag(Tag::Expr(Sym)));
            let string = self.fetch_string(&Ptr::new(Tag::Expr(Str), *car))?;
            path.push(string);
            match cdr {
                RawPtr::Atom(idx) => {
                    if self.fetch_f(*idx)? == &F::ZERO {
                        path.reverse();
                        return Some(path);
                    } else {
                        return None;
                    }
                }
                RawPtr::Hash4(idx_cdr) => idx = *idx_cdr,
                _ => return None,
            }
        }
    }

    pub fn fetch_symbol(&self, ptr: &Ptr) -> Option<Symbol> {
        if let Some(sym) = self.ptr_symbol_cache.get(ptr) {
            Some(sym.clone())
        } else {
            match (ptr.tag(), ptr.pay()) {
                (Tag::Expr(Sym), RawPtr::Atom(idx)) => {
                    if self.fetch_f(*idx)? == &F::ZERO {
                        let sym = Symbol::root_sym();
                        self.ptr_symbol_cache.insert(*ptr, Box::new(sym.clone()));
                        Some(sym)
                    } else {
                        None
                    }
                }
                (Tag::Expr(Key), RawPtr::Atom(idx)) => {
                    if self.fetch_f(*idx)? == &F::ZERO {
                        let key = Symbol::root_key();
                        self.ptr_symbol_cache.insert(*ptr, Box::new(key.clone()));
                        Some(key)
                    } else {
                        None
                    }
                }
                (Tag::Expr(Sym | Nil), RawPtr::Hash4(idx)) => {
                    let path = self.fetch_symbol_path(*idx)?;
                    let sym = Symbol::sym_from_vec(path);
                    self.ptr_symbol_cache.insert(*ptr, Box::new(sym.clone()));
                    Some(sym)
                }
                (Tag::Expr(Key), RawPtr::Hash4(idx)) => {
                    let path = self.fetch_symbol_path(*idx)?;
                    let key = Symbol::key_from_vec(path);
                    self.ptr_symbol_cache.insert(*ptr, Box::new(key.clone()));
                    Some(key)
                }
                _ => None,
            }
        }
    }

    pub fn fetch_sym(&self, ptr: &Ptr) -> Option<Symbol> {
        if ptr.tag() == &Tag::Expr(Sym) {
            self.fetch_symbol(ptr)
        } else {
            None
        }
    }

    pub fn fetch_key(&self, ptr: &Ptr) -> Option<Symbol> {
        if ptr.tag() == &Tag::Expr(Key) {
            self.fetch_symbol(ptr)
        } else {
            None
        }
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
    pub fn intern_user_symbol(&self, name: &str) -> Ptr {
        self.intern_symbol(&user_sym(name))
    }

    #[inline]
    pub fn key(&self, name: &str) -> Ptr {
        self.intern_symbol(&Symbol::key(&[name.to_string()]))
    }

    #[inline]
    pub fn add_comm(&self, hash: F, secret: F, payload: Ptr) {
        let ptrs = [
            self.intern_raw_atom(secret),
            self.tag(*payload.tag()),
            *payload.pay(),
        ];
        let (idx, _) = self.hash3.insert_probe(Box::new(ptrs));
        let ptr = RawPtr::Hash3(idx);
        let z = FWrap(hash);
        self.z_cache.insert(ptr, Box::new(z));
        self.inverse_z_cache.insert(z, Box::new(ptr));
    }

    #[inline]
    pub fn hide(&self, secret: F, payload: Ptr) -> Ptr {
        self.comm(self.hide_ptr(secret, payload))
    }

    pub fn hide_and_return_z_payload(&self, secret: F, payload: Ptr) -> (F, ZPtr<F>) {
        let z_ptr = self.hash_ptr(&payload);
        let hash = self
            .poseidon_cache
            .hash3(&[secret, z_ptr.tag_field(), *z_ptr.value()]);
        self.add_comm(hash, secret, payload);
        (hash, z_ptr)
    }

    #[inline]
    pub fn commit(&self, payload: Ptr) -> Ptr {
        self.hide(F::NON_HIDING_COMMITMENT_SECRET, payload)
    }

    #[inline]
    pub fn open(&self, hash: F) -> Option<(F, Ptr)> {
        let cached = self.inverse_z_cache.get(&FWrap(hash))?;
        let [f, tag, pay] = self.fetch_raw_ptrs::<3>(cached.get_hash3()?)?;
        let f = self.fetch_f(f.get_atom()?)?;
        let ptr = self.raw_to_ptr(tag, pay)?;
        Some((*f, ptr))
    }

    pub fn hide_ptr(&self, secret: F, payload: Ptr) -> F {
        let hash = self.poseidon_cache.hash3(&[
            secret,
            payload.tag().to_field(),
            self.hash_raw_ptr(payload.pay()).0,
        ]);
        self.add_comm(hash, secret, payload);
        hash
    }

    #[inline]
    pub fn cons(&self, car: Ptr, cdr: Ptr) -> Ptr {
        let ptrs = [car, cdr];
        self.intern_ptrs::<4, 2>(Tag::Expr(Cons), ptrs)
    }

    #[inline]
    pub fn intern_fun(&self, arg: Ptr, body: Ptr, env: Ptr) -> Ptr {
        let ptrs = [arg, body, env, self.dummy()];
        self.intern_ptrs::<8, 4>(Tag::Expr(Fun), ptrs)
    }

    #[inline]
    pub fn cont_outermost(&self) -> Ptr {
        Ptr::new(Tag::Cont(Outermost), RawPtr::Atom(self.hash8zeros_idx))
    }

    #[inline]
    pub fn cont_error(&self) -> Ptr {
        Ptr::new(Tag::Cont(ContTag::Error), RawPtr::Atom(self.hash8zeros_idx))
    }

    #[inline]
    pub fn cont_terminal(&self) -> Ptr {
        Ptr::new(Tag::Cont(Terminal), RawPtr::Atom(self.hash8zeros_idx))
    }

    pub fn car_cdr(&self, ptr: &Ptr) -> Result<(Ptr, Ptr)> {
        match ptr.tag() {
            Tag::Expr(Nil) => {
                let nil = self.intern_nil();
                Ok((nil, nil))
            }
            Tag::Expr(Cons) => {
                let Some(idx) = ptr.pay().get_hash4() else {
                    bail!("malformed cons pointer")
                };
                match self.fetch_raw_ptrs(idx) {
                    Some([car_tag, car, cdr_tag, cdr]) => {
                        let car_ptr = self.raw_to_ptr(car_tag, car).context("Not a pointer")?;
                        let cdr_ptr = self.raw_to_ptr(cdr_tag, cdr).context("Not a pointer")?;
                        Ok((car_ptr, cdr_ptr))
                    }
                    None => bail!("car/cdr not found"),
                }
            }
            Tag::Expr(Str) => {
                if self.is_zero(ptr.pay()) {
                    let nil_str = Ptr::new(Tag::Expr(Str), self.raw_zero());
                    Ok((self.intern_nil(), nil_str))
                } else {
                    let Some(idx) = ptr.pay().get_hash4() else {
                        bail!("malformed str pointer")
                    };
                    match self.fetch_raw_ptrs(idx) {
                        Some([car_tag, car, cdr_tag, cdr]) => {
                            let car_ptr = self.raw_to_ptr(car_tag, car).context("Not a pointer")?;
                            let cdr_ptr = self.raw_to_ptr(cdr_tag, cdr).context("Not a pointer")?;
                            Ok((car_ptr, cdr_ptr))
                        }
                        None => bail!("car/cdr not found"),
                    }
                }
            }
            _ => bail!("invalid pointer to extract car/cdr from"),
        }
    }

    /// Interns a sequence of pointers as a cons-list. The terminating element
    /// defaults to `nil` if `last` is `None`
    fn intern_list(&self, elts: Vec<Ptr>, last: Option<Ptr>) -> Ptr {
        elts.into_iter()
            .rev()
            .fold(last.unwrap_or_else(|| self.intern_nil()), |acc, elt| {
                self.cons(elt, acc)
            })
    }

    /// Interns a sequence of pointers as a proper (`nil`-terminated) cons-list
    #[inline]
    pub fn list(&self, elts: Vec<Ptr>) -> Ptr {
        self.intern_list(elts, None)
    }

    /// Interns a sequence of pointers as an improper cons-list whose last
    /// element is `last`
    #[inline]
    pub fn improper_list(&self, elts: Vec<Ptr>, last: Ptr) -> Ptr {
        self.intern_list(elts, Some(last))
    }

    /// Fetches a cons list that was interned. If the list is improper, the second
    /// element of the returned pair will carry the improper terminating value
    pub fn fetch_list(&self, ptr: &Ptr) -> Option<(Vec<Ptr>, Option<Ptr>)> {
        if *ptr == self.intern_nil() {
            return Some((vec![], None));
        }
        match (ptr.tag(), ptr.pay()) {
            (Tag::Expr(Nil), _) => panic!("Malformed nil expression"),
            (Tag::Expr(Cons), RawPtr::Hash4(mut idx)) => {
                let mut list = vec![];
                let mut last = None;
                while let Some([car_tag, car, cdr_tag, cdr]) = self.fetch_raw_ptrs(idx) {
                    let car_ptr = self.raw_to_ptr(car_tag, car)?;
                    let cdr_ptr = self.raw_to_ptr(cdr_tag, cdr)?;
                    list.push(car_ptr);
                    match cdr_ptr.tag() {
                        Tag::Expr(Nil) => break,
                        Tag::Expr(Cons) => {
                            idx = cdr.get_hash4()?;
                        }
                        _ => {
                            last = Some(cdr_ptr);
                            break;
                        }
                    }
                }
                Some((list, last))
            }
            _ => None,
        }
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
            Syntax::List(_, xs) => {
                self.list(xs.into_iter().map(|x| self.intern_syntax(x)).collect())
            }
            Syntax::Improper(_, xs, y) => self.improper_list(
                xs.into_iter().map(|x| self.intern_syntax(x)).collect(),
                self.intern_syntax(*y),
            ),
        }
    }

    pub fn read(&self, state: Rc<RefCell<State>>, input: &str) -> Result<Ptr> {
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
        state: Rc<RefCell<State>>,
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

    /// Recursively hashes the children of a `Ptr` in order to obtain its
    /// corresponding `ZPtr`. While traversing a `Ptr` tree, it consults the
    /// cache of `Ptr`s that have already been hydrated and also populates this
    /// cache for the new `Ptr`s.
    ///
    /// Warning: without cache hits, this function might blow up Rust's recursion
    /// depth limit. This limitation is circumvented by calling `hydrate_z_cache`
    /// beforehand or by using `hash_ptr` instead, which is slightly slower.
    fn hash_raw_ptr_unsafe(&self, ptr: &RawPtr) -> FWrap<F> {
        match ptr {
            RawPtr::Atom(idx) => FWrap(*self.expect_f(*idx)),
            RawPtr::Hash3(idx) => {
                if let Some(z) = self.z_cache.get(ptr) {
                    *z
                } else {
                    let children_ptrs = self.expect_raw_ptrs::<3>(*idx);
                    let mut children_zs = [F::ZERO; 3];
                    for (idx, child_ptr) in children_ptrs.iter().enumerate() {
                        children_zs[idx] = self.hash_raw_ptr_unsafe(child_ptr).0;
                    }
                    let z = FWrap(self.poseidon_cache.hash3(&children_zs));
                    self.z_cache.insert(*ptr, Box::new(z));
                    self.inverse_z_cache.insert(z, Box::new(*ptr));
                    z
                }
            }
            RawPtr::Hash4(idx) => {
                if let Some(z) = self.z_cache.get(ptr) {
                    *z
                } else {
                    let children_ptrs = self.expect_raw_ptrs::<4>(*idx);
                    let mut children_zs = [F::ZERO; 4];
                    for (idx, child_ptr) in children_ptrs.iter().enumerate() {
                        children_zs[idx] = self.hash_raw_ptr_unsafe(child_ptr).0;
                    }
                    let z = FWrap(self.poseidon_cache.hash4(&children_zs));
                    self.z_cache.insert(*ptr, Box::new(z));
                    self.inverse_z_cache.insert(z, Box::new(*ptr));
                    z
                }
            }
            RawPtr::Hash6(idx) => {
                if let Some(z) = self.z_cache.get(ptr) {
                    *z
                } else {
                    let children_ptrs = self.expect_raw_ptrs::<6>(*idx);
                    let mut children_zs = [F::ZERO; 6];
                    for (idx, child_ptr) in children_ptrs.iter().enumerate() {
                        children_zs[idx] = self.hash_raw_ptr_unsafe(child_ptr).0;
                    }
                    let z = FWrap(self.poseidon_cache.hash6(&children_zs));
                    self.z_cache.insert(*ptr, Box::new(z));
                    self.inverse_z_cache.insert(z, Box::new(*ptr));
                    z
                }
            }
            RawPtr::Hash8(idx) => {
                if let Some(z) = self.z_cache.get(ptr) {
                    *z
                } else {
                    let children_ptrs = self.expect_raw_ptrs::<8>(*idx);
                    let mut children_zs = [F::ZERO; 8];
                    for (idx, child_ptr) in children_ptrs.iter().enumerate() {
                        children_zs[idx] = self.hash_raw_ptr_unsafe(child_ptr).0;
                    }
                    let z = FWrap(self.poseidon_cache.hash8(&children_zs));
                    self.z_cache.insert(*ptr, Box::new(z));
                    self.inverse_z_cache.insert(z, Box::new(*ptr));
                    z
                }
            }
        }
    }

    /// Hashes pointers in parallel, consuming chunks of length 256, which is a
    /// reasonably safe limit. The danger of longer chunks is that the rightmost
    /// pointers are the ones which are more likely to reach the recursion depth
    /// limit in `hash_ptr_unsafe`. So we move in smaller chunks from left to
    /// right, populating the `z_cache`, which can rescue `hash_ptr_unsafe` from
    /// dangerously deep recursions
    fn hydrate_z_cache_with_ptrs(&self, ptrs: &[&RawPtr]) {
        ptrs.chunks(256).for_each(|chunk| {
            chunk.par_iter().for_each(|ptr| {
                self.hash_raw_ptr_unsafe(ptr);
            });
        });
    }

    /// Hashes enqueued `Ptr` trees from the bottom to the top, avoiding deep
    /// recursions in `hash_ptr`. Resets the `dehydrated` queue afterwards.
    pub fn hydrate_z_cache(&self) {
        self.hydrate_z_cache_with_ptrs(&self.dehydrated.load().iter().collect::<Vec<_>>());
        self.dehydrated.swap(Arc::new(FrozenVec::default()));
    }

    /// Whether the length of the dehydrated queue is within the safe limit.
    /// Note: these values are experimental and may be machine dependant.
    #[inline]
    fn is_below_safe_threshold(&self) -> bool {
        if cfg!(debug_assertions) {
            // not release mode
            self.dehydrated.load().len() < 443
        } else {
            // release mode
            self.dehydrated.load().len() < 2497
        }
    }

    /// Safe version of `hash_ptr_unsafe` that doesn't hit a stack overflow by
    /// precomputing the pointers that need to be hashed in order to hash the
    /// provided `ptr`
    pub fn hash_raw_ptr(&self, ptr: &RawPtr) -> FWrap<F> {
        if self.is_below_safe_threshold() {
            // just run `hash_ptr_unsafe` for extra speed when the dehydrated
            // queue is small enough
            return self.hash_raw_ptr_unsafe(ptr);
        }
        let mut ptrs: IndexSet<&RawPtr> = IndexSet::default();
        let mut stack = vec![ptr];
        macro_rules! feed_loop {
            ($x:expr) => {
                if $x.is_hash() {
                    if self.z_cache.get($x).is_none() {
                        if ptrs.insert($x) {
                            stack.push($x);
                        }
                    }
                }
            };
        }
        while let Some(ptr) = stack.pop() {
            match ptr {
                RawPtr::Atom(..) => (),
                RawPtr::Hash3(idx) => {
                    let ptrs = self.expect_raw_ptrs::<3>(*idx);
                    for ptr in ptrs {
                        feed_loop!(ptr)
                    }
                }
                RawPtr::Hash4(idx) => {
                    let ptrs = self.expect_raw_ptrs::<4>(*idx);
                    for ptr in ptrs {
                        feed_loop!(ptr)
                    }
                }
                RawPtr::Hash6(idx) => {
                    let ptrs = self.expect_raw_ptrs::<6>(*idx);
                    for ptr in ptrs {
                        feed_loop!(ptr)
                    }
                }
                RawPtr::Hash8(idx) => {
                    let ptrs = self.expect_raw_ptrs::<8>(*idx);
                    for ptr in ptrs {
                        feed_loop!(ptr)
                    }
                }
            }
        }
        ptrs.reverse();
        self.hydrate_z_cache_with_ptrs(&ptrs.into_iter().collect::<Vec<_>>());
        // Now it's okay to call `hash_ptr_unsafe`
        self.hash_raw_ptr_unsafe(ptr)
    }

    pub fn hash_ptr(&self, ptr: &Ptr) -> ZPtr<F> {
        ZPtr::from_parts(*ptr.tag(), self.hash_raw_ptr(ptr.pay()).0)
    }

    /// Constructs a vector of scalars that correspond to tags and hashes computed
    /// from a slice of `Ptr`s turned into `ZPtr`s
    pub fn to_scalar_vector(&self, ptrs: &[Ptr]) -> Vec<F> {
        ptrs.iter()
            .fold(Vec::with_capacity(2 * ptrs.len()), |mut acc, ptr| {
                let tag = ptr.tag().to_field();
                let pay = self.hash_raw_ptr(ptr.pay()).0;
                acc.push(tag);
                acc.push(pay);
                acc
            })
    }

    pub fn to_scalar_vector_raw(&self, ptrs: &[RawPtr]) -> Vec<F> {
        ptrs.iter().map(|ptr| self.hash_raw_ptr(ptr).0).collect()
    }

    /// Equality of the content-addressed versions of two pointers
    #[inline]
    pub fn raw_ptr_eq(&self, a: &RawPtr, b: &RawPtr) -> bool {
        self.hash_raw_ptr(a) == self.hash_raw_ptr(b)
    }

    #[inline]
    pub fn ptr_eq(&self, a: &Ptr, b: &Ptr) -> bool {
        self.hash_ptr(a) == self.hash_ptr(b)
    }

    /// Attempts to recover the `Ptr` that corresponds to `z_ptr` from
    /// `inverse_z_cache`. If the mapping is not there, returns an atom pointer
    /// with the same tag and value
    #[inline]
    pub fn to_raw_ptr(&self, z: &FWrap<F>) -> RawPtr {
        self.inverse_z_cache
            .get(z)
            .cloned()
            .unwrap_or_else(|| self.opaque(*z))
    }

    #[inline]
    pub fn to_ptr(&self, z_ptr: &ZPtr<F>) -> Ptr {
        Ptr::new(*z_ptr.tag(), self.to_raw_ptr(&FWrap(*z_ptr.value())))
    }
}

impl Ptr {
    pub fn fmt_to_string<F: LurkField>(&self, store: &Store<F>, state: &State) -> String {
        match self.tag() {
            Tag::Expr(t) => match t {
                Nil => {
                    if let Some(sym) = store.fetch_symbol(self) {
                        state.fmt_to_string(&sym.into())
                    } else {
                        "<Opaque Nil>".into()
                    }
                }
                Sym => {
                    if let Some(sym) = store.fetch_sym(self) {
                        state.fmt_to_string(&sym.into())
                    } else {
                        "<Opaque Sym>".into()
                    }
                }
                Key => {
                    if let Some(key) = store.fetch_key(self) {
                        state.fmt_to_string(&key.into())
                    } else {
                        "<Opaque Key>".into()
                    }
                }
                Str => {
                    if let Some(str) = store.fetch_string(self) {
                        format!("\"{str}\"")
                    } else {
                        "<Opaque Str>".into()
                    }
                }
                Char => {
                    if let Some(c) = self
                        .pay()
                        .get_atom()
                        .map(|idx| store.expect_f(idx))
                        .and_then(F::to_char)
                    {
                        format!("\'{c}\'")
                    } else {
                        "<Malformed Char>".into()
                    }
                }
                Cons => {
                    if let Some((list, non_nil)) = store.fetch_list(self) {
                        let list = list
                            .iter()
                            .map(|p| p.fmt_to_string(store, state))
                            .collect::<Vec<_>>();
                        if let Some(non_nil) = non_nil {
                            format!(
                                "({} . {})",
                                list.join(" "),
                                non_nil.fmt_to_string(store, state)
                            )
                        } else {
                            format!("({})", list.join(" "))
                        }
                    } else {
                        "<Opaque Cons>".into()
                    }
                }
                Num => {
                    if let Some(f) = self.pay().get_atom().map(|idx| store.expect_f(idx)) {
                        if let Some(u) = f.to_u64() {
                            u.to_string()
                        } else {
                            format!("0x{}", f.hex_digits())
                        }
                    } else {
                        "<Malformed Num>".into()
                    }
                }
                U64 => {
                    if let Some(u) = self
                        .pay()
                        .get_atom()
                        .map(|idx| store.expect_f(idx))
                        .and_then(F::to_u64)
                    {
                        format!("{u}u64")
                    } else {
                        "<Malformed U64>".into()
                    }
                }
                Fun => match self.pay().get_hash8() {
                    None => "<Malformed Fun>".into(),
                    Some(idx) => {
                        if let Some([vars, body, _, _]) = store.fetch_ptrs::<8, 4>(idx) {
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
                        } else {
                            "<Opaque Fun>".into()
                        }
                    }
                },
                Thunk => match self.pay().get_hash4() {
                    None => "<Malformed Thunk>".into(),
                    Some(idx) => {
                        if let Some([val, cont]) = store.fetch_ptrs::<4, 2>(idx) {
                            format!(
                                "Thunk{{ value: {} => cont: {} }}",
                                val.fmt_to_string(store, state),
                                cont.fmt_to_string(store, state)
                            )
                        } else {
                            "<Opaque Thunk>".into()
                        }
                    }
                },
                Comm => match self.pay().get_atom() {
                    Some(idx) => {
                        let f = store.expect_f(idx);
                        if store.inverse_z_cache.get(&FWrap(*f)).is_some() {
                            format!("(comm 0x{})", f.hex_digits())
                        } else {
                            format!("<Opaque Comm 0x{}>", f.hex_digits())
                        }
                    }
                    None => "<Malformed Comm>".into(),
                },
                Cproc => match self.pay().get_hash4() {
                    None => "<Malformed Cproc>".into(),
                    Some(idx) => {
                        if let Some([cproc_name, args]) = store.fetch_ptrs::<4, 2>(idx) {
                            format!(
                                "<COPROC {} {}>",
                                cproc_name.fmt_to_string(store, state),
                                args.fmt_to_string(store, state)
                            )
                        } else {
                            "<Opaque Cproc>".into()
                        }
                    }
                },
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
            },
            Tag::Op1(op) => op.to_string(),
            Tag::Op2(op) => op.to_string(),
        }
    }

    fn fmt_cont2_to_string<F: LurkField>(
        &self,
        name: &str,
        field: &str,
        store: &Store<F>,
        state: &State,
    ) -> String {
        match self.pay().get_hash8() {
            None => format!("<Malformed {name}>"),
            Some(idx) => {
                if let Some([a, cont, _, _]) = store.fetch_ptrs::<8, 4>(idx) {
                    format!(
                        "{name}{{ {field}: {}, continuation: {} }}",
                        a.fmt_to_string(store, state),
                        cont.fmt_to_string(store, state)
                    )
                } else {
                    format!("<Opaque {name}>")
                }
            }
        }
    }

    fn fmt_cont3_to_string<F: LurkField>(
        &self,
        name: &str,
        fields: (&str, &str),
        store: &Store<F>,
        state: &State,
    ) -> String {
        match self.pay().get_hash8() {
            None => format!("<Malformed {name}>"),
            Some(idx) => {
                if let Some([a, b, cont, _]) = store.fetch_ptrs::<8, 4>(idx) {
                    let (fa, fb) = fields;
                    format!(
                        "{name}{{ {fa}: {}, {fb}: {}, continuation: {} }}",
                        a.fmt_to_string(store, state),
                        b.fmt_to_string(store, state),
                        cont.fmt_to_string(store, state)
                    )
                } else {
                    format!("<Opaque {name}>")
                }
            }
        }
    }

    fn fmt_cont4_to_string<F: LurkField>(
        &self,
        name: &str,
        fields: (&str, &str, &str),
        store: &Store<F>,
        state: &State,
    ) -> String {
        match self.pay().get_hash8() {
            None => format!("<Malformed {name}>"),
            Some(idx) => {
                if let Some([a, b, c, cont]) = store.fetch_ptrs::<8, 4>(idx) {
                    let (fa, fb, fc) = fields;
                    format!(
                        "{name}{{ {fa}: {}, {fb}: {}, {fc}: {}, continuation: {} }}",
                        a.fmt_to_string(store, state),
                        b.fmt_to_string(store, state),
                        c.fmt_to_string(store, state),
                        cont.fmt_to_string(store, state)
                    )
                } else {
                    format!("<Opaque {name}>")
                }
            }
        }
    }
}
