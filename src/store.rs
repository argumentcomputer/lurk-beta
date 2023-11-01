use arc_swap::ArcSwap;
use elsa::sync::{FrozenMap, FrozenVec};
use elsa::sync_index_set::FrozenIndexSet;
use once_cell::sync::OnceCell;
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use std::fmt;
use std::sync::Arc;
use std::usize;
use thiserror;

use crate::cont::Continuation;
use crate::expr;
use crate::expr::{Expression, Thunk};
use crate::field::{FWrap, LurkField};
use crate::ptr::{ContPtr, Ptr, RawPtr};
use crate::state::{lurk_sym, user_sym};
use crate::symbol::Symbol;
use crate::tag::{ContTag, ExprTag, Op1, Op2, Tag};
use crate::z_cont::ZCont;
use crate::z_expr::ZExpr;
use crate::z_ptr::{ZContPtr, ZExprPtr, ZPtr};
use crate::z_store::ZStore;
use crate::{Num, UInt};

use crate::hash::{HashConstants, InversePoseidonCache, PoseidonCache};

type IndexSet<K> = FrozenIndexSet<K, ahash::RandomState>;

#[derive(Debug)]
pub struct Store<F: LurkField> {
    pub cons_store: IndexSet<Box<(Ptr<F>, Ptr<F>)>>,
    pub comm_store: IndexSet<Box<(FWrap<F>, Ptr<F>)>>,

    pub fun_store: IndexSet<Box<(Ptr<F>, Ptr<F>, Ptr<F>)>>,

    /// Holds a Sym or Key which is a string head and a symbol tail
    pub sym_store: IndexSet<Box<(Ptr<F>, Ptr<F>)>>,

    // Other sparse storage format without hashing is likely more efficient
    pub num_store: IndexSet<Box<Num<F>>>,

    /// Holds a Str, which is a char head and a string tail
    pub str_store: IndexSet<Box<(Ptr<F>, Ptr<F>)>>,
    pub thunk_store: IndexSet<Box<Thunk<F>>>,
    pub call0_store: IndexSet<Box<(Ptr<F>, ContPtr<F>)>>,
    pub call_store: IndexSet<Box<(Ptr<F>, Ptr<F>, ContPtr<F>)>>,
    pub call2_store: IndexSet<Box<(Ptr<F>, Ptr<F>, ContPtr<F>)>>,
    pub tail_store: IndexSet<Box<(Ptr<F>, ContPtr<F>)>>,
    pub lookup_store: IndexSet<Box<(Ptr<F>, ContPtr<F>)>>,
    pub unop_store: IndexSet<Box<(Op1, ContPtr<F>)>>,
    pub binop_store: IndexSet<Box<(Op2, Ptr<F>, Ptr<F>, ContPtr<F>)>>,
    pub binop2_store: IndexSet<Box<(Op2, Ptr<F>, ContPtr<F>)>>,
    pub if_store: IndexSet<Box<(Ptr<F>, ContPtr<F>)>>,
    pub let_store: IndexSet<Box<(Ptr<F>, Ptr<F>, Ptr<F>, ContPtr<F>)>>,
    pub letrec_store: IndexSet<Box<(Ptr<F>, Ptr<F>, Ptr<F>, ContPtr<F>)>>,
    pub emit_store: IndexSet<Box<ContPtr<F>>>,

    /// Holds opaque pointers
    pub opaque_ptrs: IndexSet<Box<ZExprPtr<F>>>,
    /// Holds opaque continuation pointers
    pub opaque_cont_ptrs: IndexSet<Box<ZContPtr<F>>>,

    /// Holds a mapping of `ZExprPtr` -> `Ptr` for reverse lookups
    pub z_expr_ptr_map: FrozenMap<ZExprPtr<F>, Box<Ptr<F>>>,
    /// Holds a mapping of `ZExprPtr` -> `ContPtr<F>` for reverse lookups
    pub z_cont_ptr_map: FrozenMap<ZContPtr<F>, Box<ContPtr<F>>>,

    z_expr_ptr_cache: FrozenMap<Ptr<F>, Box<(ZExprPtr<F>, Option<ZExpr<F>>)>>,
    z_cont_ptr_cache: FrozenMap<ContPtr<F>, Box<(ZContPtr<F>, Option<ZCont<F>>)>>,

    /// Caches poseidon hashes
    pub poseidon_cache: PoseidonCache<F>,
    /// Caches poseidon preimages
    pub inverse_poseidon_cache: InversePoseidonCache<F>,

    /// Contains Ptrs which have not yet been hydrated.
    pub dehydrated: ArcSwap<FrozenVec<Box<Ptr<F>>>>,
    pub dehydrated_cont: ArcSwap<FrozenVec<Box<ContPtr<F>>>>,

    str_cache: FrozenMap<String, Box<Ptr<F>>>,
    symbol_cache: FrozenMap<Symbol, Box<Ptr<F>>>,

    pub constants: OnceCell<NamedConstants<F>>,
}

impl<F: LurkField> Default for Store<F> {
    fn default() -> Self {
        let store = Self {
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
            opaque_ptrs: Default::default(),
            opaque_cont_ptrs: Default::default(),
            z_expr_ptr_map: Default::default(),
            z_cont_ptr_map: Default::default(),
            z_expr_ptr_cache: Default::default(),
            z_cont_ptr_cache: Default::default(),
            poseidon_cache: Default::default(),
            inverse_poseidon_cache: Default::default(),
            dehydrated: Default::default(),
            dehydrated_cont: Default::default(),
            str_cache: Default::default(),
            symbol_cache: Default::default(),
            constants: Default::default(),
        };
        store.ensure_constants();
        store
    }
}

#[derive(thiserror::Error, Debug, Clone)]
pub struct Error(pub String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StoreError: {}", self.0)
    }
}

#[macro_export]
macro_rules! lurk_sym_ptr {
    ( $store:expr, $sym:ident ) => {{
        $store.expect_constants().$sym.ptr()
    }};
}

/// These methods provide a more ergonomic means of constructing and manipulating Lurk data.
/// They can be thought of as a minimal DSL for working with Lurk data in Rust code.
/// Prefer these methods when constructing literal data or assembling program fragments in
/// tests or during evaluation, etc.
impl<F: LurkField> Store<F> {
    pub fn expect_constants(&self) -> &NamedConstants<F> {
        self.constants
            .get()
            .expect("Constants must have been set during instantiation")
    }

    #[inline]
    pub fn cons(&self, car: Ptr<F>, cdr: Ptr<F>) -> Ptr<F> {
        self.intern_cons(car, cdr)
    }

    #[inline]
    pub fn strcons(&self, car: Ptr<F>, cdr: Ptr<F>) -> Ptr<F> {
        self.intern_strcons(car, cdr)
    }

    #[inline]
    pub fn strnil(&self) -> Ptr<F> {
        Ptr::null(ExprTag::Str)
    }

    #[inline]
    pub fn symnil(&self) -> Ptr<F> {
        Ptr::null(ExprTag::Sym)
    }

    pub fn hidden(&self, secret: F, payload: Ptr<F>) -> Option<Ptr<F>> {
        self.comm_store
            .get_full(&Box::new((FWrap(secret), payload)))
            .map(|(c, _ref)| Ptr::index(ExprTag::Comm, c))
    }

    pub fn hide(&self, secret: F, payload: Ptr<F>) -> Ptr<F> {
        self.intern_comm(secret, payload)
    }

    pub fn commit(&self, payload: Ptr<F>) -> Ptr<F> {
        self.hide(F::NON_HIDING_COMMITMENT_SECRET, payload)
    }

    pub fn open(&self, ptr: Ptr<F>) -> Option<(F, Ptr<F>)> {
        let p = match ptr.tag {
            ExprTag::Comm => ptr,
            ExprTag::Num => {
                let scalar = self.fetch_num(&ptr).map(|x| x.into_scalar())?;
                match self.get_maybe_opaque(ExprTag::Comm, scalar) {
                    Some(c) => c,
                    None => {
                        panic!("Can't find commitment in the store.")
                    }
                }
            }
            _ => return None,
        };

        self.fetch_comm(&p)
            .map(|(secret, payload)| (secret.0, *payload))
    }

    pub fn open_mut(&self, ptr: Ptr<F>) -> Result<(F, Ptr<F>), Error> {
        let p = match ptr.tag {
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
        let p = match ptr.tag {
            ExprTag::Comm => ptr,
            _ => return None,
        };

        self.fetch_comm(&p)
            .and_then(|(secret, _payload)| self.get_num(Num::Scalar(secret.0)))
    }

    pub fn secret_mut(&self, ptr: Ptr<F>) -> Result<Ptr<F>, Error> {
        let p = match ptr.tag {
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

    pub fn list(&self, elts: &[Ptr<F>]) -> Ptr<F> {
        self.intern_list(elts)
    }

    pub fn num<T: Into<Num<F>>>(&self, num: T) -> Ptr<F> {
        self.intern_num(num)
    }

    pub fn uint64(&self, n: u64) -> Ptr<F> {
        self.intern_u64(n)
    }

    pub fn str(&self, s: &str) -> Ptr<F> {
        self.intern_string(s)
    }

    pub fn sym<T: AsRef<str>>(&self, name: T) -> Ptr<F> {
        self.intern_symbol(&Symbol::sym(&[name.as_ref()]))
    }

    pub fn key<T: AsRef<str>>(&self, name: T) -> Ptr<F> {
        self.intern_symbol(&Symbol::key(&[name.as_ref()]))
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

    pub fn intern_symnil(&self, key: bool) -> Ptr<F> {
        if key {
            Ptr::null(ExprTag::Key)
        } else {
            Ptr::null(ExprTag::Sym)
        }
    }

    pub fn intern_cons(&self, car: Ptr<F>, cdr: Ptr<F>) -> Ptr<F> {
        if car.is_opaque() || cdr.is_opaque() {
            self.hash_expr(&car);
            self.hash_expr(&cdr);
        }

        let (p, inserted) = self.cons_store.insert_probe(Box::new((car, cdr)));
        let ptr = Ptr::index(ExprTag::Cons, p);
        if inserted {
            self.dehydrated.load().push(Box::new(ptr));
        }
        ptr
    }

    pub fn intern_strcons(&self, car: Ptr<F>, cdr: Ptr<F>) -> Ptr<F> {
        if car.is_opaque() || cdr.is_opaque() {
            self.hash_expr(&car);
            self.hash_expr(&cdr);
        }
        assert_eq!((car.tag, cdr.tag), (ExprTag::Char, ExprTag::Str));
        let (i, _) = self.str_store.insert_probe(Box::new((car, cdr)));
        Ptr::index(ExprTag::Str, i)
    }

    pub fn intern_symcons(&self, car: Ptr<F>, cdr: Ptr<F>) -> Ptr<F> {
        if car.is_opaque() || cdr.is_opaque() {
            self.hash_expr(&car);
            self.hash_expr(&cdr);
        }
        assert_eq!((car.tag, cdr.tag), (ExprTag::Str, ExprTag::Sym));
        let (i, _) = self.sym_store.insert_probe(Box::new((car, cdr)));
        Ptr::index(ExprTag::Sym, i)
    }

    pub fn intern_keycons(&self, car: Ptr<F>, cdr: Ptr<F>) -> Ptr<F> {
        if car.is_opaque() || cdr.is_opaque() {
            self.hash_expr(&car);
            self.hash_expr(&cdr);
        }
        assert_eq!((car.tag, cdr.tag), (ExprTag::Str, ExprTag::Sym));
        let (i, _) = self.sym_store.insert_probe(Box::new((car, cdr)));
        Ptr::index(ExprTag::Key, i)
    }

    pub fn intern_comm(&self, secret: F, payload: Ptr<F>) -> Ptr<F> {
        if payload.is_opaque() {
            self.hash_expr(&payload);
        }
        let (p, inserted) = self
            .comm_store
            .insert_probe(Box::new((FWrap(secret), payload)));

        let ptr = Ptr::index(ExprTag::Comm, p);

        if inserted {
            self.dehydrated.load().push(Box::new(ptr));
        }
        ptr
    }

    // Intern a potentially-opaque value. If the corresponding value is already known to the store,
    // return the known value.
    pub fn intern_maybe_opaque(&self, tag: ExprTag, hash: F) -> Ptr<F> {
        self.intern_opaque_aux(tag, hash, true)
    }

    // Intern an opaque value. If the corresponding non-opaque value is already known to the store,
    // return an opaque one anyway.
    fn intern_opaque(&self, tag: ExprTag, hash: F) -> Ptr<F> {
        self.intern_opaque_aux(tag, hash, false)
    }

    pub fn get_maybe_opaque(&self, tag: ExprTag, hash: F) -> Option<Ptr<F>> {
        let z_ptr = ZExprPtr::from_parts(tag, hash);

        let ptr = self.z_expr_ptr_map.get(&z_ptr);
        if let Some(p) = ptr {
            return Some(*p);
        }
        None
    }

    // Intern a potentially-opaque value. If the corresponding non-opaque value is already known to the store, and
    // `return_non_opaque_if_existing` is true, return the known value.
    fn intern_opaque_aux(
        &self,
        tag: ExprTag,
        hash: F,
        return_non_opaque_if_existing: bool,
    ) -> Ptr<F> {
        self.hydrate_scalar_cache();
        let z_ptr = ZExprPtr::from_parts(tag, hash);

        // Scope the first immutable borrow.
        {
            let ptr = self.z_expr_ptr_map.get(&z_ptr);
            if let Some(p) = ptr {
                if return_non_opaque_if_existing || p.is_opaque() {
                    return *p;
                }
            }
        }

        let (i, _) = self.opaque_ptrs.insert_probe(Box::new(z_ptr));
        Ptr::opaque(tag, i)
    }

    pub fn intern_maybe_opaque_fun(&self, hash: F) -> Ptr<F> {
        self.intern_maybe_opaque(ExprTag::Fun, hash)
    }

    pub fn intern_maybe_opaque_sym(&self, hash: F) -> Ptr<F> {
        self.intern_maybe_opaque(ExprTag::Sym, hash)
    }

    pub fn intern_maybe_opaque_cons(&self, hash: F) -> Ptr<F> {
        self.intern_maybe_opaque(ExprTag::Cons, hash)
    }

    pub fn intern_maybe_opaque_comm(&self, hash: F) -> Ptr<F> {
        self.intern_maybe_opaque(ExprTag::Comm, hash)
    }

    pub fn intern_opaque_fun(&self, hash: F) -> Ptr<F> {
        self.intern_opaque(ExprTag::Fun, hash)
    }

    pub fn intern_opaque_sym(&self, hash: F) -> Ptr<F> {
        self.intern_opaque(ExprTag::Sym, hash)
    }

    pub fn intern_opaque_cons(&self, hash: F) -> Ptr<F> {
        self.intern_opaque(ExprTag::Cons, hash)
    }

    pub fn intern_opaque_comm(&self, hash: F) -> Ptr<F> {
        self.intern_opaque(ExprTag::Comm, hash)
    }

    /// Helper to allocate a list, instead of manually using `cons`.
    pub fn intern_list(&self, elts: &[Ptr<F>]) -> Ptr<F> {
        elts.iter()
            .rev()
            .fold(lurk_sym_ptr!(self, nil), |acc, elt| {
                self.intern_cons(*elt, acc)
            })
    }

    pub fn intern_symbol_path(&self, path: &[String]) -> Ptr<F> {
        path.iter().fold(self.symnil(), |acc, s| {
            let s_ptr = self.intern_string(s);
            self.intern_symcons(s_ptr, acc)
        })
    }

    pub fn intern_symbol(&self, sym: &Symbol) -> Ptr<F> {
        match self.symbol_cache.get(sym) {
            Some(ptr) => *ptr,
            None => {
                use crate::tag::ExprTag::{Key, Nil};
                let path_ptr = self.intern_symbol_path(sym.path());
                let sym_ptr = if sym == &lurk_sym("nil") {
                    path_ptr.cast(Nil)
                } else if sym.is_keyword() {
                    path_ptr.cast(Key)
                } else {
                    path_ptr
                };
                self.symbol_cache.insert(sym.clone(), Box::new(sym_ptr));
                sym_ptr
            }
        }
    }

    pub fn user_sym(&self, name: &str) -> Ptr<F> {
        self.intern_symbol(&user_sym(name))
    }

    pub fn intern_num<T: Into<Num<F>>>(&self, num: T) -> Ptr<F> {
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
        let (ptr, _) = self.num_store.insert_probe(Box::new(num));

        Ptr::index(ExprTag::Num, ptr)
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
            .get_full(&num)
            .map(|(x, _)| Ptr::index(ExprTag::Num, x))
    }

    #[inline]
    pub fn intern_char(&self, c: char) -> Ptr<F> {
        Ptr::index(ExprTag::Char, u32::from(c) as usize)
    }

    pub fn intern_uint(&self, n: UInt) -> Ptr<F> {
        match n {
            UInt::U64(x) => self.intern_u64(x),
        }
    }

    pub fn intern_u64(&self, n: u64) -> Ptr<F> {
        Ptr::index(ExprTag::U64, n as usize)
    }

    pub fn intern_string(&self, s: &str) -> Ptr<F> {
        match self.str_cache.get(s) {
            Some(ptr) => *ptr,
            None => {
                let ptr = s.chars().rev().fold(self.strnil(), |acc, c| {
                    self.intern_strcons(self.intern_char(c), acc)
                });
                self.str_cache.insert(s.to_string(), Box::new(ptr));
                ptr
            }
        }
    }

    pub fn intern_fun(&self, arg: Ptr<F>, body: Ptr<F>, closed_env: Ptr<F>) -> Ptr<F> {
        // TODO: closed_env must be an env
        assert!(matches!(arg.tag, ExprTag::Sym), "ARG must be a symbol");
        let (p, inserted) = self
            .fun_store
            .insert_probe(Box::new((arg, body, closed_env)));
        let ptr = Ptr::index(ExprTag::Fun, p);
        if inserted {
            self.dehydrated.load().push(Box::new(ptr));
        }
        ptr
    }

    pub fn intern_thunk(&self, thunk: Thunk<F>) -> Ptr<F> {
        let (p, inserted) = self.thunk_store.insert_probe(Box::new(thunk));
        let ptr = Ptr::index(ExprTag::Thunk, p);
        if inserted {
            self.dehydrated.load().push(Box::new(ptr));
        }
        ptr
    }

    pub fn mark_dehydrated_cont(&self, p: ContPtr<F>) -> ContPtr<F> {
        self.dehydrated_cont.load().push(Box::new(p));
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

    pub fn get_hash_components_cont(&self, ptr: &ContPtr<F>) -> Option<[F; 8]> {
        Some(self.to_z_cont(ptr)?.hash_components())
    }

    pub fn get_hash_components_thunk(&self, thunk: &Thunk<F>) -> Option<[F; 4]> {
        let value_hash = self.hash_expr(&thunk.value)?;
        let continuation_hash = self.hash_cont(&thunk.continuation)?;

        Some([
            value_hash.0.to_field(),
            value_hash.1,
            continuation_hash.0.to_field(),
            continuation_hash.1,
        ])
    }

    pub fn intern_cont_error(&self) -> ContPtr<F> {
        self.mark_dehydrated_cont(self.get_cont_error())
    }

    pub fn intern_cont_outermost(&self) -> ContPtr<F> {
        self.mark_dehydrated_cont(self.get_cont_outermost())
    }

    pub fn intern_cont_terminal(&self) -> ContPtr<F> {
        self.mark_dehydrated_cont(self.get_cont_terminal())
    }

    pub fn intern_cont_dummy(&self) -> ContPtr<F> {
        self.mark_dehydrated_cont(self.get_cont_dummy())
    }

    pub fn fetch_z_expr_ptr(&self, z_ptr: &ZExprPtr<F>) -> Option<Ptr<F>> {
        self.z_expr_ptr_map.get(z_ptr).copied()
    }

    pub fn fetch_z_cont_ptr(&self, z_ptr: &ZContPtr<F>) -> Option<ContPtr<F>> {
        self.z_cont_ptr_map.get(z_ptr).copied()
    }

    pub fn fetch_maybe_sym(&self, ptr: &Ptr<F>) -> Option<Symbol> {
        if matches!(ptr.tag, ExprTag::Sym) {
            self.fetch_sym(ptr)
        } else {
            None
        }
    }

    // fetch a symbol cons or keyword cons
    pub fn fetch_symcons(&self, ptr: &Ptr<F>) -> Option<(Ptr<F>, Ptr<F>)> {
        match (ptr.tag, ptr.raw) {
            (ExprTag::Sym | ExprTag::Key, RawPtr::Index(x)) => {
                let (car, cdr) = self.sym_store.get_index(x)?;
                Some((*car, *cdr))
            }
            _ => None,
        }
    }

    pub fn fetch_sym(&self, ptr: &Ptr<F>) -> Option<Symbol> {
        if ptr.tag == ExprTag::Sym {
            self.fetch_symbol(ptr)
        } else {
            None
        }
    }

    pub fn fetch_key(&self, ptr: &Ptr<F>) -> Option<Symbol> {
        if ptr.tag == ExprTag::Key {
            self.fetch_symbol(ptr)
        } else {
            None
        }
    }

    pub fn fetch_symbol(&self, ptr: &Ptr<F>) -> Option<Symbol> {
        match ptr.tag {
            ExprTag::Nil => Some(lurk_sym("nil")),
            ExprTag::Sym | ExprTag::Key => {
                let is_key = ptr.tag == ExprTag::Key;
                let mut ptr = *ptr;
                let mut path = Vec::new();
                while let Some((car, cdr)) = self.fetch_symcons(&ptr) {
                    let string = self.fetch_string(&car)?;
                    path.push(string);
                    ptr = cdr
                }
                path.reverse();
                Some(Symbol::new_from_vec(path, is_key))
            }
            _ => None,
        }
    }

    pub fn fetch_strcons(&self, ptr: &Ptr<F>) -> Option<(Ptr<F>, Ptr<F>)> {
        match (ptr.tag, ptr.raw) {
            (ExprTag::Str, RawPtr::Index(x)) => {
                let (car, cdr) = self.str_store.get_index(x)?;
                Some((*car, *cdr))
            }
            _ => None,
        }
    }

    pub fn fetch_string(&self, ptr: &Ptr<F>) -> Option<String> {
        let mut string = String::new();
        let mut ptr = ptr;
        loop {
            match (ptr.tag, ptr.raw) {
                (ExprTag::Str, RawPtr::Null) => return Some(string),
                (ExprTag::Str, RawPtr::Index(x)) => {
                    let (car, cdr) = self.str_store.get_index(x)?;
                    let chr = self.fetch_char(car)?;
                    string.push(chr);
                    ptr = cdr
                }
                _ => return None,
            }
        }
    }

    pub fn fetch_char(&self, ptr: &Ptr<F>) -> Option<char> {
        debug_assert!(matches!(ptr.tag, ExprTag::Char));
        char::from_u32(ptr.raw.idx()? as u32)
    }

    pub fn fetch_fun(&self, ptr: &Ptr<F>) -> Option<&(Ptr<F>, Ptr<F>, Ptr<F>)> {
        debug_assert!(matches!(ptr.tag, ExprTag::Fun));
        if ptr.raw.is_opaque() {
            None
        } else {
            self.fun_store.get_index(ptr.raw.idx()?)
        }
    }

    pub fn fetch_cons(&self, ptr: &Ptr<F>) -> Option<&(Ptr<F>, Ptr<F>)> {
        debug_assert!(matches!(ptr.tag, ExprTag::Cons));
        if ptr.raw.is_opaque() {
            None
        } else {
            self.cons_store.get_index(ptr.raw.idx()?)
        }
    }

    pub fn fetch_comm(&self, ptr: &Ptr<F>) -> Option<&(FWrap<F>, Ptr<F>)> {
        debug_assert!(matches!(ptr.tag, ExprTag::Comm));
        if ptr.raw.is_opaque() {
            None
        } else {
            self.comm_store.get_index(ptr.raw.idx()?)
        }
    }

    pub fn fetch_num(&self, ptr: &Ptr<F>) -> Option<&Num<F>> {
        debug_assert!(matches!(ptr.tag, ExprTag::Num));
        self.num_store.get_index(ptr.raw.idx()?)
    }

    pub fn fetch_thunk(&self, ptr: &Ptr<F>) -> Option<&Thunk<F>> {
        debug_assert!(matches!(ptr.tag, ExprTag::Thunk));
        self.thunk_store.get_index(ptr.raw.idx()?)
    }

    pub fn fetch_uint(&self, ptr: &Ptr<F>) -> Option<UInt> {
        // If more UInt variants are added, the following assertion should be relaxed to check for any of them.
        debug_assert!(matches!(ptr.tag, ExprTag::U64));
        match ptr.tag {
            ExprTag::U64 => Some(UInt::U64(ptr.raw.idx()? as u64)),
            _ => unreachable!(),
        }
    }

    pub fn fetch(&self, ptr: &Ptr<F>) -> Option<Expression<F>> {
        if ptr.is_opaque() {
            return None;
        }
        match ptr.tag {
            ExprTag::Nil => Some(Expression::Nil),
            ExprTag::Cons => self.fetch_cons(ptr).map(|(a, b)| Expression::Cons(*a, *b)),
            ExprTag::Comm => self.fetch_comm(ptr).map(|(a, b)| Expression::Comm(a.0, *b)),
            ExprTag::Sym if ptr.raw.is_null() => Some(Expression::RootSym),
            ExprTag::Sym => self
                .fetch_symcons(ptr)
                .map(|(car, cdr)| Expression::Sym(car, cdr)),
            ExprTag::Key if ptr.raw.is_null() => Some(Expression::RootKey),
            ExprTag::Key => self
                .fetch_symcons(ptr)
                .map(|(car, cdr)| Expression::Key(car, cdr)),
            ExprTag::Num => self.fetch_num(ptr).map(|num| Expression::Num(*num)),
            ExprTag::Fun => self
                .fetch_fun(ptr)
                .map(|(a, b, c)| Expression::Fun(*a, *b, *c)),
            ExprTag::Thunk => self.fetch_thunk(ptr).map(|thunk| Expression::Thunk(*thunk)),
            ExprTag::Str if ptr.raw.is_null() => Some(Expression::EmptyStr),
            ExprTag::Str => self
                .fetch_strcons(ptr)
                .map(|(car, cdr)| Expression::Str(car, cdr)),
            ExprTag::Char => self.fetch_char(ptr).map(Expression::Char),
            ExprTag::U64 => self.fetch_uint(ptr).map(Expression::UInt),
            ExprTag::Cproc => unreachable!("Lurk Alpha doesn't produce such expressions"),
        }
    }

    /// Returns a `Vec` of `Ptr`s representing the elements of a proper list, `ptr`.
    /// This is intended to be the inverse of `Store::list()`.
    /// IF `ptr` isn't a proper list, return None.
    pub fn fetch_list(&self, ptr: &Ptr<F>) -> Option<Vec<Ptr<F>>> {
        let mut list = Vec::new();
        let mut p = *ptr;

        loop {
            match self.fetch(&p) {
                Some(Expression::Cons(car, cdr)) => {
                    list.push(car);
                    p = cdr;
                }
                Some(Expression::Nil) => break,
                _ => return None,
            }
        }

        Some(list)
    }

    pub fn fetch_cont(&self, ptr: &ContPtr<F>) -> Option<Continuation<F>> {
        use ContTag::{
            Binop, Binop2, Call, Call0, Call2, Cproc, Dummy, Emit, Error, If, Let, LetRec, Lookup,
            Outermost, Tail, Terminal, Unop,
        };
        match ptr.tag {
            Outermost => Some(Continuation::Outermost),
            Call0 => self
                .call0_store
                .get_index(ptr.raw.idx()?)
                .map(|(saved_env, continuation)| Continuation::Call0 {
                    saved_env: *saved_env,
                    continuation: *continuation,
                }),
            Call => self
                .call_store
                .get_index(ptr.raw.idx()?)
                .map(|(a, b, c)| Continuation::Call {
                    unevaled_arg: *a,
                    saved_env: *b,
                    continuation: *c,
                }),
            Call2 => {
                self.call2_store
                    .get_index(ptr.raw.idx()?)
                    .map(|(a, b, c)| Continuation::Call2 {
                        function: *a,
                        saved_env: *b,
                        continuation: *c,
                    })
            }
            Tail => self
                .tail_store
                .get_index(ptr.raw.idx()?)
                .map(|(a, b)| Continuation::Tail {
                    saved_env: *a,
                    continuation: *b,
                }),
            Error => Some(Continuation::Error),
            Lookup => {
                self.lookup_store
                    .get_index(ptr.raw.idx()?)
                    .map(|(a, b)| Continuation::Lookup {
                        saved_env: *a,
                        continuation: *b,
                    })
            }
            Unop => self
                .unop_store
                .get_index(ptr.raw.idx()?)
                .map(|(a, b)| Continuation::Unop {
                    operator: *a,
                    continuation: *b,
                }),
            Binop => self
                .binop_store
                .get_index(ptr.raw.idx()?)
                .map(|(a, b, c, d)| Continuation::Binop {
                    operator: *a,
                    saved_env: *b,
                    unevaled_args: *c,
                    continuation: *d,
                }),
            Binop2 => self
                .binop2_store
                .get_index(ptr.raw.idx()?)
                .map(|(a, b, c)| Continuation::Binop2 {
                    operator: *a,
                    evaled_arg: *b,
                    continuation: *c,
                }),
            If => self
                .if_store
                .get_index(ptr.raw.idx()?)
                .map(|(a, b)| Continuation::If {
                    unevaled_args: *a,
                    continuation: *b,
                }),
            Let => self
                .let_store
                .get_index(ptr.raw.idx()?)
                .map(|(a, b, c, d)| Continuation::Let {
                    var: *a,
                    body: *b,
                    saved_env: *c,
                    continuation: *d,
                }),
            LetRec => self
                .letrec_store
                .get_index(ptr.raw.idx()?)
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
                .get_index(ptr.raw.idx()?)
                .map(|continuation| Continuation::Emit {
                    continuation: *continuation,
                }),
            Cproc => unreachable!("Lurk Alpha doesn't produce such continuations"),
        }
    }

    // TODO: add cycle detection to avoid infinite recursion
    pub fn get_z_expr(
        &self,
        ptr: &Ptr<F>,
        z_store: &mut Option<ZStore<F>>,
    ) -> Result<(ZExprPtr<F>, Option<ZExpr<F>>), Error> {
        let get_z_expr_aux = |z_store: &mut Option<ZStore<F>>| {
            let (z_ptr, z_expr) = match self.fetch(ptr) {
                Some(Expression::Nil) => (ZExpr::Nil.z_ptr(&self.poseidon_cache), Some(ZExpr::Nil)),
                Some(Expression::Cons(car, cdr)) => {
                    let (z_car, _) = self.get_z_expr(&car, z_store)?;
                    let (z_cdr, _) = self.get_z_expr(&cdr, z_store)?;
                    let z_expr = ZExpr::Cons(z_car, z_cdr);
                    (z_expr.z_ptr(&self.poseidon_cache), Some(z_expr))
                }
                Some(Expression::Comm(secret, payload)) => {
                    let (z_payload, _) = self.get_z_expr(&payload, z_store)?;
                    let z_expr = ZExpr::Comm(secret, z_payload);
                    (z_expr.z_ptr(&self.poseidon_cache), Some(z_expr))
                }
                Some(Expression::Fun(args, body, env)) => {
                    let (z_args, _) = self.get_z_expr(&args, z_store)?;
                    let (z_env, _) = self.get_z_expr(&env, z_store)?;
                    let (z_body, _) = self.get_z_expr(&body, z_store)?;
                    let z_expr = ZExpr::Fun {
                        arg: z_args,
                        body: z_body,
                        closed_env: z_env,
                    };
                    (z_expr.z_ptr(&self.poseidon_cache), Some(z_expr))
                }
                Some(Expression::Num(n)) => {
                    let f = match n {
                        Num::Scalar(f) => f,
                        Num::U64(u) => F::from_u64(u),
                    };
                    let z_expr = ZExpr::Num(f);
                    (z_expr.z_ptr(&self.poseidon_cache), Some(z_expr))
                }
                Some(Expression::Thunk(Thunk {
                    value,
                    continuation,
                })) => {
                    let (z_value, _) = self.get_z_expr(&value, z_store)?;
                    let (z_cont, _) = self.get_z_cont(&continuation, z_store)?;
                    let z_expr = ZExpr::Thunk(z_value, z_cont);
                    (z_expr.z_ptr(&self.poseidon_cache), Some(z_expr))
                }
                Some(Expression::Char(c)) => {
                    let z_expr = ZExpr::Char(c);
                    (z_expr.z_ptr(&self.poseidon_cache), Some(z_expr))
                }
                Some(Expression::UInt(u)) => {
                    let z_expr = ZExpr::UInt(u);
                    (z_expr.z_ptr(&self.poseidon_cache), Some(z_expr))
                }
                Some(Expression::EmptyStr) => (
                    ZExpr::EmptyStr.z_ptr(&self.poseidon_cache),
                    Some(ZExpr::EmptyStr),
                ),
                Some(Expression::Str(car, cdr)) => {
                    let (z_car, _) = self.get_z_expr(&car, z_store)?;
                    let (z_cdr, _) = self.get_z_expr(&cdr, z_store)?;
                    let z_expr = ZExpr::Str(z_car, z_cdr);
                    (z_expr.z_ptr(&self.poseidon_cache), Some(z_expr))
                }
                Some(Expression::RootSym) => (
                    ZExpr::RootSym.z_ptr(&self.poseidon_cache),
                    Some(ZExpr::RootSym),
                ),
                Some(Expression::RootKey) => (
                    ZExpr::RootKey.z_ptr(&self.poseidon_cache),
                    Some(ZExpr::RootKey),
                ),
                Some(Expression::Sym(car, cdr)) => {
                    let (z_car, _) = self.get_z_expr(&car, z_store)?;
                    let (z_cdr, _) = self.get_z_expr(&cdr, z_store)?;
                    let z_expr = ZExpr::Sym(z_car, z_cdr);
                    (z_expr.z_ptr(&self.poseidon_cache), Some(z_expr))
                }
                Some(Expression::Key(car, cdr)) => {
                    let (z_car, _) = self.get_z_expr(&car, z_store)?;
                    let (z_cdr, _) = self.get_z_expr(&cdr, z_store)?;
                    let z_expr = ZExpr::Key(z_car, z_cdr);
                    (z_expr.z_ptr(&self.poseidon_cache), Some(z_expr))
                }
                None => return Err(Error("get_z_expr unknown opaque".into())),
            };
            self.z_expr_ptr_map.insert(z_ptr, Box::new(*ptr));
            self.z_expr_ptr_cache
                .insert(*ptr, Box::new((z_ptr, z_expr.clone())));
            Ok((z_ptr, z_expr))
        };
        if let Some(idx) = ptr.raw.opaque_idx() {
            let z_ptr = self
                .opaque_ptrs
                .get_index(idx)
                .ok_or(Error("get_z_expr unknown opaque".into()))?;
            // TODO: should we try to dereference the opaque pointer?
            Ok((*z_ptr, None))
        } else {
            // Store all children reachable from Ptr in ZStore
            if z_store.is_some() {
                let (z_ptr, z_expr) = get_z_expr_aux(z_store)?;
                z_store
                    .as_mut()
                    .unwrap()
                    .insert_z_expr(&z_ptr, z_expr.clone());
                Ok((z_ptr, z_expr))
            // Check the Ptr cache, used extensively in hydration
            } else if let Some((z_ptr, z_expr)) = self.z_expr_ptr_cache.get(ptr) {
                Ok((*z_ptr, z_expr.clone()))
            } else {
                get_z_expr_aux(z_store)
            }
        }
    }

    // TODO: add cycle detection to avoid infinite recursions
    pub fn get_z_cont(
        &self,
        ptr: &ContPtr<F>,
        z_store: &mut Option<ZStore<F>>,
    ) -> Result<(ZContPtr<F>, Option<ZCont<F>>), Error> {
        if let Some(idx) = ptr.raw.opaque_idx() {
            let z_ptr = self
                .opaque_cont_ptrs
                .get_index(idx)
                .ok_or(Error("get_z_cont unknown opaque ".into()))?;
            // TODO: should we try to dereference the opaque pointer?
            Ok((*z_ptr, None))
        } else if let Some((z_ptr, z_cont)) = self.z_cont_ptr_cache.get(ptr) {
            Ok((*z_ptr, z_cont.clone()))
        } else {
            let (z_ptr, z_cont) = match self.fetch_cont(ptr) {
                Some(Continuation::Outermost) => {
                    let z_cont = ZCont::<F>::Outermost;
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::Call0 {
                    saved_env,
                    continuation,
                }) => {
                    let (z_env_ptr, _) = self.get_z_expr(&saved_env, z_store)?;
                    let (z_cont_ptr, _) = self.get_z_cont(&continuation, z_store)?;
                    let z_cont = ZCont::<F>::Call0 {
                        saved_env: z_env_ptr,
                        continuation: z_cont_ptr,
                    };
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::Call {
                    saved_env,
                    unevaled_arg,
                    continuation,
                }) => {
                    let (z_env_ptr, _) = self.get_z_expr(&saved_env, z_store)?;
                    let (z_arg_ptr, _) = self.get_z_expr(&unevaled_arg, z_store)?;
                    let (z_cont_ptr, _) = self.get_z_cont(&continuation, z_store)?;
                    let z_cont = ZCont::<F>::Call {
                        unevaled_arg: z_arg_ptr,
                        saved_env: z_env_ptr,
                        continuation: z_cont_ptr,
                    };
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::Call2 {
                    saved_env,
                    function,
                    continuation,
                }) => {
                    let (z_env_ptr, _) = self.get_z_expr(&saved_env, z_store)?;
                    let (z_fun_ptr, _) = self.get_z_expr(&function, z_store)?;
                    let (z_cont_ptr, _) = self.get_z_cont(&continuation, z_store)?;
                    let z_cont = ZCont::<F>::Call2 {
                        function: z_fun_ptr,
                        saved_env: z_env_ptr,
                        continuation: z_cont_ptr,
                    };
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::Tail {
                    saved_env,
                    continuation,
                }) => {
                    let (z_env_ptr, _) = self.get_z_expr(&saved_env, z_store)?;
                    let (z_cont_ptr, _) = self.get_z_cont(&continuation, z_store)?;
                    let z_cont = ZCont::<F>::Tail {
                        saved_env: z_env_ptr,
                        continuation: z_cont_ptr,
                    };
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::Error) => {
                    let z_cont = ZCont::<F>::Error;
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::Lookup {
                    saved_env,
                    continuation,
                }) => {
                    let (z_env_ptr, _) = self.get_z_expr(&saved_env, z_store)?;
                    let (z_cont_ptr, _) = self.get_z_cont(&continuation, z_store)?;
                    let z_cont = ZCont::<F>::Lookup {
                        saved_env: z_env_ptr,
                        continuation: z_cont_ptr,
                    };
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::Unop {
                    operator,
                    continuation,
                }) => {
                    let (z_cont_ptr, _) = self.get_z_cont(&continuation, z_store)?;
                    let z_cont = ZCont::<F>::Unop {
                        operator,
                        continuation: z_cont_ptr,
                    };
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::Binop {
                    operator,
                    saved_env,
                    unevaled_args,
                    continuation,
                }) => {
                    let (z_env_ptr, _) = self.get_z_expr(&saved_env, z_store)?;
                    let (z_args_ptr, _) = self.get_z_expr(&unevaled_args, z_store)?;
                    let (z_cont_ptr, _) = self.get_z_cont(&continuation, z_store)?;
                    let z_cont = ZCont::<F>::Binop {
                        operator,
                        saved_env: z_env_ptr,
                        unevaled_args: z_args_ptr,
                        continuation: z_cont_ptr,
                    };
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::Binop2 {
                    operator,
                    evaled_arg,
                    continuation,
                }) => {
                    let (z_arg_ptr, _) = self.get_z_expr(&evaled_arg, z_store)?;
                    let (z_cont_ptr, _) = self.get_z_cont(&continuation, z_store)?;
                    let z_cont = ZCont::<F>::Binop2 {
                        operator,
                        evaled_arg: z_arg_ptr,
                        continuation: z_cont_ptr,
                    };
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::If {
                    unevaled_args,
                    continuation,
                }) => {
                    let (z_args_ptr, _) = self.get_z_expr(&unevaled_args, z_store)?;
                    let (z_cont_ptr, _) = self.get_z_cont(&continuation, z_store)?;
                    let z_cont = ZCont::<F>::If {
                        unevaled_args: z_args_ptr,
                        continuation: z_cont_ptr,
                    };
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::Let {
                    var,
                    body,
                    saved_env,
                    continuation,
                }) => {
                    let (z_var_ptr, _) = self.get_z_expr(&var, z_store)?;
                    let (z_body_ptr, _) = self.get_z_expr(&body, z_store)?;
                    let (z_env_ptr, _) = self.get_z_expr(&saved_env, z_store)?;
                    let (z_cont_ptr, _) = self.get_z_cont(&continuation, z_store)?;
                    let z_cont = ZCont::<F>::Let {
                        var: z_var_ptr,
                        body: z_body_ptr,
                        saved_env: z_env_ptr,
                        continuation: z_cont_ptr,
                    };
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::LetRec {
                    var,
                    body,
                    saved_env,
                    continuation,
                }) => {
                    let (z_var_ptr, _) = self.get_z_expr(&var, z_store)?;
                    let (z_body_ptr, _) = self.get_z_expr(&body, z_store)?;
                    let (z_env_ptr, _) = self.get_z_expr(&saved_env, z_store)?;
                    let (z_cont_ptr, _) = self.get_z_cont(&continuation, z_store)?;
                    let z_cont = ZCont::<F>::LetRec {
                        var: z_var_ptr,
                        body: z_body_ptr,
                        saved_env: z_env_ptr,
                        continuation: z_cont_ptr,
                    };
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::Emit { continuation }) => {
                    let (z_cont_ptr, _) = self.get_z_cont(&continuation, z_store)?;
                    let z_cont = ZCont::<F>::Emit {
                        continuation: z_cont_ptr,
                    };
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::Dummy) => {
                    let z_cont = ZCont::<F>::Dummy;
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::Terminal) => {
                    let z_cont = ZCont::<F>::Terminal;
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                None => {
                    let (z_ptr, _) = self.get_z_cont(ptr, z_store)?;
                    (z_ptr, None)
                }
            };

            if let Some(z_store) = z_store {
                z_store.cont_map.insert(z_ptr, z_cont.clone());
            };
            self.z_cont_ptr_map.insert(z_ptr, Box::new(*ptr));
            self.z_cont_ptr_cache
                .insert(*ptr, Box::new((z_ptr, z_cont.clone())));
            Ok((z_ptr, z_cont))
        }
    }

    pub fn to_z_store_with_ptr(&self, ptr: &Ptr<F>) -> Result<(ZStore<F>, ZExprPtr<F>), Error> {
        let z_store = ZStore::new();
        let mut store_opt = Some(z_store);
        let (z_ptr, _) = self.get_z_expr(ptr, &mut store_opt)?;
        Ok((store_opt.unwrap(), z_ptr))
    }

    pub fn to_z_expr(&self, ptr: &Ptr<F>) -> Option<ZExpr<F>> {
        self.get_z_expr(ptr, &mut None).ok()?.1
    }

    pub fn hash_expr(&self, ptr: &Ptr<F>) -> Option<ZExprPtr<F>> {
        self.get_z_expr(ptr, &mut None).ok().map(|x| x.0)
    }

    // TODO: Add errors as below
    //pub fn hash_expr(&self, ptr: &Ptr<F>) -> Result<ZExprPtr<F>, Error> {
    //    self.get_z_expr(ptr, None).map(|x| x.0)
    //}

    pub fn to_z_cont(&self, ptr: &ContPtr<F>) -> Option<ZCont<F>> {
        self.get_z_cont(ptr, &mut None).ok()?.1
    }

    pub fn hash_cont(&self, ptr: &ContPtr<F>) -> Option<ZContPtr<F>> {
        self.get_z_cont(ptr, &mut None).ok().map(|x| x.0)
    }

    pub fn car_cdr(&self, ptr: &Ptr<F>) -> Result<(Ptr<F>, Ptr<F>), Error> {
        match ptr.tag {
            ExprTag::Nil => Ok((lurk_sym_ptr!(self, nil), lurk_sym_ptr!(self, nil))),
            ExprTag::Cons => match self.fetch(ptr) {
                Some(Expression::Cons(car, cdr)) => Ok((car, cdr)),
                e => Err(Error(format!(
                    "Can only extract car_cdr from known Cons, instead got {ptr:?} {e:?}",
                ))),
            },
            ExprTag::Str => match self.fetch(ptr) {
                Some(Expression::Str(car, cdr)) => Ok((car, cdr)),
                Some(Expression::EmptyStr) => Ok((lurk_sym_ptr!(self, nil), self.strnil())),
                _ => unreachable!(),
            },
            _ => Err(Error("Can only extract car_cdr from Cons".into())),
        }
    }

    pub fn get_opaque_ptr(&self, ptr: Ptr<F>) -> Option<ZExprPtr<F>> {
        let s = self.opaque_ptrs.get_index(ptr.raw.opaque_idx()?)?;
        Some(*s)
    }

    // An opaque Ptr is one for which we have the hash, but not the preimages.
    // So we cannot open or traverse the enclosed data, but we can manipulate
    // it atomically and include it in containing structures, etc.
    pub fn new_opaque_ptr(&self) -> Ptr<F> {
        // TODO: May need new tag for this.
        // Meanwhile, it is illegal to try to dereference/follow an opaque PTR.
        // So any tag and RawPtr are okay.
        let z_ptr = ZExpr::Nil.z_ptr(&self.poseidon_cache);
        let (i, _) = self.opaque_ptrs.insert_probe(Box::new(z_ptr));
        Ptr::opaque(ExprTag::Nil, i)
    }

    pub fn ptr_eq(&self, a: &Ptr<F>, b: &Ptr<F>) -> Result<bool, Error> {
        // In order to compare Ptrs, we *must* resolve the hashes. Otherwise, we risk failing to recognize equality of
        // compound data with opaque data in either element's transitive closure.
        match (self.hash_expr(a), self.hash_expr(b)) {
            (Some(a_hash), Some(b_hash)) => Ok(a.tag == b.tag && a_hash == b_hash),
            _ => Err(Error(
                "one or more values missing when comparing Ptrs for equality".into(),
            )),
        }
    }

    /// Fill the cache for Scalars. Only Ptrs which have been interned since last hydration will be hashed, so it is
    /// safe to call this incrementally. However, for best proving performance, we should call exactly once so all
    /// hashing can be batched, e.g. on the GPU.
    #[tracing::instrument(skip_all, name = "Store::hydrate_scalar_cache")]
    pub fn hydrate_scalar_cache(&self) {
        self.ensure_constants();

        self.dehydrated
            .load()
            .iter()
            .collect::<Vec<_>>()
            .par_iter()
            .for_each(|ptr| {
                self.hash_expr(ptr).expect("failed to hash_expr");
            });

        self.dehydrated.swap(Arc::new(FrozenVec::default()));

        self.dehydrated_cont
            .load()
            .iter()
            .collect::<Vec<_>>()
            .par_iter()
            .for_each(|ptr| {
                self.hash_cont(ptr).expect("failed to hash_cont");
            });

        self.dehydrated_cont.swap(Arc::new(FrozenVec::default()));
    }

    fn ensure_constants(&self) {
        if self.constants.get().is_none() {
            let new = NamedConstants::new(self);
            self.constants.set(new).expect("constants are not set");
        }
    }

    /// The only places that `ZPtr`s for `Ptr`s should be created, to
    /// ensure that they are cached properly
    fn create_z_expr_ptr(&self, ptr: Ptr<F>, hash: F) -> ZExprPtr<F> {
        let z_ptr = ZPtr(ptr.tag, hash);
        self.z_expr_ptr_map.insert(z_ptr, Box::new(ptr));
        z_ptr
    }

    pub fn z_expr_ptr_from_parts(&self, tag: F, value: F) -> Result<ZExprPtr<F>, Error> {
        let tag = ExprTag::from_field(&tag).ok_or(Error("ExprTag error".to_string()))?;
        let zptr = ZPtr(tag, value);
        if self.z_expr_ptr_map.get(&zptr).is_some() {
            Ok(zptr)
        } else {
            Err(Error("uncached z_expr_ptr".to_string()))
        }
    }

    pub fn z_cont_ptr_from_parts(&self, tag: F, value: F) -> Result<ZContPtr<F>, Error> {
        let tag = ContTag::from_field(&tag).ok_or(Error("ContTag error".to_string()))?;
        let zptr = ZPtr(tag, value);
        if self.z_cont_ptr_map.get(&zptr).is_some() {
            Ok(zptr)
        } else {
            Err(Error("uncached z_cont_ptr".to_string()))
        }
    }

    pub fn intern_z_expr_ptr(&self, z_ptr: &ZExprPtr<F>, z_store: &ZStore<F>) -> Option<Ptr<F>> {
        if let Some(ptr) = self.fetch_z_expr_ptr(z_ptr) {
            Some(ptr)
        } else {
            use ZExpr::{
                Char, Comm, Cons, EmptyStr, Fun, Key, Nil, Num, RootSym, Str, Sym, Thunk, UInt,
            };
            match (z_ptr.tag(), z_store.get_expr(z_ptr)) {
                (ExprTag::Nil, Some(Nil)) => {
                    let ptr = lurk_sym_ptr!(self, nil);
                    self.create_z_expr_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Cons, Some(Cons(car, cdr))) => {
                    let car = self.intern_z_expr_ptr(&car, z_store)?;
                    let cdr = self.intern_z_expr_ptr(&cdr, z_store)?;
                    let ptr = self.intern_cons(car, cdr);
                    self.create_z_expr_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Comm, Some(Comm(secret, payload))) => {
                    let payload = self.intern_z_expr_ptr(&payload, z_store)?;
                    let ptr = self.intern_comm(secret, payload);
                    self.create_z_expr_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Str, Some(EmptyStr)) => {
                    let ptr = self.strnil();
                    self.create_z_expr_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Str, Some(Str(strcar, strcdr))) => {
                    let strcar = self.intern_z_expr_ptr(&strcar, z_store)?;
                    let strcdr = self.intern_z_expr_ptr(&strcdr, z_store)?;
                    let ptr = self.intern_strcons(strcar, strcdr);
                    self.create_z_expr_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Sym, Some(RootSym)) => {
                    let ptr = self.intern_symnil(false);
                    self.create_z_expr_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Key, Some(RootSym)) => {
                    let ptr = self.intern_symnil(true);
                    self.create_z_expr_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Sym, Some(Sym(symcar, symcdr))) => {
                    let symcar = self.intern_z_expr_ptr(&symcar, z_store)?;
                    let symcdr = self.intern_z_expr_ptr(&symcdr, z_store)?;
                    let ptr = self.intern_symcons(symcar, symcdr);
                    self.create_z_expr_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Key, Some(Key(keycar, keycdr))) => {
                    let keycar = self.intern_z_expr_ptr(&keycar, z_store)?;
                    let keycdr = self.intern_z_expr_ptr(&keycdr, z_store)?;
                    let ptr = self.intern_keycons(keycar, keycdr);
                    self.create_z_expr_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Num, Some(Num(x))) => {
                    let ptr = self.intern_num(crate::Num::Scalar(x));
                    self.create_z_expr_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Char, Some(Char(x))) => Some(x.into()),
                (ExprTag::U64, Some(UInt(x))) => Some(self.intern_uint(x)),
                (ExprTag::Thunk, Some(Thunk(value, continuation))) => {
                    let value = self.intern_z_expr_ptr(&value, z_store)?;
                    let continuation = self.intern_z_cont_ptr(&continuation, z_store)?;
                    let ptr = self.intern_thunk(expr::Thunk {
                        value,
                        continuation,
                    });
                    self.create_z_expr_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (
                    ExprTag::Fun,
                    Some(Fun {
                        arg,
                        body,
                        closed_env,
                    }),
                ) => {
                    let arg = self.intern_z_expr_ptr(&arg, z_store)?;
                    let body = self.intern_z_expr_ptr(&body, z_store)?;
                    let env = self.intern_z_expr_ptr(&closed_env, z_store)?;
                    let ptr = self.intern_fun(arg, body, env);
                    self.create_z_expr_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (tag, None) => {
                    let ptr = self.intern_maybe_opaque(*tag, z_ptr.1);
                    self.create_z_expr_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                _ => {
                    // println!("Failed to get ptr for zptr: {:?}", z_ptr);
                    None
                }
            }
        }
    }

    fn create_z_cont_ptr(&self, ptr: ContPtr<F>, hash: F) -> ZContPtr<F> {
        let z_ptr = ZPtr(ptr.tag, hash);
        self.z_cont_ptr_map.insert(z_ptr, Box::new(ptr));
        z_ptr
    }

    pub fn intern_z_cont_ptr(
        &self,
        z_ptr: &ZContPtr<F>,
        z_store: &ZStore<F>,
    ) -> Option<ContPtr<F>> {
        use ZCont::{
            Binop, Binop2, Call, Call0, Call2, Dummy, Emit, Error, If, Let, LetRec, Lookup,
            Outermost, Tail, Terminal, Unop,
        };
        let tag: ContTag = *z_ptr.tag();

        if let Some(cont) = z_store.get_cont(z_ptr) {
            let continuation = match cont {
                Outermost => Continuation::Outermost,
                Dummy => Continuation::Dummy,
                Terminal => Continuation::Terminal,
                Call0 {
                    saved_env,
                    continuation,
                } => Continuation::Call0 {
                    saved_env: self.intern_z_expr_ptr(&saved_env, z_store)?,
                    continuation: self.intern_z_cont_ptr(&continuation, z_store)?,
                },
                Call {
                    saved_env,
                    unevaled_arg,
                    continuation,
                } => Continuation::Call {
                    saved_env: self.intern_z_expr_ptr(&saved_env, z_store)?,
                    unevaled_arg: self.intern_z_expr_ptr(&unevaled_arg, z_store)?,
                    continuation: self.intern_z_cont_ptr(&continuation, z_store)?,
                },
                Call2 {
                    saved_env,
                    function,
                    continuation,
                } => Continuation::Call2 {
                    saved_env: self.intern_z_expr_ptr(&saved_env, z_store)?,
                    function: self.intern_z_expr_ptr(&function, z_store)?,
                    continuation: self.intern_z_cont_ptr(&continuation, z_store)?,
                },
                Tail {
                    saved_env,
                    continuation,
                } => Continuation::Tail {
                    saved_env: self.intern_z_expr_ptr(&saved_env, z_store)?,
                    continuation: self.intern_z_cont_ptr(&continuation, z_store)?,
                },
                Error => Continuation::Error,
                Lookup {
                    saved_env,
                    continuation,
                } => Continuation::Lookup {
                    saved_env: self.intern_z_expr_ptr(&saved_env, z_store)?,
                    continuation: self.intern_z_cont_ptr(&continuation, z_store)?,
                },
                Unop {
                    operator,
                    continuation,
                } => Continuation::Unop {
                    operator,
                    continuation: self.intern_z_cont_ptr(&continuation, z_store)?,
                },
                Binop {
                    operator,
                    saved_env,
                    unevaled_args,
                    continuation,
                } => Continuation::Binop {
                    operator,
                    saved_env: self.intern_z_expr_ptr(&saved_env, z_store)?,
                    unevaled_args: self.intern_z_expr_ptr(&unevaled_args, z_store)?,
                    continuation: self.intern_z_cont_ptr(&continuation, z_store)?,
                },
                Binop2 {
                    operator,
                    evaled_arg,
                    continuation,
                } => Continuation::Binop2 {
                    operator,
                    evaled_arg: self.intern_z_expr_ptr(&evaled_arg, z_store)?,
                    continuation: self.intern_z_cont_ptr(&continuation, z_store)?,
                },
                If {
                    unevaled_args,
                    continuation,
                } => Continuation::If {
                    unevaled_args: self.intern_z_expr_ptr(&unevaled_args, z_store)?,
                    continuation: self.intern_z_cont_ptr(&continuation, z_store)?,
                },
                Let {
                    var,
                    body,
                    saved_env,
                    continuation,
                } => Continuation::Let {
                    var: self.intern_z_expr_ptr(&var, z_store)?,
                    body: self.intern_z_expr_ptr(&body, z_store)?,
                    saved_env: self.intern_z_expr_ptr(&saved_env, z_store)?,
                    continuation: self.intern_z_cont_ptr(&continuation, z_store)?,
                },
                LetRec {
                    var,
                    body,
                    saved_env,
                    continuation,
                } => Continuation::LetRec {
                    var: self.intern_z_expr_ptr(&var, z_store)?,
                    body: self.intern_z_expr_ptr(&body, z_store)?,
                    saved_env: self.intern_z_expr_ptr(&saved_env, z_store)?,
                    continuation: self.intern_z_cont_ptr(&continuation, z_store)?,
                },
                Emit { continuation } => Continuation::Emit {
                    continuation: self.intern_z_cont_ptr(&continuation, z_store)?,
                },
            };

            if continuation.cont_tag() == tag {
                let ptr = continuation.intern_aux(self);
                self.create_z_cont_ptr(ptr, *z_ptr.value());
                Some(ptr)
            } else {
                None
            }
        } else {
            None
        }
    }
}

impl<F: LurkField> Expression<F> {
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
        matches!(self, Self::Sym(..) | Self::RootSym)
    }
    pub const fn is_fun(&self) -> bool {
        matches!(self, Self::Fun(_, _, _))
    }

    pub const fn is_num(&self) -> bool {
        matches!(self, Self::Num(_))
    }
    pub const fn is_str(&self) -> bool {
        matches!(self, Self::Str(..) | Self::EmptyStr)
    }

    pub const fn is_thunk(&self) -> bool {
        matches!(self, Self::Thunk(_))
    }
}

#[derive(Copy, Clone, Debug)]
pub struct ConstantPtrs<F: LurkField>(Option<ZExprPtr<F>>, Ptr<F>);

impl<F: LurkField> ConstantPtrs<F> {
    pub fn value(&self) -> F {
        *self.z_ptr().value()
    }
    pub fn z_ptr(&self) -> ZExprPtr<F> {
        self.0
            .expect("ZExprPtr missing; hydrate_scalar_cache should have been called.")
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
        let nil_ptr = store.intern_symbol(&lurk_sym("nil"));
        let nil_z_ptr = Some(ZExpr::Nil.z_ptr(&store.poseidon_cache));

        let hash_sym = |name: &str| {
            let ptr = store.intern_symbol(&lurk_sym(name));
            let maybe_z_ptr = store.hash_expr(&ptr);
            ConstantPtrs(maybe_z_ptr, ptr)
        };

        let nil = ConstantPtrs(nil_z_ptr, nil_ptr);
        let t = hash_sym("t");
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

impl<F: LurkField> ZStore<F> {
    pub fn to_store(&self) -> Store<F> {
        let store = Store::new();

        for ptr in self.expr_map.keys() {
            store.intern_z_expr_ptr(ptr, self);
        }
        for ptr in self.cont_map.keys() {
            store.intern_z_cont_ptr(ptr, self);
        }
        store
    }

    pub fn to_store_with_z_ptr(&self, z_ptr: &ZExprPtr<F>) -> Result<(Store<F>, Ptr<F>), Error> {
        let store = Store::new();

        for z_ptr in self.expr_map.keys() {
            store.intern_z_expr_ptr(z_ptr, self);
        }
        for z_ptr in self.cont_map.keys() {
            store.intern_z_cont_ptr(z_ptr, self);
        }
        match store.intern_z_expr_ptr(z_ptr, self) {
            Some(ptr_ret) => Ok((store, ptr_ret)),
            None => Err(Error("Couldn't find given ZExprPtr".into())),
        }
    }
}

#[cfg(test)]
pub mod test {
    use super::*;

    use crate::state::{initial_lurk_state, State};
    use crate::writer::Write;
    use crate::{
        eval::{
            empty_sym_env,
            lang::{Coproc, Lang},
            Evaluator,
        },
        parser::position::Pos,
    };
    use crate::{list, num, symbol};

    use ff::Field;
    use pasta_curves::pallas::Scalar as Fr;
    use pasta_curves::pallas::Scalar as S1;
    use rand::rngs::OsRng;

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
        use super::ContTag::{
            Binop, Binop2, Call, Call0, Call2, Dummy, Emit, Error, If, Let, LetRec, Lookup,
            Outermost, Tail, Terminal, Unop,
        };

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
        let store = Store::<Fr>::default();

        let num_ptr = store.num(123);
        let num = store.fetch(&num_ptr).unwrap();
        let num_again = store.fetch(&num_ptr).unwrap();

        assert_eq!(num, num_again);
    }

    #[test]
    fn equality() {
        let store = Store::<Fr>::default();

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
        let store = Store::<Fr>::default();

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

        let eq = lurk_sym_ptr!(store, equal);
        let t = lurk_sym_ptr!(store, t);
        let nil = lurk_sym_ptr!(store, nil);
        let limit = 10;
        let lang: Lang<Fr, Coproc<Fr>> = Lang::new();
        {
            let comparison_expr = store.list(&[eq, fun, opaque_fun]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &store, limit, &lang)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, fun2, opaque_fun]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &store, limit, &lang)
                .eval()
                .unwrap();
            assert_eq!(nil, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, fun2, opaque_fun2]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &store, limit, &lang)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
        {
            // This test is important. It demonstrates that we can handle opaque data in compound data being evaluated
            // without this affecting equality semantics.

            let n = store.num(123);
            let cons = lurk_sym_ptr!(store, cons);
            let cons_expr1 = store.list(&[cons, fun, n]);
            let cons_expr2 = store.list(&[cons, opaque_fun, n]);

            let comparison_expr = store.list(&[eq, cons_expr1, cons_expr2]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &store, limit, &lang)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
    }

    #[test]
    fn opaque_sym() {
        let store = Store::<Fr>::default();

        let empty_env = empty_sym_env(&store);
        let sym = store.sym("sym");
        let sym2 = store.sym("sym2");
        let sym_hash = store.hash_expr(&sym).unwrap();
        let sym_hash2 = store.hash_expr(&sym2).unwrap();
        let opaque_sym = store.intern_opaque_sym(*sym_hash.value());
        let opaque_sym2 = store.intern_opaque_sym(*sym_hash2.value());

        let quote = lurk_sym_ptr!(store, quote);
        let qsym = store.list(&[quote, sym]);
        let qsym2 = store.list(&[quote, sym2]);
        let qsym_opaque = store.list(&[quote, opaque_sym]);
        let qsym_opaque2 = store.list(&[quote, opaque_sym2]);

        let eq = lurk_sym_ptr!(store, equal);
        let t = lurk_sym_ptr!(store, t);
        let nil = lurk_sym_ptr!(store, nil);
        let limit = 10;

        let state = initial_lurk_state();

        // When an opaque sym is inserted into a store which contains the same sym, the store knows its identity.
        // Should we just immediately coalesce and never create an opaque version in that case? Probably not because
        // that may interact badly with explicit hiding to be implemented.
        // Let's defer any such considerations until we have a well-specified way of segreting secret/private data.
        //
        // If implemented, the following commented test would pass.
        // assert_eq!(sym.fmt_to_string(&store), opaque_sym.fmt_to_string(&store));

        // For now, all opaque data remains opaque, even if the Store has enough information to clarify it.
        assert!(sym.fmt_to_string(&store, state) != opaque_sym.fmt_to_string(&store, state));

        let other_store = Store::<Fr>::default();
        let other_opaque_sym = other_store.intern_opaque_sym(*sym_hash.value());

        let other_sym = other_store.sym("sym");
        // other_sym and other_opaque_sym are not equal, since the non-opaque symbol was inserted after the opaque one.
        // TODO: we could check for this and fix when inserting non-opaque syms. If we decide to clarify opaque data
        // when possible, we should do this too.
        assert!(
            other_sym.fmt_to_string(&other_store, state)
                != other_opaque_sym.fmt_to_string(&other_store, state)
        );

        let num = num::Num::from_scalar(*sym_hash.value());
        assert_eq!(
            format!(
                "<Opaque Sym {}>",
                Expression::Num(num).fmt_to_string(&store, state)
            ),
            other_opaque_sym.fmt_to_string(&other_store, state)
        );

        // We need to insert a few opaque syms in other_store, in order to acquire a raw_ptr that doesn't exist in
        // store. Use that to check for a malformed/missing opaque sym in store below.
        let _other_opaque_sym2 = other_store.intern_opaque_sym(*sym_hash.value());

        let lang = Lang::<Fr, Coproc<Fr>>::new();
        {
            let comparison_expr = store.list(&[eq, qsym, qsym_opaque]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &store, limit, &lang)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, qsym2, qsym_opaque]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &store, limit, &lang)
                .eval()
                .unwrap();
            assert_eq!(nil, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, qsym2, qsym_opaque2]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &store, limit, &lang)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
        {
            // This test is important. It demonstrates that we can handle opaque data in compound data being evaluated
            // without this affecting equality semantics.

            let n = store.num(123);
            let cons = lurk_sym_ptr!(store, cons);
            let cons_expr1 = store.list(&[cons, qsym, n]);
            let cons_expr2 = store.list(&[cons, qsym_opaque, n]);

            let comparison_expr = store.list(&[eq, cons_expr1, cons_expr2]);
            let lang: Lang<Fr, Coproc<Fr>> = Lang::new();
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &store, limit, &lang)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
    }

    #[test]
    fn opaque_cons() {
        let store = Store::<Fr>::default();

        let num1 = store.num(123);
        let num2 = store.num(987);
        let empty_env = empty_sym_env(&store);
        let cons = store.intern_cons(num1, num2);
        let cons2 = store.intern_cons(num2, num1);
        let cons_hash = store.hash_expr(&cons).unwrap();
        let cons_hash2 = store.hash_expr(&cons2).unwrap();
        let opaque_cons = store.intern_opaque_cons(*cons_hash.value());
        let opaque_cons2 = store.intern_opaque_cons(*cons_hash2.value());

        let eq = lurk_sym_ptr!(store, equal);
        let t = lurk_sym_ptr!(store, t);
        let nil = lurk_sym_ptr!(store, nil);
        let limit = 10;
        let quote = lurk_sym_ptr!(store, quote);
        let qcons = store.list(&[quote, cons]);
        let qcons2 = store.list(&[quote, cons2]);
        let qcons_opaque = store.list(&[quote, opaque_cons]);
        let qcons_opaque2 = store.list(&[quote, opaque_cons2]);

        let num = Expression::Num(num::Num::Scalar(*cons_hash.value()));
        let lang = Lang::<Fr, Coproc<Fr>>::new();

        let state = initial_lurk_state();

        assert_eq!(
            format!("<Opaque Cons {}>", num.fmt_to_string(&store, state)),
            opaque_cons.fmt_to_string(&store, state)
        );

        {
            let comparison_expr = store.list(&[eq, qcons, qcons_opaque]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &store, limit, &lang)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, qcons2, qcons_opaque]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &store, limit, &lang)
                .eval()
                .unwrap();
            assert_eq!(nil, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, qcons2, qcons_opaque2]);
            let (result, _, _) = Evaluator::new(comparison_expr, empty_env, &store, limit, &lang)
                .eval()
                .unwrap();
            assert_eq!(t, result.expr);
        }
        {
            // This test is important. It demonstrates that we can handle opaque data in compound data being evaluated
            // without this affecting equality semantics.

            let n = store.num(123);
            let n2 = store.num(321);
            let cons_sym = lurk_sym_ptr!(store, cons);
            let cons_expr1 = store.list(&[cons_sym, qcons, n]);
            let cons_expr2 = store.list(&[cons_sym, qcons_opaque, n]);
            let cons_expr3 = store.list(&[cons_sym, qcons_opaque, n2]);

            let comparison_expr = store.list(&[eq, cons_expr1, cons_expr2]);
            let comparison_expr2 = store.list(&[eq, cons_expr1, cons_expr3]);

            let lang: Lang<Fr, Coproc<Fr>> = Lang::new();
            {
                let (result, _, _) =
                    Evaluator::new(comparison_expr, empty_env, &store, limit, &lang)
                        .eval()
                        .unwrap();
                assert_eq!(t, result.expr);
            }
            {
                let (result, _, _) =
                    Evaluator::new(comparison_expr2, empty_env, &store, limit, &lang)
                        .eval()
                        .unwrap();
                assert_eq!(nil, result.expr);
            }
        }
    }

    fn make_maybe_opaque_cons(store: &Store<Fr>, car: u64, cdr: u64) -> Ptr<Fr> {
        let num1 = store.num(Num::<Fr>::from(car));
        let num2 = store.num(Num::<Fr>::from(cdr));
        let cons = store.intern_cons(num1, num2);
        let cons_hash = store.hash_expr(&cons).unwrap();

        store.intern_maybe_opaque_cons(*cons_hash.value())
    }

    fn make_opaque_cons(store: &Store<Fr>) -> Ptr<Fr> {
        store.intern_opaque_cons(12345.into())
    }

    #[test]
    #[should_panic]
    fn opaque_cons_car() {
        let store = Store::<Fr>::default();

        let opaque_cons = make_opaque_cons(&store);
        store.car(&opaque_cons).unwrap();
    }
    #[test]
    #[should_panic]
    fn opaque_cons_cdr() {
        let store = Store::<Fr>::default();

        let opaque_cons = make_opaque_cons(&store);
        store.cdr(&opaque_cons).unwrap();
    }

    #[test]
    fn maybe_opaque_cons_car() {
        let store = Store::<Fr>::default();

        let opaque_cons = make_maybe_opaque_cons(&store, 123, 987);
        store.car(&opaque_cons).unwrap();
    }
    #[test]
    fn maybe_opaque_cons_cdr() {
        let store = Store::<Fr>::default();

        let opaque_cons = make_maybe_opaque_cons(&store, 123, 987);
        store.cdr(&opaque_cons).unwrap();
    }

    #[test]
    fn symbol_hashing() {
        let s = &mut Store::<Fr>::default();
        let foo_ptr = s.intern_string("foo");
        let bar_ptr = s.intern_string("bar");
        let foo_bar_ptr = s.intern_symbol(&Symbol::sym_from_vec(vec!["foo".into(), "bar".into()]));

        let foo_z_ptr = s.hash_expr(&foo_ptr).unwrap();
        let bar_z_ptr = s.hash_expr(&bar_ptr).unwrap();
        let foo_bar_hash = s.hash_expr(&foo_bar_ptr).unwrap().1;

        let foo_bar_hash_manual = s.poseidon_cache.hash4(&[
            bar_z_ptr.0.to_field(),
            bar_z_ptr.1,
            ExprTag::Sym.to_field(),
            s.poseidon_cache.hash4(&[
                foo_z_ptr.0.to_field(),
                foo_z_ptr.1,
                ExprTag::Sym.to_field(),
                Fr::ZERO,
            ]),
        ]);
        assert_eq!(foo_bar_hash, foo_bar_hash_manual);
    }

    #[test]
    fn sym_and_key_hashes() {
        let s = &mut Store::<Fr>::default();

        let sym_ptr = s.intern_symbol(&Symbol::sym(&["a", "b", "c"]));
        let key_ptr = s.intern_symbol(&Symbol::key(&["a", "b", "c"]));

        let sym_z_ptr = s.hash_expr(&sym_ptr).unwrap();
        let key_z_ptr = s.hash_expr(&key_ptr).unwrap();
        let sym_hash = sym_z_ptr.1;
        let key_hash = key_z_ptr.1;

        assert_ne!(sym_ptr, key_ptr);
        assert_ne!(sym_z_ptr, key_z_ptr);
        assert_eq!(sym_hash, key_hash);
    }

    #[test]
    fn sym_in_list() {
        let store = &mut Store::<Fr>::default();

        let foo_list = list!(Fr, [symbol!(["foo"])]);
        let foo_sym = symbol!(Fr, ["foo"]);

        let expr = store.intern_syntax(foo_list);
        let sym = store.intern_syntax(foo_sym);
        let sym1 = store.car(&expr).unwrap();
        let sss = store.fetch_sym(&sym);
        let hash = store.hash_expr(&sym);
        tracing::debug!("{:?} {:?} {:?}", &sym1, &sss, &hash);

        assert_eq!(sym, sym1);
    }

    #[test]
    fn empty_sym_tag_hash() {
        let s = &mut Store::<Fr>::default();

        let sym = s.sym("");
        let sym_tag = s.hash_expr(&sym).unwrap().0;
        // let sym_hash = s.hash_expr(&sym).unwrap().1;

        assert_eq!(ExprTag::Sym, sym_tag);

        // FIXME: What should this be? Should this even be allowed?
        // assert_eq!(Fr::from(0), sym_hash)
    }

    #[test]
    fn str_car_cdr_hashes() {
        let s = &mut Store::<Fr>::default();

        let str = s.intern_string("ORANGE");
        let str2 = s.cdr(&str).unwrap();
        let c = s.car(&str).unwrap();

        let str_hash = s.hash_expr(&str).unwrap().1;

        let str_again = s.cons(c, str2);
        let str_again_hash = s.hash_expr(&str_again).unwrap().1;

        assert_eq!(str_hash, str_again_hash);
    }

    fn str_inner_fetch_aux(str: &str, hydrate: bool) {
        let s = &mut Store::<Fr>::default();

        let str = s.intern_string(str);
        let str2 = s.cdr(&str).unwrap();

        // Unless the cache is hydrated, the inner destructuring will not map the ZExprPtr to corresponding Ptr.
        if hydrate {
            s.hydrate_scalar_cache();
        };

        let str2_z_ptr = s.hash_expr(&str2).unwrap();

        let str2_again = s.fetch_z_expr_ptr(&str2_z_ptr).unwrap();

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

        let str = s.intern_string("");

        // Unless the cache is hydrated, the inner destructuring will not map the ZExprPtr to corresponding Ptr.
        if hydrate {
            s.hydrate_scalar_cache();
        };

        let str_z_ptr = s.hash_expr(&str).unwrap();

        let str_again = s.fetch_z_expr_ptr(&str_z_ptr).unwrap();

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

        let num = num::Num::from_scalar(scalar);
        let state = initial_lurk_state();
        assert_eq!(
            format!(
                "<Opaque Comm {}>",
                Expression::Num(num).fmt_to_string(s, state)
            ),
            opaque_comm.fmt_to_string(s, state),
        );
    }

    fn commit_and_open(store: &Store<S1>, expr: Ptr<S1>) -> Ptr<S1> {
        let secret = <S1>::random(OsRng);
        let comm = store.hide(secret, expr);

        let (_, new_ptr) = store.open(comm).unwrap();
        assert_eq!(expr, new_ptr);
        comm
    }

    #[test]
    fn commitment_z_store_roundtrip() {
        let store = &mut Store::<S1>::default();
        let state = State::init_lurk_state().rccell();
        let two = store.read_with_state(state.clone(), "(+ 1 1)").unwrap();
        let three = store.read_with_state(state, "(+ 1 2)").unwrap();

        let comm2 = commit_and_open(store, two);
        let comm3 = commit_and_open(store, three);

        store.hydrate_scalar_cache();

        let (z_store, z_ptr) = ZStore::new_with_expr(store, &comm2);
        let z_ptr = z_ptr.unwrap();

        let (store, _ptr) = z_store.to_store_with_z_ptr(&z_ptr).unwrap();
        let (_, two_opened) = store.open(comm2).unwrap();
        // The `cons_store` indices are scrambled when converting to a ZStore, so we
        // hash each pointer to check equality
        assert!(store.ptr_eq(&two, &two_opened).unwrap());

        assert!(store.open(comm3).is_none());
    }
}
