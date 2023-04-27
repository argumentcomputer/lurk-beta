use itertools::Itertools;
use rayon::prelude::*;
use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;
use std::usize;
use string_interner::symbol::{Symbol, SymbolUsize};
use thiserror;

use once_cell::sync::OnceCell;

use crate::cont::Continuation;
use crate::expr;
use crate::expr::{Expression, Thunk};
use crate::field::{FWrap, LurkField};
use crate::package::{Package, LURK_EXTERNAL_SYMBOL_NAMES};
use crate::parser::{convert_sym_case, names_keyword};
use crate::ptr::{ContPtr, Ptr};
use crate::sym::Sym;
use crate::tag::{ContTag, ExprTag, Op1, Op2, Tag};
use crate::z_data::{ZCont, ZContPtr, ZExpr, ZExprPtr, ZPtr, ZStore};
use crate::{Num, UInt};
use crate::cache_map::CacheMap;

use crate::hash::{HashConstants, PoseidonCache};

type IndexSet<K> = indexmap::IndexSet<K, ahash::RandomState>;

#[derive(Debug)]
pub struct StringSet(
    pub  string_interner::StringInterner<
        string_interner::backend::BufferBackend<SymbolUsize>,
        ahash::RandomState,
    >,
);

impl Default for StringSet {
    fn default() -> Self {
        StringSet(string_interner::StringInterner::new())
    }
}

impl StringSet {
    #[allow(dead_code)]
    pub fn all_strings(&self) -> Vec<&str> {
        self.0.into_iter().map(|x| x.1).collect::<Vec<_>>()
    }
}

#[derive(Debug)]
pub struct Store<F: LurkField> {
    pub cons_store: IndexSet<(Ptr<F>, Ptr<F>)>,
    pub comm_store: IndexSet<(FWrap<F>, Ptr<F>)>,

    pub fun_store: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>)>,

    pub sym_store: StringSet,

    // Other sparse storage format without hashing is likely more efficient
    pub num_store: IndexSet<Num<F>>,

    pub str_store: StringSet,
    pub thunk_store: IndexSet<Thunk<F>>,
    pub call0_store: IndexSet<(Ptr<F>, ContPtr<F>)>,
    pub call_store: IndexSet<(Ptr<F>, Ptr<F>, ContPtr<F>)>,
    pub call2_store: IndexSet<(Ptr<F>, Ptr<F>, ContPtr<F>)>,
    pub tail_store: IndexSet<(Ptr<F>, ContPtr<F>)>,
    pub lookup_store: IndexSet<(Ptr<F>, ContPtr<F>)>,
    pub unop_store: IndexSet<(Op1, ContPtr<F>)>,
    pub binop_store: IndexSet<(Op2, Ptr<F>, Ptr<F>, ContPtr<F>)>,
    pub binop2_store: IndexSet<(Op2, Ptr<F>, ContPtr<F>)>,
    pub if_store: IndexSet<(Ptr<F>, ContPtr<F>)>,
    pub let_store: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>, ContPtr<F>)>,
    pub letrec_store: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>, ContPtr<F>)>,
    pub emit_store: IndexSet<ContPtr<F>>,

    pub opaque_ptrs: IndexSet<ZExprPtr<F>>,
    pub opaque_cont_ptrs: IndexSet<ZContPtr<F>>,

    /// Holds a mapping of ZExprPtr -> Ptr for reverse lookups
    pub z_expr_ptr_map: CacheMap<ZExprPtr<F>, Box<Ptr<F>>>,
    /// Holds a mapping of ZExprPtr -> ContPtr<F> for reverse lookups
    pub z_cont_ptr_map: CacheMap<ZContPtr<F>, Box<ContPtr<F>>>,

    /// Caches poseidon hashes
    pub poseidon_cache: PoseidonCache<F>,
    /// Contains Ptrs which have not yet been hydrated.
    pub dehydrated: Vec<Ptr<F>>,
    pub dehydrated_cont: Vec<ContPtr<F>>,

    pub lurk_package: Arc<Package>,
    pub constants: OnceCell<NamedConstants<F>>,

    /// Speeds up the internalization of strings into the ZStore
    /// When interning "blah", search for ['h', 'a', 'l', 'b']
    vec_char_cache: CacheMap<Vec<char>, Box<(ZExprPtr<F>, ZExpr<F>)>>,
    /// Speeds up the internalization of symbols into the ZStore
    /// When interning .foo.bar, search for ["bar", "foo"]
    vec_str_cache: CacheMap<Vec<String>, Box<(ZExprPtr<F>, ZExpr<F>)>>,
}

pub trait TypePredicates {
    fn is_fun(&self) -> bool;
    fn is_self_evaluating(&self) -> bool;
    fn is_potentially(&self, tag: ExprTag) -> bool;
}

impl<F: LurkField> TypePredicates for Ptr<F> {
    fn is_fun(&self) -> bool {
        self.tag.is_fun()
    }
    fn is_self_evaluating(&self) -> bool {
        self.tag.is_self_evaluating()
    }
    fn is_potentially(&self, tag: ExprTag) -> bool {
        self.tag.is_potentially(tag)
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
            opaque_ptrs: Default::default(),
            opaque_cont_ptrs: Default::default(),
            z_expr_ptr_map: Default::default(),
            z_cont_ptr_map: Default::default(),
            poseidon_cache: Default::default(),
            dehydrated: Default::default(),
            dehydrated_cont: Default::default(),
            lurk_package: Arc::new(Package::lurk()),
            constants: Default::default(),
            vec_char_cache: Default::default(),
            vec_str_cache: Default::default(),
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
            .map(|c| Ptr::index(ExprTag::Comm, c))
    }

    pub fn hide(&mut self, secret: F, payload: Ptr<F>) -> Ptr<F> {
        self.intern_comm(secret, payload)
    }

    pub fn open(&self, ptr: Ptr<F>) -> Option<(F, Ptr<F>)> {
        let p = match ptr.tag {
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

        self.fetch_comm(&p)
            .map(|(secret, payload)| (secret.0, *payload))
    }

    pub fn open_mut(&mut self, ptr: Ptr<F>) -> Result<(F, Ptr<F>), Error> {
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

    pub fn secret_mut(&mut self, ptr: Ptr<F>) -> Result<Ptr<F>, Error> {
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

    pub fn intern_symnil(&self, key: bool) -> Ptr<F> {
        // TODO: Is this right?
        if key {
            Ptr::null(ExprTag::Key)
        } else {
            Ptr::null(ExprTag::Sym)
        }
    }

    pub fn intern_strnil(&self) -> Ptr<F> {
        // TODO: Is this right?
        Ptr::null(ExprTag::Str)
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
        let ptr = Ptr::index(ExprTag::Cons, p);
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
        assert_eq!((car.tag, cdr.tag), (ExprTag::Char, ExprTag::Str));
        let (c, s) = (
            self.fetch_char(&car).unwrap(),
            self.fetch_str(&cdr).unwrap(),
        );
        let new_str = format!("{c}{s}");

        self.intern_str(&new_str)
    }

    pub fn intern_symcons(&mut self, car: Ptr<F>, cdr: Ptr<F>, key: bool) -> Ptr<F> {
        // TODO Is this right?
        if car.is_opaque() || cdr.is_opaque() {
            self.hash_expr(&car);
            self.hash_expr(&cdr);
        }
        assert_eq!((car.tag, cdr.tag), (ExprTag::Str, ExprTag::Sym));
        let (c, s) = (self.fetch_str(&car).unwrap(), self.fetch_sym(&cdr).unwrap());
        match s.extend(&[c.to_string()]) {
            Sym::Key(sym) => {
                if key {
                    self.intern_sym(&Sym::Key(sym))
                } else {
                    self.intern_sym(&Sym::Sym(sym))
                }
            }
            Sym::Sym(sym) => {
                if key {
                    self.intern_sym(&Sym::Key(sym))
                } else {
                    self.intern_sym(&Sym::Sym(sym))
                }
            }
        }
    }

    pub fn intern_comm(&mut self, secret: F, payload: Ptr<F>) -> Ptr<F> {
        if payload.is_opaque() {
            self.hash_expr(&payload);
        }
        let (p, inserted) = self.comm_store.insert_full((FWrap(secret), payload));

        let ptr = Ptr::index(ExprTag::Comm, p);

        if inserted {
            self.dehydrated.push(ptr);
        }
        ptr
    }

    // Intern a potentially-opaque value. If the corresponding value is already known to the store,
    // return the known value.
    pub fn intern_maybe_opaque(&mut self, tag: ExprTag, hash: F) -> Ptr<F> {
        self.intern_opaque_aux(tag, hash, true)
    }

    // Intern an opaque value. If the corresponding non-opaque value is already known to the store,
    // return an opaque one anyway.
    fn intern_opaque(&mut self, tag: ExprTag, hash: F) -> Ptr<F> {
        self.intern_opaque_aux(tag, hash, false)
    }

    pub fn get_maybe_opaque(&self, tag: ExprTag, hash: F) -> Option<Ptr<F>> {
        let scalar_ptr = ZExprPtr::from_parts(tag, hash);

        let ptr = self.z_expr_ptr_map.get(&scalar_ptr);
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
        let scalar_ptr = ZExprPtr::from_parts(tag, hash);

        // Scope the first immutable borrow.
        {
            let ptr = self.z_expr_ptr_map.get(&scalar_ptr);
            if let Some(p) = ptr {
                if return_non_opaque_if_existing || p.is_opaque() {
                    return *p;
                }
            }
        }

        let (i, _) = self.opaque_ptrs.insert_full(scalar_ptr);
        Ptr::opaque(tag, i)
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

            (
                if names_keyword {
                    ExprTag::Key
                } else {
                    ExprTag::Sym
                },
                symbol_name,
            )
        };

        if let Some(ptr) = self.sym_store.0.get(&symbol_name) {
            Ptr::index(tag, ptr.to_usize())
        } else {
            let ptr = self.sym_store.0.get(symbol_name).unwrap();
            Ptr::index(tag, ptr.to_usize())
        }
    }

    fn intern_sym_by_full_name<T: AsRef<str>>(&mut self, name: T) -> Ptr<F> {
        let name = name.as_ref();
        self.hash_string(name);

        let (tag, symbol_name) = if name == ".LURK.NIL" {
            (ExprTag::Nil, "LURK.NIL")
        } else {
            let (names_keyword, symbol_name) = names_keyword(name);

            (
                if names_keyword {
                    ExprTag::Key
                } else {
                    ExprTag::Sym
                },
                symbol_name,
            )
        };

        if let Some(ptr) = self.sym_store.0.get(&symbol_name) {
            Ptr::index(tag, ptr.to_usize())
        } else {
            // We need to intern each of the path segments individually, so they will be in the store.
            // Otherwise, there can be an error when calling `hash_symbol()` with an immutable store.

            Sym::new_absolute(name.into()).path().iter().for_each(|x| {
                self.intern_str(x);
            });

            let ptr = self.sym_store.0.get_or_intern(symbol_name);
            let ptr = Ptr::index(tag, ptr.to_usize());
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
            .get_index_of::<Num<F>>(&num)
            .map(|x| Ptr::index(ExprTag::Num, x))
    }

    pub fn get_char(&self, c: char) -> Ptr<F> {
        self.get_char_from_u32(u32::from(c))
    }

    pub fn get_char_from_u32(&self, code: u32) -> Ptr<F> {
        Ptr::index(ExprTag::Char, code as usize)
    }

    pub fn get_u64(&self, n: u64) -> Ptr<F> {
        Ptr::index(ExprTag::U64, n as usize)
    }

    pub fn intern_str<T: AsRef<str>>(&mut self, str: T) -> Ptr<F> {
        // Hash string for side effect. This will cause all tails to be interned.
        self.hash_string(str.as_ref());
        self.intern_str_aux(str)
    }

    fn intern_str_aux<T: AsRef<str>>(&mut self, str: T) -> Ptr<F> {
        if let Some(ptr) = self.str_store.0.get(&str) {
            Ptr::index(ExprTag::Str, ptr.to_usize())
        } else {
            let ptr = self.str_store.0.get_or_intern(str);
            let ptr = Ptr::index(ExprTag::Str, ptr.to_usize());

            self.dehydrated.push(ptr);
            ptr
        }
    }

    pub fn get_str<T: AsRef<str>>(&self, name: T) -> Option<Ptr<F>> {
        let ptr = self.str_store.0.get(name)?;
        Some(Ptr::index(ExprTag::Str, ptr.to_usize()))
    }

    pub fn get_sym(&self, sym: &Sym) -> Option<Ptr<F>> {
        let name = sym.full_sym_name();
        let ptr = self.sym_store.0.get(name)?;
        Some(Ptr::index(ExprTag::Sym, ptr.to_usize()))
    }

    pub fn intern_fun(&mut self, arg: Ptr<F>, body: Ptr<F>, closed_env: Ptr<F>) -> Ptr<F> {
        // TODO: closed_env must be an env
        assert!(matches!(arg.tag, ExprTag::Sym), "ARG must be a symbol");
        let (p, inserted) = self.fun_store.insert_full((arg, body, closed_env));
        let ptr = Ptr::index(ExprTag::Fun, p);
        if inserted {
            self.dehydrated.push(ptr);
        }
        ptr
    }

    pub fn intern_thunk(&mut self, thunk: Thunk<F>) -> Ptr<F> {
        let (p, inserted) = self.thunk_store.insert_full(thunk);
        let ptr = Ptr::index(ExprTag::Thunk, p);
        if inserted {
            self.dehydrated.push(ptr);
        }
        ptr
    }

    pub fn mark_dehydrated_cont(&mut self, p: ContPtr<F>) -> ContPtr<F> {
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

    pub fn fetch_scalar(&self, scalar_ptr: &ZExprPtr<F>) -> Option<Ptr<F>> {
        self.z_expr_ptr_map.get(scalar_ptr).map(|p| *p)
    }

    pub fn fetch_scalar_cont(&self, scalar_ptr: &ZContPtr<F>) -> Option<ContPtr<F>> {
        self.z_cont_ptr_map.get(scalar_ptr).map(|p| *p)
    }

    pub fn fetch_maybe_sym(&self, ptr: &Ptr<F>) -> Option<Sym> {
        if matches!(ptr.tag, ExprTag::Sym) {
            self.fetch_sym(ptr)
        } else {
            None
        }
    }

    pub fn fetch_sym(&self, ptr: &Ptr<F>) -> Option<Sym> {
        debug_assert!(matches!(
            ptr.tag,
            ExprTag::Sym | ExprTag::Key | ExprTag::Nil
        ));

        if ptr.raw.is_opaque() {
            let is_keyword = ptr.tag == ExprTag::Key;

            return Some(Sym::new_opaque(is_keyword));
        }

        if ptr.tag == ExprTag::Nil {
            return Some(Sym::new(".LURK.NIL".into()));
        };
        self.sym_store
            .0
            .resolve(SymbolUsize::try_from_usize(ptr.raw.idx()?).unwrap())
            .map(|s| match ptr.tag {
                ExprTag::Sym => Sym::new_sym(s.into()),
                ExprTag::Key => Sym::new_key(s.into()),
                _ => unreachable!(),
            })
    }

    pub fn fetch_str(&self, ptr: &Ptr<F>) -> Option<&str> {
        debug_assert!(matches!(ptr.tag, ExprTag::Str));
        let symbol = SymbolUsize::try_from_usize(ptr.raw.idx()?)?;
        self.str_store.0.resolve(symbol)
    }

    pub fn fetch_char(&self, ptr: &Ptr<F>) -> Option<char> {
        debug_assert!(matches!(ptr.tag, ExprTag::Char));
        char::from_u32(ptr.raw.idx()? as u32)
    }

    pub fn fetch_fun(&self, ptr: &Ptr<F>) -> Option<&(Ptr<F>, Ptr<F>, Ptr<F>)> {
        debug_assert!(matches!(ptr.tag, ExprTag::Fun));
        if ptr.raw.is_opaque() {
            None
            // Some(&self.opaque_fun)
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

    fn fetch_thunk(&self, ptr: &Ptr<F>) -> Option<&Thunk<F>> {
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

    pub fn fetch(&self, ptr: &Ptr<F>) -> Option<Expression<'_, F>> {
        if ptr.is_opaque() {
            return Some(Expression::Opaque(*ptr));
        }
        match ptr.tag {
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
        use ContTag::*;
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
        }
    }

    /// Folds over a vector of chars, from right to left, hashing and caching
    /// the hashes of string tails formed by such sequences. For example, when
    /// hashing ['a', 'b', 'c'], it will also store the hashes of ['b', 'c'],
    /// ['c'] and [].
    ///
    /// While computing this right folded hashes, `put_z_chars` tries to find
    /// previously computed hashes so it can stop in case of cache hits.
    pub fn put_z_chars(
        &self,
        chars: Vec<char>,
        z_store: Option<Rc<RefCell<ZStore<F>>>>,
    ) -> (ZExprPtr<F>, ZExpr<F>) {
        let mut ptr: ZExprPtr<F>;
        let mut expr: ZExpr<F>;
        let mut chars_rev = chars;
        chars_rev.reverse();
        let mut heads_acc: Vec<char> = vec![];
        loop {
            if chars_rev.is_empty() {
                expr = ZExpr::StrNil;
                ptr = expr.z_ptr(&self.poseidon_cache);
                break;
            }
            heads_acc.push(chars_rev.pop().unwrap());
            match self.vec_char_cache.get(&chars_rev) {
                Some(cache) => {
                    let (ptr_cache, expr_cache) = &*cache;
                    ptr = ptr_cache.clone();
                    expr = expr_cache.clone();
                    break;
                }
                None => continue,
            }
        }
        while let Some(c) = heads_acc.pop() {
            expr = ZExpr::StrCons(ZPtr(ExprTag::Char, F::from_char(c)), ptr.clone());
            ptr = expr.z_ptr(&self.poseidon_cache);
            if let Some(z_store) = z_store.clone() {
                z_store
                    .borrow_mut()
                    .expr_map
                    .insert(ptr.clone(), Some(expr.clone()));
            };
            chars_rev.push(c);
            self.vec_char_cache
                .insert(chars_rev.clone(), Box::new((ptr.clone(), expr.clone())));
        }
        (ptr, expr)
    }

    /// Similar to `put_z_chars`, but deals with strings instead of chars and
    /// computes symbol hashes instead of string hashes.
    pub fn put_z_strs(
        &self,
        strs: Vec<String>,
        z_store: Option<Rc<RefCell<ZStore<F>>>>,
    ) -> (ZExprPtr<F>, ZExpr<F>) {
        let mut ptr: ZExprPtr<F>;
        let mut expr: ZExpr<F>;
        let mut strs_rev = strs;
        strs_rev.reverse();
        let mut heads_acc: Vec<String> = vec![];
        loop {
            if strs_rev.is_empty() {
                expr = ZExpr::SymNil;
                ptr = expr.z_ptr(&self.poseidon_cache);
                break;
            }
            heads_acc.push(strs_rev.pop().unwrap());
            match self.vec_str_cache.get(&strs_rev) {
                Some(cache) => {
                    let (ptr_cache, expr_cache) = &*cache;
                    ptr = ptr_cache.clone();
                    expr = expr_cache.clone();
                    break;
                }
                None => continue,
            }
        }
        while let Some(s) = heads_acc.pop() {
            let (name_ptr, _) = self.put_z_chars(s.chars().collect(), z_store.clone());
            expr = ZExpr::SymCons(name_ptr, ptr.clone());
            ptr = expr.z_ptr(&self.poseidon_cache);
            if let Some(z_store) = z_store.clone() {
                z_store
                    .borrow_mut()
                    .expr_map
                    .insert(ptr.clone(), Some(expr.clone()));
            };
            strs_rev.push(s);
            self.vec_str_cache
                .insert(strs_rev.clone(), Box::new((ptr.clone(), expr.clone())));
        }
        (ptr, expr)
    }

    #[inline]
    pub fn put_z_str(
        &self,
        s: String,
        z_store: Option<Rc<RefCell<ZStore<F>>>>,
    ) -> (ZExprPtr<F>, ZExpr<F>) {
        self.put_z_chars(s.chars().collect_vec(), z_store)
    }

    #[inline]
    pub fn put_z_sym(
        &self,
        s: Sym,
        z_store: Option<Rc<RefCell<ZStore<F>>>>,
    ) -> (ZExprPtr<F>, ZExpr<F>) {
        self.put_z_strs(s.path().to_vec(), z_store)
    }

    pub fn get_z_cont(
        &self,
        ptr: &ContPtr<F>,
        z_store: Option<Rc<RefCell<ZStore<F>>>>,
    ) -> Result<(ZContPtr<F>, Option<ZCont<F>>), Error> {
        if let Some(idx) = ptr.raw.opaque_idx() {
            let z_ptr = self
                .opaque_cont_ptrs
                .get_index(idx)
                .ok_or(Error(format!("get_z_expr unknown opaque")))?;
            match self.z_cont_ptr_map.get(z_ptr) {
                // TODO: cycle-detection needed either here or on opaque ptr creation
                Some(p) => self.get_z_cont(&p, z_store.clone()),
                None => Ok((*z_ptr, None)),
            }
        } else {
            let (z_ptr, z_cont) = match self.fetch_cont(ptr) {
                Some(Continuation::Outermost) => {
                    let z_cont = ZCont::<F>::Outermost;
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                Some(Continuation::Call0 { saved_env, continuation }) => {
                    let (z_env_ptr, _) = self.get_z_expr(&saved_env, z_store.clone())?;
                    let (z_cont_ptr, _) = self.get_z_cont(&continuation, z_store.clone())?;
                    let z_cont = ZCont::<F>::Call0 { saved_env: z_env_ptr, continuation: z_cont_ptr };
                    let z_ptr = z_cont.z_ptr(&self.poseidon_cache);
                    (z_ptr, Some(z_cont))
                }
                _ => todo!(),
            };

            if let Some(z_store) = z_store {
                z_store
                    .borrow_mut()
                    .cont_map.insert(z_ptr, z_cont.clone());
            };
            Ok((z_ptr, z_cont))
        }
    }

    pub fn get_z_expr(
        &self,
        ptr: &Ptr<F>,
        z_store: Option<Rc<RefCell<ZStore<F>>>>,
    ) -> Result<(ZExprPtr<F>, Option<ZExpr<F>>), Error> {
        if let Some(idx) = ptr.raw.opaque_idx() {
            let z_ptr = self
                .opaque_ptrs
                .get_index(idx)
                .ok_or(Error(format!("get_z_expr unknown opaque")))?;
            match self.z_expr_ptr_map.get(z_ptr) {
                None => Ok((*z_ptr, None)),
                // TODO: cycle-detection needed either here or on opaque ptr creation
                Some(p) => self.get_z_expr(&p, z_store.clone()),
            }
        } else {
            let (z_ptr, z_expr) = match self.fetch(ptr) {
                Some(Expression::Nil) => (ZExpr::Nil.z_ptr(&self.poseidon_cache), Some(ZExpr::Nil)),
                Some(Expression::Cons(car, cdr)) => {
                    let (z_car, _) = self.get_z_expr(&car, z_store.clone())?;
                    let (z_cdr, _) = self.get_z_expr(&cdr, z_store.clone())?;
                    let z_expr = ZExpr::Cons(z_car, z_cdr);
                    (z_expr.z_ptr(&self.poseidon_cache), Some(z_expr))
                }
                Some(Expression::Comm(secret, payload)) => {
                    let (z_payload, _) = self.get_z_expr(&payload, z_store.clone())?;
                    let z_expr = ZExpr::Comm(secret, z_payload);
                    (z_expr.z_ptr(&self.poseidon_cache), Some(z_expr))
                }
                Some(Expression::Fun(args, env, body)) => {
                    let (z_args, _) = self.get_z_expr(&args, z_store.clone())?;
                    let (z_env, _) = self.get_z_expr(&env, z_store.clone())?;
                    let (z_body, _) = self.get_z_expr(&body, z_store.clone())?;
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
                    let (z_value, _) = self.get_z_expr(&value, z_store.clone())?;
                    let (z_cont, _) = self.get_z_cont(&continuation, z_store.clone())?;
                    let z_expr = ZExpr::Thunk(z_value, z_cont);
                    (z_expr.z_ptr(&self.poseidon_cache), Some(z_expr))
                }
                None => {
                    let (z_ptr, _) = self.get_z_expr(&ptr, z_store.clone())?;
                    (z_ptr, None)
                }
                Some(Expression::Opaque(ptr)) => {
                    let (z_ptr, _) = self.get_z_expr(&ptr, z_store.clone())?;
                    (z_ptr, None)
                }
                Some(Expression::Char(c)) => {
                    let z_expr = ZExpr::Char(c);
                    (z_expr.z_ptr(&self.poseidon_cache), Some(z_expr))
                }
                Some(Expression::UInt(u)) => {
                    let z_expr = ZExpr::Uint(u);
                    (z_expr.z_ptr(&self.poseidon_cache), Some(z_expr))
                }
                Some(Expression::Str(s)) => {
                    let (ptr, expr) = self.put_z_str(s.to_string(), z_store.clone());
                    (ptr, Some(expr))
                }
                Some(Expression::Sym(s)) => {
                    let (ptr, expr) = self.put_z_sym(s, z_store.clone());
                    (ptr, Some(expr))
                }
            };
            // TODO
            if let Some(z_store) = z_store {
                z_store
                    .borrow_mut()
                    .expr_map.insert(z_ptr, z_expr.clone());
            };
            Ok((z_ptr, z_expr))
        }
    }
    
    pub fn to_z_expr(&self, ptr: &Ptr<F>) -> Option<ZExpr<F>> {
        self.get_z_expr(ptr, None).ok()?.1
    }

    pub fn hash_expr(&self, ptr: &Ptr<F>) -> Option<ZExprPtr<F>> {
        self.get_z_expr(ptr, None).ok().map(|x| x.0)
    }

    pub fn to_z_cont(&self, ptr: &ContPtr<F>) -> Option<ZCont<F>> {
        self.get_z_cont(ptr, None).ok()?.1
    }

    pub fn hash_cont(&self, ptr: &ContPtr<F>) -> Option<ZContPtr<F>> {
        self.get_z_cont(ptr, None).ok().map(|x| x.0)
    }

    pub fn hash_string(&mut self, s: &str) -> ZExprPtr<F> {
        self.put_z_str(s.to_string(), None).0
    }

    pub fn hash_symbol(&mut self, s: Sym) -> ZExprPtr<F> {
        self.put_z_sym(s, None).0
    }

    pub fn from_z_store(z_store: &ZStore<F>) -> Option<Self> {
        todo!()
    }
    pub fn z_store_with_expr(&self, expr: &Ptr<F>) -> (ZStore<F>, ZExprPtr<F>) {
        todo!()
    }

    pub fn intern_z_expr(
        &mut self,
        ptr: ZExprPtr<F>,
        scalar_store: &ZStore<F>,
    ) -> Option<ContPtr<F>> {
        todo!()
    }

    pub fn intern_z_cont(
        &mut self,
        ptr: ZContPtr<F>,
        scalar_store: &ZStore<F>,
    ) -> Option<ContPtr<F>> {
        todo!()
    }

    /// Mutable version of car_cdr to handle Str. `(cdr str)` may return a new str (the tail), which must be allocated.
    pub fn car_cdr_mut(&mut self, ptr: &Ptr<F>) -> Result<(Ptr<F>, Ptr<F>), Error> {
        match ptr.tag {
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
        match ptr.tag {
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

    pub fn get_opaque_ptr(&self, ptr: Ptr<F>) -> Option<ZExprPtr<F>> {
        let s = self.opaque_ptrs.get_index(ptr.raw.opaque_idx()?)?;
        Some(*s)
    }

    // An opaque Ptr is one for which we have the hash, but not the preimages.
    // So we cannot open or traverse the enclosed data, but we can manipulate
    // it atomically and include it in containing structures, etc.
    pub fn new_opaque_ptr(&mut self) -> Ptr<F> {
        // TODO: May need new tag for this.
        // Meanwhile, it is illegal to try to dereference/follow an opaque PTR.
        // So any tag and RawPtr are okay.
        let z_ptr = ZExpr::Nil.z_ptr(&self.poseidon_cache);
        let (i, _) = self.opaque_ptrs.insert_full(z_ptr);
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

    pub fn cons_eq(&self, a: &Ptr<F>, b: &Ptr<F>) -> bool {
        assert_eq!(ExprTag::Cons, a.tag);
        assert_eq!(ExprTag::Cons, b.tag);

        let a_opaque = a.is_opaque();
        let b_opaque = b.is_opaque();

        if !a_opaque && !b_opaque {
            return a == b;
        }
        self.hash_expr(a) == self.hash_expr(b)
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

    pub fn intern_sym_and_ancestors(&mut self, sym: &Sym) -> Option<Ptr<F>> {
        if let Some(s) = sym.parent() {
            if !s.is_root() {
                self.intern_sym_and_ancestors(&s);
            }
        };
        Some(self.intern_sym(sym))
    }

    /// The only places that `ZPtr`s for `Ptr`s should be created, to
    /// ensure that they are cached properly
    fn create_z_ptr(&self, ptr: Ptr<F>, hash: F) -> ZExprPtr<F> {
        let z_ptr = ZPtr(ptr.tag, hash);
        self.z_expr_ptr_map.insert(z_ptr, Box::new(ptr));
        z_ptr
    }

    pub fn intern_z_expr_ptr(&mut self, z_ptr: ZExprPtr<F>, z_store: &ZStore<F>) -> Option<Ptr<F>> {
        if let Some(ptr) = self.fetch_scalar(&z_ptr) {
            Some(ptr)
        } else {
            use ZExpr::*;
            match (z_ptr.tag(), z_store.get_expr(&z_ptr)) {
                (ExprTag::Nil, Some(Nil)) => {
                    let ptr = self.intern_nil();
                    self.create_z_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Cons, Some(Cons(car, cdr))) => {
                    let car = self.intern_z_expr_ptr(car, z_store)?;
                    let cdr = self.intern_z_expr_ptr(cdr, z_store)?;
                    let ptr = self.intern_cons(car, cdr);
                    self.create_z_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Comm, Some(Comm(secret, payload))) => {
                    let payload = self.intern_z_expr_ptr(payload, z_store)?;
                    let ptr = self.intern_comm(secret, payload);
                    self.create_z_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Str, Some(StrNil)) => {
                    let ptr = self.intern_strnil();
                    self.create_z_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Str, Some(StrCons(strcar, strcdr))) => {
                    let strcar = self.intern_z_expr_ptr(strcar, z_store)?;
                    let strcdr = self.intern_z_expr_ptr(strcdr, z_store)?;
                    let ptr = self.intern_strcons(strcar, strcdr);
                    self.create_z_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Str, Some(SymNil)) => {
                    let ptr = self.intern_symnil(false);
                    self.create_z_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Sym, Some(SymCons(symcar, symcdr))) => {
                    let symcar = self.intern_z_expr_ptr(symcar, z_store)?;
                    let symcdr = self.intern_z_expr_ptr(symcdr, z_store)?;
                    let ptr = self.intern_symcons(symcar, symcdr, false);
                    self.create_z_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Key, Some(SymNil)) => {
                    let ptr = self.intern_symnil(true);
                    self.create_z_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Key, Some(SymCons(keycar, keycdr))) => {
                    let keycar = self.intern_z_expr_ptr(keycar, z_store)?;
                    let keycdr = self.intern_z_expr_ptr(keycdr, z_store)?;
                    let ptr = self.intern_symcons(keycar, keycdr, true);
                    self.create_z_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Num, Some(Num(x))) => {
                    let ptr = self.intern_num(crate::Num::Scalar(x));
                    self.create_z_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (ExprTag::Char, Some(Char(x))) => Some(x.into()),
                (ExprTag::Thunk, Some(Thunk(value, continuation))) => {
                    let value = self.intern_z_expr_ptr(value, z_store)?;
                    let continuation = self.intern_z_cont_ptr(continuation, z_store)?;
                    let ptr = self.intern_thunk(expr::Thunk {
                        value,
                        continuation,
                    });
                    self.create_z_ptr(ptr, *z_ptr.value());
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
                    let arg = self.intern_z_expr_ptr(arg, z_store)?;
                    let body = self.intern_z_expr_ptr(body, z_store)?;
                    let env = self.intern_z_expr_ptr(closed_env, z_store)?;
                    let ptr = self.intern_fun(arg, body, env);
                    self.create_z_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                (tag, None) => {
                    let ptr = self.intern_maybe_opaque(tag, z_ptr.1);
                    self.create_z_ptr(ptr, *z_ptr.value());
                    Some(ptr)
                }
                _ => None,
            }
        }
    }

    pub fn intern_z_cont_ptr(
        &mut self,
        z_ptr: ZContPtr<F>,
        z_store: &ZStore<F>,
    ) -> Option<ContPtr<F>> {
        use ZCont::*;
        let tag: ContTag = z_ptr.tag();

        if let Some(cont) = z_store.get_cont(&z_ptr) {
            let continuation = match cont {
                Outermost => Continuation::Outermost,
                Dummy => Continuation::Dummy,
                Terminal => Continuation::Terminal,
                Call0 {
                    saved_env,
                    continuation,
                } => Continuation::Call0 {
                    saved_env: self.intern_z_expr_ptr(saved_env, z_store)?,
                    continuation: self.intern_z_cont_ptr(continuation, z_store)?,
                },
                Call {
                    unevaled_arg,
                    saved_env,
                    continuation,
                } => Continuation::Call {
                    unevaled_arg: self.intern_z_expr_ptr(unevaled_arg, z_store)?,
                    saved_env: self.intern_z_expr_ptr(saved_env, z_store)?,
                    continuation: self.intern_z_cont_ptr(continuation, z_store)?,
                },
                Call2 {
                    function,
                    saved_env,
                    continuation,
                } => Continuation::Call2 {
                    function: self.intern_z_expr_ptr(function, z_store)?,
                    saved_env: self.intern_z_expr_ptr(saved_env, z_store)?,
                    continuation: self.intern_z_cont_ptr(continuation, z_store)?,
                },
                Tail {
                    saved_env,
                    continuation,
                } => Continuation::Tail {
                    saved_env: self.intern_z_expr_ptr(saved_env, z_store)?,
                    continuation: self.intern_z_cont_ptr(continuation, z_store)?,
                },
                Error => Continuation::Error,
                Lookup {
                    saved_env,
                    continuation,
                } => Continuation::Lookup {
                    saved_env: self.intern_z_expr_ptr(saved_env, z_store)?,
                    continuation: self.intern_z_cont_ptr(continuation, z_store)?,
                },
                Unop {
                    operator,
                    continuation,
                } => Continuation::Unop {
                    operator: operator,
                    continuation: self.intern_z_cont_ptr(continuation, z_store)?,
                },
                Binop {
                    operator,
                    saved_env,
                    unevaled_args,
                    continuation,
                } => Continuation::Binop {
                    operator: operator,
                    saved_env: self.intern_z_expr_ptr(saved_env, z_store)?,
                    unevaled_args: self.intern_z_expr_ptr(unevaled_args, z_store)?,
                    continuation: self.intern_z_cont_ptr(continuation, z_store)?,
                },
                Binop2 {
                    operator,
                    evaled_arg,
                    continuation,
                } => Continuation::Binop2 {
                    operator: operator,
                    evaled_arg: self.intern_z_expr_ptr(evaled_arg, z_store)?,
                    continuation: self.intern_z_cont_ptr(continuation, z_store)?,
                },
                If {
                    unevaled_args,
                    continuation,
                } => Continuation::If {
                    unevaled_args: self.intern_z_expr_ptr(unevaled_args, z_store)?,
                    continuation: self.intern_z_cont_ptr(continuation, z_store)?,
                },
                Let {
                    var,
                    body,
                    saved_env,
                    continuation,
                } => Continuation::Let {
                    var: self.intern_z_expr_ptr(var, z_store)?,
                    body: self.intern_z_expr_ptr(body, z_store)?,
                    saved_env: self.intern_z_expr_ptr(saved_env, z_store)?,
                    continuation: self.intern_z_cont_ptr(continuation, z_store)?,
                },
                LetRec {
                    var,
                    body,
                    saved_env,
                    continuation,
                } => Continuation::LetRec {
                    var: self.intern_z_expr_ptr(var, z_store)?,
                    body: self.intern_z_expr_ptr(body, z_store)?,
                    saved_env: self.intern_z_expr_ptr(saved_env, z_store)?,
                    continuation: self.intern_z_cont_ptr(continuation, z_store)?,
                },
                Emit { continuation } => Continuation::Emit {
                    continuation: self.intern_z_cont_ptr(continuation, z_store)?,
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
pub struct ConstantPtrs<F: LurkField>(Option<ZExprPtr<F>>, Ptr<F>);

impl<F: LurkField> ConstantPtrs<F> {
    pub fn value(&self) -> F {
        *self.scalar_ptr().value()
    }
    pub fn scalar_ptr(&self) -> ZExprPtr<F> {
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
        let hash_sym = |name: &str| {
            let ptr = store.get_lurk_sym(name, true).unwrap();
            let maybe_z_ptr = store.hash_expr(&ptr);
            ConstantPtrs(maybe_z_ptr, ptr)
        };

        let t = hash_sym("t");
        let nil = ConstantPtrs(
            Some(ZExpr::Nil.z_ptr(&store.poseidon_cache)),
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

impl<F: LurkField> ZStore<F> {
    pub fn to_store(&mut self) -> Store<F> {
        let mut store = Store::new();

        for ptr in self.expr_map.keys() {
            store.intern_z_expr_ptr(*ptr, self);
        }
        for ptr in self.cont_map.keys() {
            store.intern_z_cont_ptr(*ptr, self);
        }
        store
    }
}

#[cfg(test)]
pub mod test {

    use crate::eval::{
        empty_sym_env,
        lang::{Coproc, Lang},
        Evaluator,
    };
    use crate::num;
    use crate::writer::Write;

    #[cfg(not(target_arch = "wasm32"))]
    use proptest::prelude::*;

    use blstrs::Scalar as Fr;

    use super::*;

    use libipld::serde::from_ipld;
    use libipld::serde::to_ipld;
    use libipld::Ipld;

    proptest! {
      #[test]
      fn test_scalar_ptr_ipld(x in any::<ZExprPtr<Fr>>())  {
        let to_ipld = to_ipld(x).unwrap();
        let from_ipld = from_ipld(to_ipld).unwrap();
        assert_eq!(x, from_ipld);
      }

      #[test]
      fn prop_scalar_cont_ptr_ipld(x in any::<ZContPtr<Fr>>()) {
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
        let lang: Lang<Fr, Coproc<Fr>> = Lang::new();
        {
            let comparison_expr = store.list(&[eq, fun, opaque_fun]);
            println!("comparison_expr: {}", comparison_expr.fmt_to_string(&store));
            let (result, _, _) =
                Evaluator::new(comparison_expr, empty_env, &mut store, limit, &lang)
                    .eval()
                    .unwrap();
            assert_eq!(t, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, fun2, opaque_fun]);
            println!("comparison_expr: {}", comparison_expr.fmt_to_string(&store));
            let (result, _, _) =
                Evaluator::new(comparison_expr, empty_env, &mut store, limit, &lang)
                    .eval()
                    .unwrap();
            assert_eq!(nil, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, fun2, opaque_fun2]);
            let (result, _, _) =
                Evaluator::new(comparison_expr, empty_env, &mut store, limit, &lang)
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
            let (result, _, _) =
                Evaluator::new(comparison_expr, empty_env, &mut store, limit, &lang)
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
        assert_eq!(
            Sym::new_opaque(false),
            store.fetch_sym(&other_opaque_sym3).unwrap()
        );

        let lang = Lang::<Fr, Coproc<Fr>>::new();
        {
            let comparison_expr = store.list(&[eq, qsym, qsym_opaque]);
            let (result, _, _) =
                Evaluator::new(comparison_expr, empty_env, &mut store, limit, &lang)
                    .eval()
                    .unwrap();
            assert_eq!(t, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, qsym2, qsym_opaque]);
            let (result, _, _) =
                Evaluator::new(comparison_expr, empty_env, &mut store, limit, &lang)
                    .eval()
                    .unwrap();
            assert_eq!(nil, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, qsym2, qsym_opaque2]);
            let (result, _, _) =
                Evaluator::new(comparison_expr, empty_env, &mut store, limit, &lang)
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
            let lang: Lang<Fr, Coproc<Fr>> = Lang::new();
            let (result, _, _) =
                Evaluator::new(comparison_expr, empty_env, &mut store, limit, &lang)
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
        let lang = Lang::<Fr, Coproc<Fr>>::new();

        assert_eq!(
            format!("<Opaque Cons {}>", num.fmt_to_string(&store)),
            opaque_cons.fmt_to_string(&store)
        );

        {
            let comparison_expr = store.list(&[eq, qcons, qcons_opaque]);
            // FIXME: need to implement Write for opaque data.
            let (result, _, _) =
                Evaluator::new(comparison_expr, empty_env, &mut store, limit, &lang)
                    .eval()
                    .unwrap();
            assert_eq!(t, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, qcons2, qcons_opaque]);
            let (result, _, _) =
                Evaluator::new(comparison_expr, empty_env, &mut store, limit, &lang)
                    .eval()
                    .unwrap();
            assert_eq!(nil, result.expr);
        }
        {
            let comparison_expr = store.list(&[eq, qcons2, qcons_opaque2]);
            let (result, _, _) =
                Evaluator::new(comparison_expr, empty_env, &mut store, limit, &lang)
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

            let lang: Lang<Fr, Coproc<Fr>> = Lang::new();
            {
                let (result, _, _) =
                    Evaluator::new(comparison_expr, empty_env, &mut store, limit, &lang)
                        .eval()
                        .unwrap();
                assert_eq!(t, result.expr);
            }
            {
                let (result, _, _) =
                    Evaluator::new(comparison_expr2, empty_env, &mut store, limit, &lang)
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

        let sym_ptr = s.hash_expr(&sym).unwrap();
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
        let hash = s.hash_expr(&sym);
        dbg!(&sym1, &sss, &hash);

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

        // Unless the cache is hydrated, the inner destructuring will not map the ZExprPtr to corresponding Ptr.
        if hydrate {
            s.hydrate_scalar_cache();
        };

        let str2_scalar_ptr = s.hash_expr(&str2).unwrap();

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

        // Unless the cache is hydrated, the inner destructuring will not map the ZExprPtr to corresponding Ptr.
        if hydrate {
            s.hydrate_scalar_cache();
        };

        let str_scalar_ptr = s.hash_expr(&str).unwrap();

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
