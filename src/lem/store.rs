use anyhow::{bail, Result};
use arc_swap::ArcSwap;
use elsa::sync::{FrozenMap, FrozenVec};
use elsa::sync_index_set::FrozenIndexSet;
use indexmap::IndexSet;
use nom::{sequence::preceded, Parser};
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use std::{cell::RefCell, rc::Rc, sync::Arc};

use crate::{
    field::{FWrap, LurkField},
    hash::PoseidonCache,
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
    uint::UInt,
};

use super::pointers::{Ptr, ZPtr};

/// The `Store` is a crucial part of Lurk's implementation and tries to be a
/// vesatile data structure for many parts of Lurk's data pipeline.
///
/// It holds Lurk data structured as trees of `Ptr`s. When a `Ptr` has children,
/// we store them in the `IndexSet`s available: `tuple2`, `tuple3` or `tuple4`.
/// These data structures speed up LEM interpretation because lookups by indices
/// are fast.
///
/// The `Store` provides an infra to speed up interning strings and symbols. This
/// data is saved in `string_ptr_cache` and `symbol_ptr_cache`.
///
/// There's also a process that we call "hydration", in which we use Poseidon
/// hashes to compute the (stable) hash of the children of a pointer. These hashes
/// are necessary when we want to create Lurk proofs because the circuit consumes
/// elements of the `LurkField`, not (unstable) indices of `IndexSet`s.
///
/// Lastly, we have a `HashMap` to hold committed data, which can be retrieved by
/// the resulting commitment hash.
#[derive(Default, Debug)]
pub struct Store<F: LurkField> {
    tuple2: FrozenIndexSet<Box<(Ptr<F>, Ptr<F>)>>,
    tuple3: FrozenIndexSet<Box<(Ptr<F>, Ptr<F>, Ptr<F>)>>,
    tuple4: FrozenIndexSet<Box<(Ptr<F>, Ptr<F>, Ptr<F>, Ptr<F>)>>,

    string_ptr_cache: FrozenMap<String, Box<Ptr<F>>>,
    symbol_ptr_cache: FrozenMap<Symbol, Box<Ptr<F>>>,

    ptr_string_cache: FrozenMap<Ptr<F>, String>,
    ptr_symbol_cache: FrozenMap<Ptr<F>, Box<Symbol>>,

    pub poseidon_cache: PoseidonCache<F>,

    dehydrated: ArcSwap<FrozenVec<Box<Ptr<F>>>>,
    z_cache: FrozenMap<Ptr<F>, Box<ZPtr<F>>>,

    comms: FrozenMap<FWrap<F>, Box<(F, Ptr<F>)>>, // hash -> (secret, src)
}

impl<F: LurkField> Store<F> {
    /// Creates a `Ptr` that's a parent of two children
    pub fn intern_2_ptrs(&self, tag: Tag, a: Ptr<F>, b: Ptr<F>) -> Ptr<F> {
        let (idx, inserted) = self.tuple2.insert_probe(Box::new((a, b)));
        let ptr = Ptr::Tuple2(tag, idx);
        if inserted {
            // this is for `hydrate_z_cache`
            self.dehydrated.load().push(Box::new(ptr));
        }
        ptr
    }

    /// Similar to `intern_2_ptrs` but doesn't add the resulting pointer to
    /// `dehydrated`. This function is used when converting a `ZStore` to a
    /// `Store`.
    pub fn intern_2_ptrs_hydrated(&self, tag: Tag, a: Ptr<F>, b: Ptr<F>, z: ZPtr<F>) -> Ptr<F> {
        let ptr = Ptr::Tuple2(tag, self.tuple2.insert_probe(Box::new((a, b))).0);
        self.z_cache.insert(ptr, Box::new(z));
        ptr
    }

    /// Creates a `Ptr` that's a parent of three children
    pub fn intern_3_ptrs(&self, tag: Tag, a: Ptr<F>, b: Ptr<F>, c: Ptr<F>) -> Ptr<F> {
        let (idx, inserted) = self.tuple3.insert_probe(Box::new((a, b, c)));
        let ptr = Ptr::Tuple3(tag, idx);
        if inserted {
            // this is for `hydrate_z_cache`
            self.dehydrated.load().push(Box::new(ptr));
        }
        ptr
    }

    /// Similar to `intern_3_ptrs` but doesn't add the resulting pointer to
    /// `dehydrated`. This function is used when converting a `ZStore` to a
    /// `Store`.
    pub fn intern_3_ptrs_hydrated(
        &self,
        tag: Tag,
        a: Ptr<F>,
        b: Ptr<F>,
        c: Ptr<F>,
        z: ZPtr<F>,
    ) -> Ptr<F> {
        let ptr = Ptr::Tuple3(tag, self.tuple3.insert_probe(Box::new((a, b, c))).0);
        self.z_cache.insert(ptr, Box::new(z));
        ptr
    }

    /// Creates a `Ptr` that's a parent of four children
    pub fn intern_4_ptrs(&self, tag: Tag, a: Ptr<F>, b: Ptr<F>, c: Ptr<F>, d: Ptr<F>) -> Ptr<F> {
        let (idx, inserted) = self.tuple4.insert_probe(Box::new((a, b, c, d)));
        let ptr = Ptr::Tuple4(tag, idx);
        if inserted {
            // this is for `hydrate_z_cache`
            self.dehydrated.load().push(Box::new(ptr));
        }
        ptr
    }

    /// Similar to `intern_4_ptrs` but doesn't add the resulting pointer to
    /// `dehydrated`. This function is used when converting a `ZStore` to a
    /// `Store`.
    pub fn intern_4_ptrs_hydrated(
        &self,
        tag: Tag,
        a: Ptr<F>,
        b: Ptr<F>,
        c: Ptr<F>,
        d: Ptr<F>,
        z: ZPtr<F>,
    ) -> Ptr<F> {
        let ptr = Ptr::Tuple4(tag, self.tuple4.insert_probe(Box::new((a, b, c, d))).0);
        self.z_cache.insert(ptr, Box::new(z));
        ptr
    }

    #[inline]
    pub fn fetch_2_ptrs(&self, idx: usize) -> Option<&(Ptr<F>, Ptr<F>)> {
        self.tuple2.get_index(idx)
    }

    #[inline]
    pub fn fetch_3_ptrs(&self, idx: usize) -> Option<&(Ptr<F>, Ptr<F>, Ptr<F>)> {
        self.tuple3.get_index(idx)
    }

    #[inline]
    pub fn fetch_4_ptrs(&self, idx: usize) -> Option<&(Ptr<F>, Ptr<F>, Ptr<F>, Ptr<F>)> {
        self.tuple4.get_index(idx)
    }

    pub fn intern_string(&self, s: &str) -> Ptr<F> {
        if let Some(ptr) = self.string_ptr_cache.get(s) {
            *ptr
        } else {
            let ptr = s.chars().rev().fold(Ptr::null(Tag::Expr(Str)), |acc, c| {
                self.intern_2_ptrs(Tag::Expr(Str), Ptr::char(c), acc)
            });
            self.string_ptr_cache.insert(s.to_string(), Box::new(ptr));
            self.ptr_string_cache.insert(ptr, s.to_string());
            ptr
        }
    }

    pub fn fetch_string(&self, ptr: &Ptr<F>) -> Option<String> {
        if let Some(str) = self.ptr_string_cache.get(ptr) {
            Some(str.to_string())
        } else {
            let mut string = String::new();
            let mut ptr = *ptr;
            loop {
                match ptr {
                    Ptr::Atom(Tag::Expr(Str), f) => {
                        if f == F::ZERO {
                            self.ptr_string_cache.insert(ptr, string.clone());
                            return Some(string);
                        } else {
                            return None;
                        }
                    }
                    Ptr::Tuple2(Tag::Expr(Str), idx) => {
                        let (car, cdr) = self.fetch_2_ptrs(idx)?;
                        match car {
                            Ptr::Atom(Tag::Expr(Char), c) => {
                                string.push(c.to_char().expect("char pointers are well formed"));
                                ptr = *cdr
                            }
                            _ => return None,
                        }
                    }
                    _ => return None,
                }
            }
        }
    }

    pub fn intern_symbol_path(&self, path: &[String]) -> Ptr<F> {
        path.iter().fold(Ptr::null(Tag::Expr(Sym)), |acc, s| {
            let s_ptr = self.intern_string(s);
            self.intern_2_ptrs(Tag::Expr(Sym), s_ptr, acc)
        })
    }

    pub fn intern_symbol(&self, sym: &Symbol) -> Ptr<F> {
        if let Some(ptr) = self.symbol_ptr_cache.get(sym) {
            *ptr
        } else {
            let path_ptr = self.intern_symbol_path(sym.path());
            let sym_ptr = if sym == &lurk_sym("nil") {
                path_ptr.cast(Tag::Expr(Nil))
            } else if sym.is_keyword() {
                path_ptr.cast(Tag::Expr(Key))
            } else {
                path_ptr
            };
            self.symbol_ptr_cache.insert(sym.clone(), Box::new(sym_ptr));
            self.ptr_symbol_cache.insert(sym_ptr, Box::new(sym.clone()));
            sym_ptr
        }
    }

    pub fn fetch_symbol_path(&self, mut idx: usize) -> Option<Vec<String>> {
        let mut path = vec![];
        loop {
            let (car, cdr) = self.fetch_2_ptrs(idx)?;
            let string = self.fetch_string(car)?;
            path.push(string);
            match cdr {
                Ptr::Atom(Tag::Expr(Sym), f) => {
                    if f == &F::ZERO {
                        path.reverse();
                        return Some(path);
                    } else {
                        return None;
                    }
                }
                Ptr::Tuple2(Tag::Expr(Sym), idx_cdr) => idx = *idx_cdr,
                _ => return None,
            }
        }
    }

    pub fn fetch_symbol(&self, ptr: &Ptr<F>) -> Option<Symbol> {
        if let Some(sym) = self.ptr_symbol_cache.get(ptr) {
            Some(sym.clone())
        } else {
            match ptr {
                Ptr::Atom(Tag::Expr(Sym), f) => {
                    if f == &F::ZERO {
                        let sym = Symbol::root_sym();
                        self.ptr_symbol_cache.insert(*ptr, Box::new(sym.clone()));
                        Some(sym)
                    } else {
                        None
                    }
                }
                Ptr::Atom(Tag::Expr(Key), f) => {
                    if f == &F::ZERO {
                        let key = Symbol::root_key();
                        self.ptr_symbol_cache.insert(*ptr, Box::new(key.clone()));
                        Some(key)
                    } else {
                        None
                    }
                }
                Ptr::Tuple2(Tag::Expr(Sym | Nil), idx) => {
                    let path = self.fetch_symbol_path(*idx)?;
                    let sym = Symbol::sym_from_vec(path);
                    self.ptr_symbol_cache.insert(*ptr, Box::new(sym.clone()));
                    Some(sym)
                }
                Ptr::Tuple2(Tag::Expr(Key), idx) => {
                    let path = self.fetch_symbol_path(*idx)?;
                    let key = Symbol::key_from_vec(path);
                    self.ptr_symbol_cache.insert(*ptr, Box::new(key.clone()));
                    Some(key)
                }
                _ => None,
            }
        }
    }

    pub fn fetch_sym(&self, ptr: &Ptr<F>) -> Option<Symbol> {
        if ptr.tag() == &Tag::Expr(Sym) {
            self.fetch_symbol(ptr)
        } else {
            None
        }
    }

    pub fn fetch_key(&self, ptr: &Ptr<F>) -> Option<Symbol> {
        if ptr.tag() == &Tag::Expr(Key) {
            self.fetch_symbol(ptr)
        } else {
            None
        }
    }

    #[inline]
    pub fn hide(&self, secret: F, payload: Ptr<F>) -> Result<Ptr<F>> {
        Ok(Ptr::comm(
            self.hide_and_return_z_payload(secret, payload)?.0,
        ))
    }

    pub fn hide_and_return_z_payload(&self, secret: F, payload: Ptr<F>) -> Result<(F, ZPtr<F>)> {
        let z_ptr = self.hash_ptr(&payload)?;
        let hash = self
            .poseidon_cache
            .hash3(&[secret, z_ptr.tag_field(), *z_ptr.value()]);
        self.comms
            .insert(FWrap::<F>(hash), Box::new((secret, payload)));
        Ok((hash, z_ptr))
    }

    #[inline]
    pub fn commit(&self, payload: Ptr<F>) -> Result<Ptr<F>> {
        self.hide(F::NON_HIDING_COMMITMENT_SECRET, payload)
    }

    #[inline]
    pub fn open(&self, hash: F) -> Option<&(F, Ptr<F>)> {
        self.comms.get(&FWrap(hash))
    }

    #[inline]
    pub fn intern_lurk_symbol(&self, name: &str) -> Ptr<F> {
        self.intern_symbol(&lurk_sym(name))
    }

    #[inline]
    pub fn intern_nil(&self) -> Ptr<F> {
        self.intern_lurk_symbol("nil")
    }

    #[inline]
    pub fn intern_user_symbol(&self, name: &str) -> Ptr<F> {
        self.intern_symbol(&user_sym(name))
    }

    #[inline]
    pub fn key(&self, name: &str) -> Ptr<F> {
        self.intern_symbol(&Symbol::key(&[name.to_string()]))
    }

    #[inline]
    pub fn cons(&self, car: Ptr<F>, cdr: Ptr<F>) -> Ptr<F> {
        self.intern_2_ptrs(Tag::Expr(Cons), car, cdr)
    }

    #[inline]
    pub fn intern_fun(&self, arg: Ptr<F>, body: Ptr<F>, env: Ptr<F>) -> Ptr<F> {
        self.intern_3_ptrs(Tag::Expr(Fun), arg, body, env)
    }

    pub fn car_cdr(&self, ptr: &Ptr<F>) -> Result<(Ptr<F>, Ptr<F>)> {
        match ptr.tag() {
            Tag::Expr(Nil) => {
                let nil = self.intern_nil();
                Ok((nil, nil))
            }
            Tag::Expr(Cons) => {
                let Some(idx) = ptr.get_index2() else {
                    bail!("malformed cons pointer")
                };
                match self.fetch_2_ptrs(idx) {
                    Some(res) => Ok(*res),
                    None => bail!("car/cdr not found"),
                }
            }
            Tag::Expr(Str) => {
                if ptr.is_null() {
                    Ok((self.intern_nil(), Ptr::null(Tag::Expr(Str))))
                } else {
                    let Some(idx) = ptr.get_index2() else {
                        bail!("malformed str pointer")
                    };
                    match self.fetch_2_ptrs(idx) {
                        Some(res) => Ok(*res),
                        None => bail!("car/cdr not found"),
                    }
                }
            }
            _ => bail!("invalid pointer to extract car/cdr from"),
        }
    }

    pub fn list(&self, elts: Vec<Ptr<F>>) -> Ptr<F> {
        elts.into_iter().rev().fold(self.intern_nil(), |acc, elt| {
            self.intern_2_ptrs(Tag::Expr(Cons), elt, acc)
        })
    }

    pub fn intern_syntax(&self, syn: Syntax<F>) -> Ptr<F> {
        match syn {
            Syntax::Num(_, x) => Ptr::Atom(Tag::Expr(Num), x.into_scalar()),
            Syntax::UInt(_, UInt::U64(x)) => Ptr::Atom(Tag::Expr(U64), x.into()),
            Syntax::Char(_, x) => Ptr::Atom(Tag::Expr(Char), (x as u64).into()),
            Syntax::Symbol(_, symbol) => self.intern_symbol(&symbol),
            Syntax::String(_, x) => self.intern_string(&x),
            Syntax::Quote(pos, x) => {
                let xs = vec![Syntax::Symbol(pos, lurk_sym("quote").into()), *x];
                self.intern_syntax(Syntax::List(pos, xs))
            }
            Syntax::List(_, xs) => xs.into_iter().rev().fold(self.intern_nil(), |acc, x| {
                let car = self.intern_syntax(x);
                self.intern_2_ptrs(Tag::Expr(Cons), car, acc)
            }),
            Syntax::Improper(_, xs, end) => {
                xs.into_iter()
                    .rev()
                    .fold(self.intern_syntax(*end), |acc, x| {
                        let car = self.intern_syntax(x);
                        self.intern_2_ptrs(Tag::Expr(Cons), car, acc)
                    })
            }
        }
    }

    pub fn read(&self, state: Rc<RefCell<State>>, input: &str) -> Result<Ptr<F>> {
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
    ) -> Result<(Span<'a>, Ptr<F>, bool), Error> {
        match preceded(syntax::parse_space, syntax::parse_maybe_meta(state, false))
            .parse(input.into())
        {
            Ok((i, Some((is_meta, x)))) => Ok((i, self.intern_syntax(x), is_meta)),
            Ok((_, None)) => Err(Error::NoInput),
            Err(e) => Err(Error::Syntax(format!("{}", e))),
        }
    }

    #[inline]
    pub fn read_with_default_state(&self, input: &str) -> Result<Ptr<F>> {
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
    fn hash_ptr_unsafe(&self, ptr: &Ptr<F>) -> Result<ZPtr<F>> {
        match ptr {
            Ptr::Atom(tag, x) => match tag {
                Tag::Cont(Outermost | ContTag::Error | Dummy | Terminal) => {
                    // temporary shim for compatibility with Lurk Alpha
                    Ok(ZPtr::from_parts(
                        *tag,
                        self.poseidon_cache.hash8(&[F::ZERO; 8]),
                    ))
                }
                _ => Ok(ZPtr::from_parts(*tag, *x)),
            },
            Ptr::Tuple2(tag, idx) => {
                if let Some(z_ptr) = self.z_cache.get(ptr) {
                    Ok(*z_ptr)
                } else {
                    let Some((a, b)) = self.fetch_2_ptrs(*idx) else {
                        bail!("Index {idx} not found on tuple2")
                    };
                    let a = self.hash_ptr_unsafe(a)?;
                    let b = self.hash_ptr_unsafe(b)?;
                    let z_ptr = ZPtr::from_parts(
                        *tag,
                        self.poseidon_cache.hash4(&[
                            a.tag_field(),
                            *a.value(),
                            b.tag_field(),
                            *b.value(),
                        ]),
                    );
                    self.z_cache.insert(*ptr, Box::new(z_ptr));
                    Ok(z_ptr)
                }
            }
            Ptr::Tuple3(tag, idx) => {
                if let Some(z_ptr) = self.z_cache.get(ptr) {
                    Ok(*z_ptr)
                } else {
                    let Some((a, b, c)) = self.fetch_3_ptrs(*idx) else {
                        bail!("Index {idx} not found on tuple3")
                    };
                    let a = self.hash_ptr_unsafe(a)?;
                    let b = self.hash_ptr_unsafe(b)?;
                    let c = self.hash_ptr_unsafe(c)?;
                    let z_ptr = ZPtr::from_parts(
                        *tag,
                        self.poseidon_cache.hash6(&[
                            a.tag_field(),
                            *a.value(),
                            b.tag_field(),
                            *b.value(),
                            c.tag_field(),
                            *c.value(),
                        ]),
                    );
                    self.z_cache.insert(*ptr, Box::new(z_ptr));
                    Ok(z_ptr)
                }
            }
            Ptr::Tuple4(tag, idx) => {
                if let Some(z_ptr) = self.z_cache.get(ptr) {
                    Ok(*z_ptr)
                } else {
                    let Some((a, b, c, d)) = self.fetch_4_ptrs(*idx) else {
                        bail!("Index {idx} not found on tuple4")
                    };
                    let a = self.hash_ptr_unsafe(a)?;
                    let b = self.hash_ptr_unsafe(b)?;
                    let c = self.hash_ptr_unsafe(c)?;
                    let d = self.hash_ptr_unsafe(d)?;
                    let z_ptr = ZPtr::from_parts(
                        *tag,
                        self.poseidon_cache.hash8(&[
                            a.tag_field(),
                            *a.value(),
                            b.tag_field(),
                            *b.value(),
                            c.tag_field(),
                            *c.value(),
                            d.tag_field(),
                            *d.value(),
                        ]),
                    );
                    self.z_cache.insert(*ptr, Box::new(z_ptr));
                    Ok(z_ptr)
                }
            }
        }
    }

    /// Hashes pointers in parallel, consuming chunks of length 256, which is a
    /// reasonably safe limit in terms of memory consumption.
    fn hydrate_z_cache_with_ptrs(&self, ptrs: &[&Ptr<F>]) {
        for chunk in ptrs.chunks(256) {
            chunk.par_iter().for_each(|ptr| {
                self.hash_ptr_unsafe(ptr).expect("hash_ptr failed");
            });
        }
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
    pub fn hash_ptr(&self, ptr: &Ptr<F>) -> Result<ZPtr<F>> {
        if self.is_below_safe_threshold() {
            // just run `hash_ptr_unsafe` for extra speed when the dehydrated
            // queue is small enough
            return self.hash_ptr_unsafe(ptr);
        }
        let mut ptrs: IndexSet<&Ptr<F>> = IndexSet::default();
        let mut stack = vec![ptr];
        macro_rules! feed_loop {
            ($x:expr) => {
                if $x.is_tuple() {
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
                Ptr::Atom(..) => (),
                Ptr::Tuple2(_, idx) => {
                    let Some((a, b)) = self.fetch_2_ptrs(*idx) else {
                        bail!("Index {idx} not found on tuple2")
                    };
                    for ptr in [a, b] {
                        feed_loop!(ptr)
                    }
                }
                Ptr::Tuple3(_, idx) => {
                    let Some((a, b, c)) = self.fetch_3_ptrs(*idx) else {
                        bail!("Index {idx} not found on tuple3")
                    };
                    for ptr in [a, b, c] {
                        feed_loop!(ptr)
                    }
                }
                Ptr::Tuple4(_, idx) => {
                    let Some((a, b, c, d)) = self.fetch_4_ptrs(*idx) else {
                        bail!("Index {idx} not found on tuple4")
                    };
                    for ptr in [a, b, c, d] {
                        feed_loop!(ptr)
                    }
                }
            }
        }
        ptrs.reverse();
        self.hydrate_z_cache_with_ptrs(&ptrs.into_iter().collect::<Vec<_>>());
        // Now it's okay to call `hash_ptr_unsafe`
        self.hash_ptr_unsafe(ptr)
    }

    pub fn to_vector(&self, ptrs: &[Ptr<F>]) -> Result<Vec<F>> {
        ptrs.iter()
            .try_fold(Vec::with_capacity(2 * ptrs.len()), |mut acc, ptr| {
                let z_ptr = self.hash_ptr(ptr)?;
                acc.push(z_ptr.tag_field());
                acc.push(*z_ptr.value());
                Ok(acc)
            })
    }

    /// Equality of the content-addressed versions of two pointers
    #[inline]
    pub fn ptr_eq(&self, a: &Ptr<F>, b: &Ptr<F>) -> Result<bool> {
        Ok(self.hash_ptr(a)? == self.hash_ptr(b)?)
    }
}

impl<F: LurkField> Ptr<F> {
    pub fn dbg_display(self, store: &Store<F>) -> String {
        if let Some(s) = store.fetch_string(&self) {
            return format!("\"{s}\"");
        }
        if let Some(s) = store.fetch_symbol(&self) {
            return format!("{s}");
        }
        match self {
            Ptr::Atom(tag, f) => {
                if let Some(x) = f.to_u64() {
                    format!("{tag}{x}")
                } else {
                    format!("{tag}{f:?}")
                }
            }
            Ptr::Tuple2(tag, x) => {
                let (p1, p2) = store.fetch_2_ptrs(x).unwrap();
                format!(
                    "({} {} {})",
                    tag,
                    (*p1).dbg_display(store),
                    (*p2).dbg_display(store)
                )
            }
            Ptr::Tuple3(tag, x) => {
                let (p1, p2, p3) = store.fetch_3_ptrs(x).unwrap();
                format!(
                    "({} {} {} {})",
                    tag,
                    (*p1).dbg_display(store),
                    (*p2).dbg_display(store),
                    (*p3).dbg_display(store)
                )
            }
            Ptr::Tuple4(tag, x) => {
                let (p1, p2, p3, p4) = store.fetch_4_ptrs(x).unwrap();
                format!(
                    "({} {} {} {} {})",
                    tag,
                    (*p1).dbg_display(store),
                    (*p2).dbg_display(store),
                    (*p3).dbg_display(store),
                    (*p4).dbg_display(store)
                )
            }
        }
    }

    fn unfold_list(&self, store: &Store<F>) -> Option<(Vec<Ptr<F>>, Option<Ptr<F>>)> {
        let mut idx = self.get_index2()?;
        let mut list = vec![];
        let mut last = None;
        while let Some((car, cdr)) = store.fetch_2_ptrs(idx) {
            list.push(*car);
            match cdr.tag() {
                Tag::Expr(Nil) => break,
                Tag::Expr(Cons) => {
                    idx = cdr.get_index2()?;
                }
                _ => {
                    last = Some(*cdr);
                    break;
                }
            }
        }
        Some((list, last))
    }

    pub fn fmt_to_string(&self, store: &Store<F>, state: &State) -> String {
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
                Char => match self.get_atom().map(F::to_char) {
                    Some(Some(c)) => format!("\'{c}\'"),
                    _ => "<Malformed Char>".into(),
                },
                Cons => {
                    if let Some((list, last)) = self.unfold_list(store) {
                        let list = list
                            .iter()
                            .map(|p| p.fmt_to_string(store, state))
                            .collect::<Vec<_>>();
                        if let Some(last) = last {
                            format!(
                                "({} . {})",
                                list.join(" "),
                                last.fmt_to_string(store, state)
                            )
                        } else {
                            format!("({})", list.join(" "))
                        }
                    } else {
                        "<Opaque Cons>".into()
                    }
                }
                Num => match self.get_atom() {
                    None => "<Malformed Num>".into(),
                    Some(f) => {
                        if let Some(u) = f.to_u64() {
                            u.to_string()
                        } else {
                            format!("0x{}", f.hex_digits())
                        }
                    }
                },
                U64 => match self.get_atom().map(F::to_u64) {
                    Some(Some(u)) => format!("{u}u64"),
                    _ => "<Malformed U64>".into(),
                },
                Fun => match self.get_index3() {
                    None => "<Malformed Fun>".into(),
                    Some(idx) => {
                        if let Some((arg, bod, _)) = store.fetch_3_ptrs(idx) {
                            match bod.tag() {
                                Tag::Expr(Nil) => {
                                    format!(
                                        "<FUNCTION ({}) {}>",
                                        arg.fmt_to_string(store, state),
                                        bod.fmt_to_string(store, state)
                                    )
                                }
                                Tag::Expr(Cons) => {
                                    if let Some(idx) = bod.get_index2() {
                                        if let Some((bod, _)) = store.fetch_2_ptrs(idx) {
                                            format!(
                                                "<FUNCTION ({}) {}>",
                                                arg.fmt_to_string(store, state),
                                                bod.fmt_to_string(store, state)
                                            )
                                        } else {
                                            "<Opaque Fun>".into()
                                        }
                                    } else {
                                        "<Malformed Fun>".into()
                                    }
                                }
                                _ => "<Malformed Fun>".into(),
                            }
                        } else {
                            "<Opaque Fun>".into()
                        }
                    }
                },
                Thunk => match self.get_index2() {
                    None => "<Malformed Thunk>".into(),
                    Some(idx) => {
                        if let Some((val, cont)) = store.fetch_2_ptrs(idx) {
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
                Comm => match self.get_atom() {
                    Some(f) => {
                        if store.comms.get(&FWrap(*f)).is_some() {
                            format!("(comm 0x{})", f.hex_digits())
                        } else {
                            format!("<Opaque Comm 0x{}>", f.hex_digits())
                        }
                    }
                    None => "<Malformed Comm>".into(),
                },
                Cproc => match self.get_index2() {
                    None => "<Malformed Cproc>".into(),
                    Some(idx) => {
                        if let Some((cproc_name, args)) = store.fetch_2_ptrs(idx) {
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

    fn fmt_cont2_to_string(
        &self,
        name: &str,
        field: &str,
        store: &Store<F>,
        state: &State,
    ) -> String {
        match self.get_index2() {
            None => format!("<Malformed {name}>"),
            Some(idx) => {
                if let Some((a, cont)) = store.fetch_2_ptrs(idx) {
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

    fn fmt_cont3_to_string(
        &self,
        name: &str,
        fields: (&str, &str),
        store: &Store<F>,
        state: &State,
    ) -> String {
        match self.get_index3() {
            None => format!("<Malformed {name}>"),
            Some(idx) => {
                if let Some((a, b, cont)) = store.fetch_3_ptrs(idx) {
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

    fn fmt_cont4_to_string(
        &self,
        name: &str,
        fields: (&str, &str, &str),
        store: &Store<F>,
        state: &State,
    ) -> String {
        match self.get_index4() {
            None => format!("<Malformed {name}>"),
            Some(idx) => {
                if let Some((a, b, c, cont)) = store.fetch_4_ptrs(idx) {
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

#[cfg(test)]
mod tests {
    #[test]
    fn test_ptr_hashing() {
        let string = String::from_utf8(vec![b'0'; 4096]).unwrap();
        let store = super::Store::<blstrs::Scalar>::default();
        let ptr = store.intern_string(&string);
        // `hash_ptr_unsafe` would overflow the stack, whereas `hash_ptr` works
        let x = store.hash_ptr(&ptr).unwrap();

        let store = super::Store::<blstrs::Scalar>::default();
        let ptr = store.intern_string(&string);
        store.hydrate_z_cache();
        // but `hash_ptr_unsafe` works just fine after manual hydration
        let y = store.hash_ptr_unsafe(&ptr).unwrap();

        // and, of course, those functions result on the same `ZPtr`
        assert_eq!(x, y);
    }
}
