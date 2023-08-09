use rayon::prelude::*;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    field::{FWrap, LurkField},
    hash::PoseidonCache,
    lem::Tag,
    state::{lurk_sym, State},
    symbol::Symbol,
    syntax::Syntax,
    tag::ExprTag::*,
    uint::UInt,
};
use anyhow::{bail, Result};
use dashmap::DashMap;
use indexmap::IndexSet;

use super::pointers::{Ptr, ZChildren, ZPtr};

/// The `Store` is a crucial part of Lurk's implementation and tries to be a
/// vesatile data structure for many parts of Lurk's data pipeline.
///
/// It holds Lurk data structured as trees of `Ptr`s (or `ZPtr`s). When a `Ptr`
/// has children`, we store them in the `IndexSet`s available: `ptrs2`, `ptrs3`
/// or `ptrs4`. These data structures speed up LEM interpretation because lookups
/// by indices are fast.
///
/// The `Store` also provides an infra to speed up interning strings and symbols.
/// This data is saved in `str_tails_cache` and `sym_tails_cache`, which are better
/// explained in `intern_string` and `intern_symbol_path` respectively.
///
/// There's also a process that we call "hydration", in which we use Poseidon
/// hashes to compute the (stable) hash of the children of a pointer. These hashes
/// are necessary when we want to create Lurk proofs because the circuit consumes
/// elements of the `LurkField`, not (unstable) indices of `IndexSet`s.
///
/// Lastly, we have a `HashMap` to hold committed data, which can be retrieved by
/// the resulting commitment hash.
#[derive(Default)]
pub struct Store<F: LurkField> {
    ptrs2: IndexSet<(Ptr<F>, Ptr<F>)>,
    ptrs3: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>)>,
    ptrs4: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>, Ptr<F>)>,

    str_cache: HashMap<String, Ptr<F>>,
    ptr_str_cache: HashMap<Ptr<F>, String>,
    sym_cache: HashMap<Vec<String>, Ptr<F>>,
    ptr_sym_cache: HashMap<Ptr<F>, Vec<String>>,

    pub poseidon_cache: PoseidonCache<F>,
    dehydrated: Vec<Ptr<F>>,
    z_cache: DashMap<Ptr<F>, ZPtr<F>, ahash::RandomState>,
    z_dag: DashMap<ZPtr<F>, ZChildren<F>, ahash::RandomState>,

    pub comms: HashMap<FWrap<F>, (F, Ptr<F>)>, // hash -> (secret, src)
}

impl<F: LurkField> Store<F> {
    /// Creates a `Ptr` that's a parent of two children
    pub fn intern_2_ptrs(&mut self, tag: Tag, a: Ptr<F>, b: Ptr<F>) -> Ptr<F> {
        let (idx, inserted) = self.ptrs2.insert_full((a, b));
        let ptr = Ptr::Tree2(tag, idx);
        if inserted {
            // this is for `hydrate_z_cache`
            self.dehydrated.push(ptr);
        }
        ptr
    }

    /// Similar to `intern_2_ptrs` but doesn't add the resulting pointer to
    /// `dehydrated`. This function is used when converting a `ZStore` to a
    /// `Store` (TODO).
    #[inline]
    pub fn intern_2_ptrs_not_dehydrated(&mut self, tag: Tag, a: Ptr<F>, b: Ptr<F>) -> Ptr<F> {
        Ptr::Tree2(tag, self.ptrs2.insert_full((a, b)).0)
    }

    /// Creates a `Ptr` that's a parent of three children
    pub fn intern_3_ptrs(&mut self, tag: Tag, a: Ptr<F>, b: Ptr<F>, c: Ptr<F>) -> Ptr<F> {
        let (idx, inserted) = self.ptrs3.insert_full((a, b, c));
        let ptr = Ptr::Tree3(tag, idx);
        if inserted {
            // this is for `hydrate_z_cache`
            self.dehydrated.push(ptr);
        }
        ptr
    }

    /// Similar to `intern_3_ptrs` but doesn't add the resulting pointer to
    /// `dehydrated`. This function is used when converting a `ZStore` to a
    /// `Store` (TODO).
    #[inline]
    pub fn intern_3_ptrs_not_dehydrated(
        &mut self,
        tag: Tag,
        a: Ptr<F>,
        b: Ptr<F>,
        c: Ptr<F>,
    ) -> Ptr<F> {
        Ptr::Tree3(tag, self.ptrs3.insert_full((a, b, c)).0)
    }

    /// Creates a `Ptr` that's a parent of four children
    pub fn intern_4_ptrs(
        &mut self,
        tag: Tag,
        a: Ptr<F>,
        b: Ptr<F>,
        c: Ptr<F>,
        d: Ptr<F>,
    ) -> Ptr<F> {
        let (idx, inserted) = self.ptrs4.insert_full((a, b, c, d));
        let ptr = Ptr::Tree4(tag, idx);
        if inserted {
            // this is for `hydrate_z_cache`
            self.dehydrated.push(ptr);
        }
        ptr
    }

    /// Similar to `intern_4_ptrs` but doesn't add the resulting pointer to
    /// `dehydrated`. This function is used when converting a `ZStore` to a
    /// `Store` (TODO).
    #[inline]
    pub fn intern_4_ptrs_not_dehydrated(
        &mut self,
        tag: Tag,
        a: Ptr<F>,
        b: Ptr<F>,
        c: Ptr<F>,
        d: Ptr<F>,
    ) -> Ptr<F> {
        Ptr::Tree4(tag, self.ptrs4.insert_full((a, b, c, d)).0)
    }

    #[inline]
    pub fn fetch_2_ptrs(&self, idx: usize) -> Option<&(Ptr<F>, Ptr<F>)> {
        self.ptrs2.get_index(idx)
    }

    #[inline]
    pub fn fetch_3_ptrs(&self, idx: usize) -> Option<&(Ptr<F>, Ptr<F>, Ptr<F>)> {
        self.ptrs3.get_index(idx)
    }

    #[inline]
    pub fn fetch_4_ptrs(&self, idx: usize) -> Option<&(Ptr<F>, Ptr<F>, Ptr<F>, Ptr<F>)> {
        self.ptrs4.get_index(idx)
    }

    /// Interns a string recursively
    pub fn intern_string(&mut self, s: &str) -> Ptr<F> {
        if s.is_empty() {
            let ptr = Ptr::null(Tag::Expr(Str));
            self.ptr_str_cache.insert(ptr, "".into());
            return ptr;
        }

        match self.str_cache.get(s) {
            Some(ptr_cache) => *ptr_cache,
            None => {
                let tail = &s.chars().skip(1).collect::<String>();
                let tail_ptr = self.intern_string(tail);
                let head = s.chars().next().unwrap();
                let s_ptr = self.intern_2_ptrs(Tag::Expr(Str), Ptr::char(head), tail_ptr);
                self.str_cache.insert(s.into(), s_ptr);
                self.ptr_str_cache.insert(s_ptr, s.into());
                s_ptr
            }
        }
    }

    #[inline]
    pub fn fetch_string(&self, ptr: &Ptr<F>) -> Option<&String> {
        match ptr.tag() {
            Tag::Expr(Str) => self.ptr_str_cache.get(ptr),
            _ => None,
        }
    }

    /// Interns a symbol path recursively
    pub fn intern_symbol_path(&mut self, path: &[String]) -> Ptr<F> {
        if path.is_empty() {
            let ptr = Ptr::null(Tag::Expr(Sym));
            self.ptr_sym_cache.insert(ptr, vec![]);
            return ptr;
        }

        match self.sym_cache.get(path) {
            Some(ptr_cache) => *ptr_cache,
            None => {
                let tail = &path[1..];
                let tail_ptr = self.intern_symbol_path(tail);
                let head = &path[0];
                let head_ptr = self.intern_string(head);
                let path_ptr = self.intern_2_ptrs(Tag::Expr(Sym), head_ptr, tail_ptr);
                self.sym_cache.insert(path.to_vec(), path_ptr);
                self.ptr_sym_cache.insert(path_ptr, path.to_vec());
                path_ptr
            }
        }
    }

    #[inline]
    pub fn fetch_sym_path(&self, ptr: &Ptr<F>) -> Option<&Vec<String>> {
        self.ptr_sym_cache.get(ptr)
    }

    #[inline]
    pub fn fetch_symbol(&self, ptr: &Ptr<F>) -> Option<Symbol> {
        match ptr.tag() {
            Tag::Expr(Sym) | Tag::Expr(Key) => Some(Symbol::new(
                self.fetch_sym_path(ptr)?,
                ptr.tag() == &Tag::Expr(Key),
            )),
            _ => None,
        }
    }

    pub fn intern_symbol(&mut self, sym: &Symbol) -> Ptr<F> {
        let path_ptr = self.intern_symbol_path(sym.path());
        if sym == &lurk_sym("nil") {
            path_ptr.cast(Tag::Expr(Nil))
        } else if !sym.is_keyword() {
            path_ptr
        } else {
            path_ptr.cast(Tag::Expr(Key))
        }
    }

    pub fn intern_syntax(&mut self, syn: Syntax<F>) -> Result<Ptr<F>> {
        match syn {
            Syntax::Num(_, x) => Ok(Ptr::Leaf(Tag::Expr(Num), x.into_scalar())),
            Syntax::UInt(_, UInt::U64(x)) => Ok(Ptr::Leaf(Tag::Expr(U64), x.into())),
            Syntax::Char(_, x) => Ok(Ptr::Leaf(Tag::Expr(Char), (x as u64).into())),
            Syntax::Symbol(_, symbol) => Ok(self.intern_symbol(&symbol)),
            Syntax::String(_, x) => Ok(self.intern_string(&x)),
            Syntax::Quote(pos, x) => {
                let xs = vec![Syntax::Symbol(pos, lurk_sym("quote").into()), *x];
                self.intern_syntax(Syntax::List(pos, xs))
            }
            Syntax::List(_, xs) => {
                let mut cdr = self.intern_symbol(&lurk_sym("nil"));
                for x in xs.into_iter().rev() {
                    let car = self.intern_syntax(x)?;
                    cdr = self.intern_2_ptrs(Tag::Expr(Cons), car, cdr);
                }
                Ok(cdr)
            }
            Syntax::Improper(_, xs, end) => {
                let mut cdr = self.intern_syntax(*end)?;
                for x in xs.into_iter().rev() {
                    let car = self.intern_syntax(x)?;
                    cdr = self.intern_2_ptrs(Tag::Expr(Cons), car, cdr);
                }
                Ok(cdr)
            }
        }
    }

    pub fn read(&mut self, state: Rc<RefCell<State>>, input: &str) -> Result<Ptr<F>> {
        use crate::parser::*;
        use nom::sequence::preceded;
        use nom::Parser;
        match preceded(
            syntax::parse_space,
            syntax::parse_syntax(state, false, false),
        )
        .parse(Span::new(input))
        {
            Ok((_i, x)) => self.intern_syntax(x),
            Err(e) => bail!("{}", e),
        }
    }

    /// Recursively hashes the children of a `Ptr` in order to obtain its
    /// corresponding `ZPtr`. While traversing a `Ptr` tree, it consults the
    /// cache of `Ptr`s that have already been hydrated and also populates this
    /// cache for the new `Ptr`s.
    ///
    /// Warning: without cache hits, this function might blow up Rust's recursion
    /// depth limit. This limitation is circumvented by calling `hydrate_z_cache`.
    pub fn hash_ptr(&self, ptr: &Ptr<F>) -> Result<ZPtr<F>> {
        match ptr {
            Ptr::Leaf(tag, x) => Ok(ZPtr {
                tag: *tag,
                hash: *x,
            }),
            Ptr::Tree2(tag, idx) => match self.z_cache.get(ptr) {
                Some(z_ptr) => Ok(*z_ptr),
                None => {
                    let Some((a, b)) = self.ptrs2.get_index(*idx) else {
                        bail!("Index {idx} not found on ptrs2")
                    };
                    let a = self.hash_ptr(a)?;
                    let b = self.hash_ptr(b)?;
                    let z_ptr = ZPtr {
                        tag: *tag,
                        hash: self.poseidon_cache.hash4(&[
                            a.tag.to_field(),
                            a.hash,
                            b.tag.to_field(),
                            b.hash,
                        ]),
                    };
                    self.z_dag.insert(z_ptr, ZChildren::Tree2(a, b));
                    self.z_cache.insert(*ptr, z_ptr);
                    Ok(z_ptr)
                }
            },
            Ptr::Tree3(tag, idx) => match self.z_cache.get(ptr) {
                Some(z_ptr) => Ok(*z_ptr),
                None => {
                    let Some((a, b, c)) = self.ptrs3.get_index(*idx) else {
                        bail!("Index {idx} not found on ptrs3")
                    };
                    let a = self.hash_ptr(a)?;
                    let b = self.hash_ptr(b)?;
                    let c = self.hash_ptr(c)?;
                    let z_ptr = ZPtr {
                        tag: *tag,
                        hash: self.poseidon_cache.hash6(&[
                            a.tag.to_field(),
                            a.hash,
                            b.tag.to_field(),
                            b.hash,
                            c.tag.to_field(),
                            c.hash,
                        ]),
                    };
                    self.z_dag.insert(z_ptr, ZChildren::Tree3(a, b, c));
                    self.z_cache.insert(*ptr, z_ptr);
                    Ok(z_ptr)
                }
            },
            Ptr::Tree4(tag, idx) => match self.z_cache.get(ptr) {
                Some(z_ptr) => Ok(*z_ptr),
                None => {
                    let Some((a, b, c, d)) = self.ptrs4.get_index(*idx) else {
                        bail!("Index {idx} not found on ptrs4")
                    };
                    let a = self.hash_ptr(a)?;
                    let b = self.hash_ptr(b)?;
                    let c = self.hash_ptr(c)?;
                    let d = self.hash_ptr(d)?;
                    let z_ptr = ZPtr {
                        tag: *tag,
                        hash: self.poseidon_cache.hash8(&[
                            a.tag.to_field(),
                            a.hash,
                            b.tag.to_field(),
                            b.hash,
                            c.tag.to_field(),
                            c.hash,
                            d.tag.to_field(),
                            d.hash,
                        ]),
                    };
                    self.z_dag.insert(z_ptr, ZChildren::Tree4(a, b, c, d));
                    self.z_cache.insert(*ptr, z_ptr);
                    Ok(z_ptr)
                }
            },
        }
    }

    /// Hashes `Ptr` trees from the bottom to the top, avoiding deep recursions
    /// in `hash_ptr`.
    pub fn hydrate_z_cache(&mut self) {
        self.dehydrated.par_iter().for_each(|ptr| {
            self.hash_ptr(ptr).expect("failed to hydrate pointer");
        });
        self.dehydrated = Vec::new();
    }
}

impl<F: LurkField> Ptr<F> {
    pub fn to_string(self, store: &Store<F>) -> String {
        if let Some(s) = store.fetch_string(&self) {
            return format!("\"{}\"", s);
        }
        if let Some(s) = store.fetch_symbol(&self) {
            return format!("{}", s);
        }
        match self {
            Ptr::Leaf(tag, f) => {
                if let Some(x) = f.to_u64() {
                    format!("{}{}", tag, x)
                } else {
                    format!("{}{:?}", tag, f)
                }
            }
            Ptr::Tree2(tag, x) => {
                let (p1, p2) = store.fetch_2_ptrs(x).unwrap();
                format!(
                    "({} {} {})",
                    tag,
                    (*p1).to_string(store),
                    (*p2).to_string(store)
                )
            }
            Ptr::Tree3(tag, x) => {
                let (p1, p2, p3) = store.fetch_3_ptrs(x).unwrap();
                format!(
                    "({} {} {} {})",
                    tag,
                    (*p1).to_string(store),
                    (*p2).to_string(store),
                    (*p3).to_string(store)
                )
            }
            Ptr::Tree4(tag, x) => {
                let (p1, p2, p3, p4) = store.fetch_4_ptrs(x).unwrap();
                format!(
                    "({} {} {} {} {})",
                    tag,
                    (*p1).to_string(store),
                    (*p2).to_string(store),
                    (*p3).to_string(store),
                    (*p4).to_string(store)
                )
            }
        }
    }
}
