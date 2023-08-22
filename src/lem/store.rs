use anyhow::{bail, Result};
use indexmap::IndexSet;
use nom::{sequence::preceded, Parser};
use rayon::prelude::*;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    cache_map::CacheMap,
    field::{FWrap, LurkField},
    hash::PoseidonCache,
    lem::Tag,
    parser::*,
    state::{lurk_sym, State},
    symbol::Symbol,
    syntax::Syntax,
    tag::ExprTag::*,
    uint::UInt,
};

use super::pointers::{Ptr, ZPtr};

/// The `Store` is a crucial part of Lurk's implementation and tries to be a
/// vesatile data structure for many parts of Lurk's data pipeline.
///
/// It holds Lurk data structured as trees of `Ptr`s (or `ZPtr`s). When a `Ptr`
/// has children, we store them in the `IndexSet`s available: `tuple2`, `tuple3`
/// or `tuple4`. These data structures speed up LEM interpretation because lookups
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
    tuple2: IndexSet<(Ptr<F>, Ptr<F>)>,
    tuple3: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>)>,
    tuple4: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>, Ptr<F>)>,

    pub string_ptr_cache: HashMap<String, Ptr<F>>,
    ptr_string_cache: HashMap<Ptr<F>, String>,

    pub symbol_ptr_cache: HashMap<Symbol, Ptr<F>>,
    ptr_symbol_cache: HashMap<Ptr<F>, Symbol>,

    pub poseidon_cache: PoseidonCache<F>,

    dehydrated: Vec<Ptr<F>>,
    z_cache: CacheMap<Ptr<F>, Box<ZPtr<F>>>,

    comms: HashMap<FWrap<F>, (F, Ptr<F>)>, // hash -> (secret, src)
}

impl<F: LurkField> Store<F> {
    /// Creates a `Ptr` that's a parent of two children
    pub fn intern_2_ptrs(&mut self, tag: Tag, a: Ptr<F>, b: Ptr<F>) -> Ptr<F> {
        let (idx, inserted) = self.tuple2.insert_full((a, b));
        let ptr = Ptr::Tuple2(tag, idx);
        if inserted {
            // this is for `hydrate_z_cache`
            self.dehydrated.push(ptr);
        }
        ptr
    }

    /// Similar to `intern_2_ptrs` but doesn't add the resulting pointer to
    /// `dehydrated`. This function is used when converting a `ZStore` to a
    /// `Store`.
    #[inline]
    pub fn intern_2_ptrs_not_dehydrated(&mut self, tag: Tag, a: Ptr<F>, b: Ptr<F>) -> Ptr<F> {
        Ptr::Tuple2(tag, self.tuple2.insert_full((a, b)).0)
    }

    /// Creates a `Ptr` that's a parent of three children
    pub fn intern_3_ptrs(&mut self, tag: Tag, a: Ptr<F>, b: Ptr<F>, c: Ptr<F>) -> Ptr<F> {
        let (idx, inserted) = self.tuple3.insert_full((a, b, c));
        let ptr = Ptr::Tuple3(tag, idx);
        if inserted {
            // this is for `hydrate_z_cache`
            self.dehydrated.push(ptr);
        }
        ptr
    }

    /// Similar to `intern_3_ptrs` but doesn't add the resulting pointer to
    /// `dehydrated`. This function is used when converting a `ZStore` to a
    /// `Store`.
    #[inline]
    pub fn intern_3_ptrs_not_dehydrated(
        &mut self,
        tag: Tag,
        a: Ptr<F>,
        b: Ptr<F>,
        c: Ptr<F>,
    ) -> Ptr<F> {
        Ptr::Tuple3(tag, self.tuple3.insert_full((a, b, c)).0)
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
        let (idx, inserted) = self.tuple4.insert_full((a, b, c, d));
        let ptr = Ptr::Tuple4(tag, idx);
        if inserted {
            // this is for `hydrate_z_cache`
            self.dehydrated.push(ptr);
        }
        ptr
    }

    /// Similar to `intern_4_ptrs` but doesn't add the resulting pointer to
    /// `dehydrated`. This function is used when converting a `ZStore` to a
    /// `Store`.
    #[inline]
    pub fn intern_4_ptrs_not_dehydrated(
        &mut self,
        tag: Tag,
        a: Ptr<F>,
        b: Ptr<F>,
        c: Ptr<F>,
        d: Ptr<F>,
    ) -> Ptr<F> {
        Ptr::Tuple4(tag, self.tuple4.insert_full((a, b, c, d)).0)
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

    pub fn intern_string(&mut self, s: &str) -> Ptr<F> {
        if let Some(ptr) = self.string_ptr_cache.get(s) {
            *ptr
        } else {
            let ptr = s.chars().rev().fold(Ptr::null(Tag::Expr(Str)), |acc, c| {
                self.intern_2_ptrs(Tag::Expr(Str), Ptr::char(c), acc)
            });
            self.string_ptr_cache.insert(s.to_string(), ptr);
            self.ptr_string_cache.insert(ptr, s.to_string());
            ptr
        }
    }

    #[inline]
    pub fn fetch_string(&self, ptr: &Ptr<F>) -> Option<&String> {
        self.ptr_string_cache.get(ptr)
    }

    pub fn intern_symbol_path(&mut self, path: &[String]) -> Ptr<F> {
        path.iter().fold(Ptr::null(Tag::Expr(Sym)), |acc, s| {
            let s_ptr = self.intern_string(s);
            self.intern_2_ptrs(Tag::Expr(Sym), s_ptr, acc)
        })
    }

    pub fn intern_symbol(&mut self, sym: &Symbol) -> Ptr<F> {
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
            self.symbol_ptr_cache.insert(sym.clone(), sym_ptr);
            self.ptr_symbol_cache.insert(sym_ptr, sym.clone());
            sym_ptr
        }
    }

    #[inline]
    pub fn fetch_symbol(&self, ptr: &Ptr<F>) -> Option<&Symbol> {
        self.ptr_symbol_cache.get(ptr)
    }

    pub fn fetch_sym(&self, ptr: &Ptr<F>) -> Option<&Symbol> {
        if ptr.tag() == &Tag::Expr(Sym) {
            self.fetch_symbol(ptr)
        } else {
            None
        }
    }

    pub fn fetch_key(&self, ptr: &Ptr<F>) -> Option<&Symbol> {
        if ptr.tag() == &Tag::Expr(Key) {
            self.fetch_symbol(ptr)
        } else {
            None
        }
    }

    pub fn hide(&mut self, secret: F, payload: Ptr<F>) -> Result<Ptr<F>> {
        let z_ptr = self.hash_ptr(&payload)?;
        let hash = self
            .poseidon_cache
            .hash3(&[secret, z_ptr.tag.to_field(), z_ptr.hash]);
        self.comms.insert(FWrap::<F>(hash), (secret, payload));
        Ok(Ptr::comm(hash))
    }

    pub fn hide_and_return_z_payload(
        &mut self,
        secret: F,
        payload: Ptr<F>,
    ) -> Result<(F, ZPtr<F>)> {
        let z_ptr = self.hash_ptr(&payload)?;
        let hash = self
            .poseidon_cache
            .hash3(&[secret, z_ptr.tag.to_field(), z_ptr.hash]);
        self.comms.insert(FWrap::<F>(hash), (secret, payload));
        Ok((hash, z_ptr))
    }

    #[inline]
    pub fn commit(&mut self, payload: Ptr<F>) -> Result<Ptr<F>> {
        self.hide(F::NON_HIDING_COMMITMENT_SECRET, payload)
    }

    pub fn open(&self, hash: F) -> Option<&(F, Ptr<F>)> {
        self.comms.get(&FWrap(hash))
    }

    #[inline]
    pub fn intern_lurk_sym(&mut self, name: &str) -> Ptr<F> {
        self.intern_symbol(&lurk_sym(name))
    }

    #[inline]
    pub fn intern_nil(&mut self) -> Ptr<F> {
        self.intern_lurk_sym("nil")
    }

    #[inline]
    pub fn key(&mut self, name: &str) -> Ptr<F> {
        self.intern_symbol(&Symbol::key(&[name.to_string()]))
    }

    pub fn car_cdr(&mut self, ptr: &Ptr<F>) -> Result<(Ptr<F>, Ptr<F>)> {
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

    pub fn list(&mut self, elts: Vec<Ptr<F>>) -> Ptr<F> {
        elts.into_iter().rev().fold(self.intern_nil(), |acc, elt| {
            self.intern_2_ptrs(Tag::Expr(Cons), elt, acc)
        })
    }

    pub fn intern_syntax(&mut self, syn: Syntax<F>) -> Ptr<F> {
        match syn {
            Syntax::Num(_, x) => Ptr::Leaf(Tag::Expr(Num), x.into_scalar()),
            Syntax::UInt(_, UInt::U64(x)) => Ptr::Leaf(Tag::Expr(U64), x.into()),
            Syntax::Char(_, x) => Ptr::Leaf(Tag::Expr(Char), (x as u64).into()),
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

    pub fn read(&mut self, state: Rc<RefCell<State>>, input: &str) -> Result<Ptr<F>> {
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

    pub fn read_maybe_meta(
        &mut self,
        state: Rc<RefCell<State>>,
        input: &str,
    ) -> Result<(Ptr<F>, bool), crate::parser::Error> {
        match preceded(syntax::parse_space, syntax::parse_maybe_meta(state, false))
            .parse(input.into())
        {
            Ok((_, Some((is_meta, x)))) => Ok((self.intern_syntax(x), is_meta)),
            Ok((_, None)) => Err(Error::NoInput),
            Err(e) => Err(Error::Syntax(format!("{}", e))),
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
            Ptr::Tuple2(tag, idx) => match self.z_cache.get(ptr) {
                Some(z_ptr) => Ok(*z_ptr),
                None => {
                    let Some((a, b)) = self.fetch_2_ptrs(*idx) else {
                        bail!("Index {idx} not found on tuple2")
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
                    self.z_cache.insert(*ptr, Box::new(z_ptr));
                    Ok(z_ptr)
                }
            },
            Ptr::Tuple3(tag, idx) => match self.z_cache.get(ptr) {
                Some(z_ptr) => Ok(*z_ptr),
                None => {
                    let Some((a, b, c)) = self.fetch_3_ptrs(*idx) else {
                        bail!("Index {idx} not found on tuple3")
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
                    self.z_cache.insert(*ptr, Box::new(z_ptr));
                    Ok(z_ptr)
                }
            },
            Ptr::Tuple4(tag, idx) => match self.z_cache.get(ptr) {
                Some(z_ptr) => Ok(*z_ptr),
                None => {
                    let Some((a, b, c, d)) = self.fetch_4_ptrs(*idx) else {
                        bail!("Index {idx} not found on tuple4")
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
                    self.z_cache.insert(*ptr, Box::new(z_ptr));
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

    #[inline]
    pub fn add_to_z_cache(&mut self, ptr: Ptr<F>, z_ptr: ZPtr<F>) {
        self.z_cache.insert(ptr, Box::new(z_ptr));
    }

    pub fn to_vector(&self, ptrs: &[Ptr<F>]) -> Result<Vec<F>> {
        ptrs.iter()
            .try_fold(Vec::with_capacity(2 * ptrs.len()), |mut acc, ptr| {
                let z_ptr = self.hash_ptr(ptr)?;
                acc.push(z_ptr.tag.to_field());
                acc.push(z_ptr.hash);
                Ok(acc)
            })
    }
}

impl<F: LurkField> Ptr<F> {
    pub fn dbg_display(self, store: &Store<F>) -> String {
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
                        state.fmt_to_string(&sym.clone().into())
                    } else {
                        "<Opaque Nil>".into()
                    }
                }
                Sym => {
                    if let Some(sym) = store.fetch_sym(self) {
                        state.fmt_to_string(&sym.clone().into())
                    } else {
                        "<Opaque Sym>".into()
                    }
                }
                Key => {
                    if let Some(key) = store.fetch_key(self) {
                        state.fmt_to_string(&key.clone().into())
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
                Char => match self.get_leaf().map(F::to_char) {
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
                Num => match self.get_leaf() {
                    None => "<Malformed Num>".into(),
                    Some(f) => {
                        if let Some(u) = f.to_u64() {
                            u.to_string()
                        } else {
                            format!("0x{}", f.hex_digits())
                        }
                    }
                },
                U64 => match self.get_leaf().map(F::to_u64) {
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
                Comm => match self.get_leaf() {
                    Some(f) => {
                        if store.comms.contains_key(&FWrap(*f)) {
                            format!("(comm 0x{})", f.hex_digits())
                        } else {
                            format!("<Opaque Comm 0x{}>", f.hex_digits())
                        }
                    }
                    None => "<Malformed Comm>".into(),
                },
            },
            Tag::Cont(_) => todo!(),
            Tag::Ctrl(_) => unreachable!(),
        }
    }
}
