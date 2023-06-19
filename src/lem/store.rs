use rayon::prelude::*;
use std::collections::HashMap;

use crate::{
    field::{FWrap, LurkField},
    hash::PoseidonCache,
    lem::tag::Tag,
};
use anyhow::{bail, Result};
use dashmap::DashMap;
use indexmap::IndexSet;

use super::{
    pointers::{Ptr, ZChildren, ZPtr},
    symbol::Symbol,
    AString,
};

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

    str_tails_cache: HashMap<String, Ptr<F>>,
    sym_tails_cache: HashMap<Vec<AString>, Ptr<F>>,
    sym_path_cache: HashMap<Ptr<F>, Vec<AString>>,

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

    /// Iterates on the tails of a string, interning all of them, eventually
    /// interning the full string provided as input. If some tail has already
    /// been interned (and cached), break the loop.
    ///
    /// Tails are cached as reversed `String`s because of how interning and hashing
    /// works: from right to left. So, for example, after interning the string
    /// `"abc"`, we will end up with cached pointers to the strings `"c"`, `"bc"`
    /// and `"abc"` stored in `str_tails_cache` as `"c"`, `"cb"` and `"cba"`
    /// respectively.
    pub fn intern_string(&mut self, s: &str) -> Ptr<F> {
        let mut tail = s.chars().rev().collect::<String>();
        let mut ptr;
        let mut heads = vec![];
        loop {
            // try a cache hit until no char is left while accumulating the heads
            if tail.is_empty() {
                ptr = Ptr::null(Tag::Str);
                break;
            }
            match self.str_tails_cache.get(&tail) {
                Some(ptr_cache) => {
                    ptr = *ptr_cache;
                    break;
                }
                None => heads.push(tail.pop().unwrap()),
            }
        }
        while let Some(head) = heads.pop() {
            // use the accumulated heads to construct the pointers and populate the cache
            ptr = self.intern_2_ptrs(Tag::Str, Ptr::char(head), ptr);
            tail.push(head);
            self.str_tails_cache.insert(tail.clone(), ptr);
        }
        ptr
    }

    /// Iterates on the tails of a symbol path, interning all of them, eventually
    /// interning the full symbol path provided as input. If some tail has already
    /// been interned (and cached), break the loop.
    ///
    /// Tails are cached as reversed vectors of `String`s because of how interning
    /// and hashing works: from right to left. So, for example, after interning
    /// the symbol path `["aa", "bb", "cc"]`, we will end up with cached pointers
    /// to the symbol paths `["cc"]`, `["bb", "cc"]` and `["aa", "bb", "cc"]`
    /// stored in `sym_tails_cache` as `["cc"]`, `["cc", "bb"]` and
    /// ["cc", "bb", "aa"]` respectively.
    pub fn intern_symbol_path(&mut self, path: &[AString]) -> Ptr<F> {
        let mut tail = path.to_owned();
        tail.reverse();
        let mut ptr;
        let mut heads = vec![];
        loop {
            // try a cache hit until no char is left while accumulating the heads
            if tail.is_empty() {
                ptr = Ptr::null(Tag::Sym);
                self.sym_path_cache.insert(ptr, vec![]);
                break;
            }
            match self.sym_tails_cache.get(&tail) {
                Some(ptr_cache) => {
                    ptr = *ptr_cache;
                    break;
                }
                None => heads.push(tail.pop().unwrap()),
            }
        }
        while let Some(head) = heads.pop() {
            // use the accumulated heads to construct the pointers and populate the cache
            let head_ptr = self.intern_string(&head);
            ptr = self.intern_2_ptrs(Tag::Sym, head_ptr, ptr);
            tail.push(head);
            self.sym_tails_cache.insert(tail.clone(), ptr);
            self.sym_path_cache
                .insert(ptr, tail.iter().rev().cloned().collect());
        }
        ptr
    }

    #[inline]
    pub fn fetch_sym_path(&self, ptr: &Ptr<F>) -> Option<&Vec<AString>> {
        self.sym_path_cache.get(ptr)
    }

    pub fn intern_symbol(&mut self, s: &Symbol) -> Ptr<F> {
        match s {
            Symbol::Sym(path) => self.intern_symbol_path(path),
            Symbol::Key(path) => self.intern_symbol_path(path).sym_to_key(),
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
