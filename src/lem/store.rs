use rayon::prelude::*;
use std::collections::HashMap;

use dashmap::DashMap;
use indexmap::IndexSet;
use itertools::Itertools;

use crate::{
    field::{FWrap, LurkField},
    hash::PoseidonCache,
    lem::tag::Tag,
};

use super::{
    pointers::{AquaPtr, AquaPtrKind, Ptr},
    symbol::Symbol,
};

#[derive(Default)]
pub struct Store<F: LurkField> {
    ptrs2: IndexSet<(Ptr<F>, Ptr<F>)>,
    ptrs3: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>)>,
    ptrs4: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>, Ptr<F>)>,

    vec_char_cache: HashMap<Vec<char>, Ptr<F>>,
    vec_str_cache: HashMap<Vec<String>, Ptr<F>>,

    dehydrated: Vec<Ptr<F>>,
    aqua_cache: DashMap<Ptr<F>, AquaPtr<F>, ahash::RandomState>,
    aqua_dag: DashMap<AquaPtr<F>, AquaPtrKind<F>, ahash::RandomState>,

    pub poseidon_cache: PoseidonCache<F>,
    pub comms: HashMap<FWrap<F>, (F, Ptr<F>)>, // hash -> (secret, src)
}

impl<F: LurkField> Store<F> {
    pub fn index_2_ptrs(&mut self, tag: Tag, a: Ptr<F>, b: Ptr<F>) -> Ptr<F> {
        let (idx, inserted) = self.ptrs2.insert_full((a, b));
        let ptr = Ptr::Tree2(tag, idx);
        if inserted {
            self.dehydrated.push(ptr);
        }
        ptr
    }

    #[inline]
    pub fn index_2_ptrs_not_dehydrated(&mut self, tag: Tag, a: Ptr<F>, b: Ptr<F>) -> Ptr<F> {
        Ptr::Tree2(tag, self.ptrs2.insert_full((a, b)).0)
    }

    pub fn index_3_ptrs(&mut self, tag: Tag, a: Ptr<F>, b: Ptr<F>, c: Ptr<F>) -> Ptr<F> {
        let (idx, inserted) = self.ptrs3.insert_full((a, b, c));
        let ptr = Ptr::Tree3(tag, idx);
        if inserted {
            self.dehydrated.push(ptr);
        }
        ptr
    }

    #[inline]
    pub fn index_3_ptrs_not_dehydrated(
        &mut self,
        tag: Tag,
        a: Ptr<F>,
        b: Ptr<F>,
        c: Ptr<F>,
    ) -> Ptr<F> {
        Ptr::Tree3(tag, self.ptrs3.insert_full((a, b, c)).0)
    }

    pub fn index_4_ptrs(&mut self, tag: Tag, a: Ptr<F>, b: Ptr<F>, c: Ptr<F>, d: Ptr<F>) -> Ptr<F> {
        let (idx, inserted) = self.ptrs4.insert_full((a, b, c, d));
        let ptr = Ptr::Tree4(tag, idx);
        if inserted {
            self.dehydrated.push(ptr);
        }
        ptr
    }

    #[inline]
    pub fn index_4_ptrs_not_dehydrated(
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

    pub fn index_string(&mut self, s: String) -> Ptr<F> {
        let mut chars = s.chars().rev().collect_vec();
        let mut ptr;
        let mut heads = vec![];
        loop {
            // try a cache hit until no char is left while accumulating the heads
            if chars.is_empty() {
                ptr = Ptr::null(Tag::Str);
                break;
            }
            match self.vec_char_cache.get(&chars) {
                Some(ptr_cache) => {
                    ptr = *ptr_cache;
                    break;
                }
                None => heads.push(chars.pop().unwrap()),
            }
        }
        while let Some(head) = heads.pop() {
            // use the accumulated heads to construct the pointers and populate the cache
            ptr = self.index_2_ptrs(Tag::Str, Ptr::char(head), ptr);
            chars.push(head);
            self.vec_char_cache.insert(chars.clone(), ptr);
        }
        ptr
    }

    pub fn index_symbol_path(&mut self, path: Vec<String>) -> Ptr<F> {
        let mut components = path;
        components.reverse();
        let mut ptr;
        let mut heads = vec![];
        loop {
            // try a cache hit until no char is left while accumulating the heads
            if components.is_empty() {
                ptr = Ptr::null(Tag::Sym);
                break;
            }
            match self.vec_str_cache.get(&components) {
                Some(ptr_cache) => {
                    ptr = *ptr_cache;
                    break;
                }
                None => heads.push(components.pop().unwrap()),
            }
        }
        while let Some(head) = heads.pop() {
            // use the accumulated heads to construct the pointers and populate the cache
            let head_ptr = self.index_string(head.clone());
            ptr = self.index_2_ptrs(Tag::Sym, head_ptr, ptr);
            components.push(head);
            self.vec_str_cache.insert(components.clone(), ptr);
        }
        ptr
    }

    pub fn index_symbol(&mut self, s: Symbol) -> Ptr<F> {
        match s {
            Symbol::Sym(path) => self.index_symbol_path(path),
            Symbol::Key(path) => self.index_symbol_path(path).sym_to_key(),
        }
    }

    pub fn hydrate_ptr(&self, ptr: &Ptr<F>) -> Result<AquaPtr<F>, String> {
        match ptr {
            Ptr::Leaf(Tag::Comm, hash) => match self.aqua_cache.get(ptr) {
                Some(aqua_ptr) => Ok(*aqua_ptr),
                None => {
                    let Some((secret, ptr)) = self.comms.get(&FWrap(*hash)) else {
                            return Err(format!("Hash {} not found", hash.hex_digits()))
                        };
                    let aqua_ptr = AquaPtr {
                        tag: Tag::Comm,
                        val: *hash,
                    };
                    self.aqua_dag
                        .insert(aqua_ptr, AquaPtrKind::Comm(*secret, self.hydrate_ptr(ptr)?));
                    self.aqua_cache.insert(*ptr, aqua_ptr);
                    Ok(aqua_ptr)
                }
            },
            Ptr::Leaf(tag, x) => Ok(AquaPtr { tag: *tag, val: *x }),
            Ptr::Tree2(tag, idx) => match self.aqua_cache.get(ptr) {
                Some(aqua_ptr) => Ok(*aqua_ptr),
                None => {
                    let Some((a, b)) = self.ptrs2.get_index(*idx) else {
                            return Err(format!("Index {idx} not found on ptrs2"))
                        };
                    let a = self.hydrate_ptr(a)?;
                    let b = self.hydrate_ptr(b)?;
                    let aqua_ptr = AquaPtr {
                        tag: *tag,
                        val: self.poseidon_cache.hash4(&[
                            a.tag.field(),
                            a.val,
                            b.tag.field(),
                            b.val,
                        ]),
                    };
                    self.aqua_dag.insert(aqua_ptr, AquaPtrKind::Tree2(a, b));
                    self.aqua_cache.insert(*ptr, aqua_ptr);
                    Ok(aqua_ptr)
                }
            },
            Ptr::Tree3(tag, idx) => match self.aqua_cache.get(ptr) {
                Some(aqua_ptr) => Ok(*aqua_ptr),
                None => {
                    let Some((a, b, c)) = self.ptrs3.get_index(*idx) else {
                            return Err(format!("Index {idx} not found on ptrs3"))
                        };
                    let a = self.hydrate_ptr(a)?;
                    let b = self.hydrate_ptr(b)?;
                    let c = self.hydrate_ptr(c)?;
                    let aqua_ptr = AquaPtr {
                        tag: *tag,
                        val: self.poseidon_cache.hash6(&[
                            a.tag.field(),
                            a.val,
                            b.tag.field(),
                            b.val,
                            c.tag.field(),
                            c.val,
                        ]),
                    };
                    self.aqua_dag.insert(aqua_ptr, AquaPtrKind::Tree3(a, b, c));
                    self.aqua_cache.insert(*ptr, aqua_ptr);
                    Ok(aqua_ptr)
                }
            },
            Ptr::Tree4(tag, idx) => match self.aqua_cache.get(ptr) {
                Some(aqua_ptr) => Ok(*aqua_ptr),
                None => {
                    let Some((a, b, c, d)) = self.ptrs4.get_index(*idx) else {
                            return Err(format!("Index {idx} not found on ptrs4"))
                        };
                    let a = self.hydrate_ptr(a)?;
                    let b = self.hydrate_ptr(b)?;
                    let c = self.hydrate_ptr(c)?;
                    let d = self.hydrate_ptr(d)?;
                    let aqua_ptr = AquaPtr {
                        tag: *tag,
                        val: self.poseidon_cache.hash8(&[
                            a.tag.field(),
                            a.val,
                            b.tag.field(),
                            b.val,
                            c.tag.field(),
                            c.val,
                            d.tag.field(),
                            d.val,
                        ]),
                    };
                    self.aqua_dag
                        .insert(aqua_ptr, AquaPtrKind::Tree4(a, b, c, d));
                    self.aqua_cache.insert(*ptr, aqua_ptr);
                    Ok(aqua_ptr)
                }
            },
        }
    }

    pub fn deluge(&mut self) {
        self.dehydrated.par_iter().for_each(|ptr| {
            self.hydrate_ptr(ptr).expect("failed to hydrate pointer");
        });
        self.dehydrated = Vec::new();
    }
}
