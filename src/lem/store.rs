use std::collections::HashMap;

use indexmap::IndexSet;
use itertools::Itertools;

use crate::{
    field::{FWrap, LurkField},
    hash::PoseidonCache,
    lem::tag::Tag,
};

use super::{
    pointers::{AquaPtr, Ptr, PtrVal},
    symbol::Symbol,
};

#[derive(Default)]
pub struct Store<F: LurkField> {
    pub comms: IndexSet<(FWrap<F>, FWrap<F>, Ptr<F>)>, // hash, secret, src
    pub ptrs2: IndexSet<(Ptr<F>, Ptr<F>)>,
    pub ptrs3: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>)>,
    pub ptrs4: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>, Ptr<F>)>,

    vec_char_cache: HashMap<Vec<char>, Ptr<F>>,
    vec_str_cache: HashMap<Vec<String>, Ptr<F>>,

    pub poseidon_cache: PoseidonCache<F>,
}

impl<F: LurkField> Store<F> {
    pub fn index_string(&mut self, s: String) -> Ptr<F> {
        let mut chars = s.chars().rev().collect_vec();
        let mut ptr;
        let mut heads = vec![];
        loop {
            // try a cache hit until no char is left while accumulating the heads
            if chars.is_empty() {
                ptr = Ptr {
                    tag: Tag::Str,
                    val: PtrVal::Null,
                };
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
            let (idx, _) = self.ptrs2.insert_full((
                Ptr {
                    tag: Tag::Char,
                    val: PtrVal::Null,
                },
                ptr,
            ));
            ptr = Ptr {
                tag: Tag::Str,
                val: PtrVal::Index2(idx),
            };
            chars.push(head);
            self.vec_char_cache.insert(chars.clone(), ptr);
        }
        ptr
    }

    pub fn index_symbol_path(&mut self, path: Vec<String>) -> Ptr<F> {
        let mut components = path.clone();
        components.reverse();
        let mut ptr;
        let mut heads = vec![];
        loop {
            // try a cache hit until no char is left while accumulating the heads
            if components.is_empty() {
                ptr = Ptr {
                    tag: Tag::Sym,
                    val: PtrVal::Null,
                };
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
            let (idx, _) = self.ptrs2.insert_full((head_ptr, ptr));
            ptr = Ptr {
                tag: Tag::Sym,
                val: PtrVal::Index2(idx),
            };
            components.push(head);
            self.vec_str_cache.insert(components.clone(), ptr);
        }
        ptr
    }

    pub fn index_symbol(&mut self, s: Symbol) -> Ptr<F> {
        match s {
            Symbol::Sym(path) => self.index_symbol_path(path),
            Symbol::Key(path) => self.index_symbol_path(path).key_ptr_if_sym_ptr(),
        }
    }

    // TODO: this function can be even faster if `AquaPtr` implements `Copy`
    pub fn hydrate_ptr(&self, ptr: &Ptr<F>) -> Result<AquaPtr<F>, &str> {
        match (ptr.tag, ptr.val) {
            (Tag::Char, PtrVal::Char(x)) => Ok(AquaPtr::Leaf(Tag::Char, F::from_char(x))),
            (Tag::U64, PtrVal::U64(x)) => Ok(AquaPtr::Leaf(Tag::Char, F::from_u64(x))),
            (Tag::Num, PtrVal::Num(x)) => Ok(AquaPtr::Leaf(Tag::Num, x)),
            (tag, PtrVal::Null) => Ok(AquaPtr::Leaf(tag, F::zero())),
            (tag, PtrVal::Index2(idx)) => {
                // TODO: how to cache this?
                let Some((a, b)) = self.ptrs2.get_index(idx) else {
                    return Err("Index not found on ptrs2")
                };
                let a = self.hydrate_ptr(a)?;
                let b = self.hydrate_ptr(b)?;
                let (a_tag_f, a_val_f) = a.tag_val_fields();
                let (b_tag_f, b_val_f) = b.tag_val_fields();
                Ok(AquaPtr::Tree2(
                    tag,
                    self.poseidon_cache
                        .hash4(&[a_tag_f, a_val_f, b_tag_f, b_val_f]),
                    Box::new((a, b)),
                ))
            }
            (tag, PtrVal::Index3(idx)) => {
                // TODO: how to cache this?
                let Some((a, b, c)) = self.ptrs3.get_index(idx) else {
                    return Err("Index not found on ptrs3")
                };
                let a = self.hydrate_ptr(a)?;
                let b = self.hydrate_ptr(b)?;
                let c = self.hydrate_ptr(c)?;
                let (a_tag_f, a_val_f) = a.tag_val_fields();
                let (b_tag_f, b_val_f) = b.tag_val_fields();
                let (c_tag_f, c_val_f) = c.tag_val_fields();
                Ok(AquaPtr::Tree3(
                    tag,
                    self.poseidon_cache
                        .hash6(&[a_tag_f, a_val_f, b_tag_f, b_val_f, c_tag_f, c_val_f]),
                    Box::new((a, b, c)),
                ))
            }
            (tag, PtrVal::Index4(idx)) => {
                // TODO: how to cache this?
                let Some((a, b, c, d)) = self.ptrs4.get_index(idx) else {
                    return Err("Index not found on ptrs4")
                };
                let a = self.hydrate_ptr(a)?;
                let b = self.hydrate_ptr(b)?;
                let c = self.hydrate_ptr(c)?;
                let d = self.hydrate_ptr(d)?;
                let (a_tag_f, a_val_f) = a.tag_val_fields();
                let (b_tag_f, b_val_f) = b.tag_val_fields();
                let (c_tag_f, c_val_f) = c.tag_val_fields();
                let (d_tag_f, d_val_f) = d.tag_val_fields();
                Ok(AquaPtr::Tree4(
                    tag,
                    self.poseidon_cache.hash8(&[
                        a_tag_f, a_val_f, b_tag_f, b_val_f, c_tag_f, c_val_f, d_tag_f, d_val_f,
                    ]),
                    Box::new((a, b, c, d)),
                ))
            }
            (Tag::Comm, PtrVal::Comm(idx)) => {
                let Some((hash, secret, ptr)) = self.comms.get_index(idx) else {
                    return Err("Index not found on ptrs4")
                };
                let ptr = self.hydrate_ptr(ptr)?;
                Ok(AquaPtr::Comm(hash.0, secret.0, Box::new(ptr)))
            }
            _ => Err("Invalid tag/val combination"),
        }
    }
}
