use std::collections::HashMap;

use indexmap::IndexSet;
use itertools::Itertools;

use crate::{field::LurkField, lem::tag::Tag};

use super::{
    pointers::{AquaPtr, Ptr},
    symbol::Symbol,
};

#[derive(Default)]
pub struct Store<F: LurkField> {
    pub data2: IndexSet<(Ptr<F>, Ptr<F>)>,
    pub data3: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>)>,
    pub data4: IndexSet<(Ptr<F>, Ptr<F>, Ptr<F>, Ptr<F>)>,

    vec_char_cache: HashMap<Vec<char>, Ptr<F>>,
    vec_str_cache: HashMap<Vec<String>, Ptr<F>>,
}

impl<F: LurkField + std::hash::Hash> Store<F> {
    pub fn index_string(&mut self, s: String) -> Ptr<F> {
        let mut chars = s.chars().rev().collect_vec();
        let mut ptr;
        let mut heads = vec![];
        loop {
            // try a cache hit until no char is left while accumulating the heads
            if chars.is_empty() {
                ptr = Ptr::Indexed(Tag::Str, None);
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
            let (idx, _) = self.data2.insert_full((Ptr::Char(head), ptr));
            ptr = Ptr::Indexed(Tag::Str, Some(idx));
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
                ptr = Ptr::Indexed(Tag::Sym, None);
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
            let (idx, _) = self.data2.insert_full((head_ptr, ptr));
            ptr = Ptr::Indexed(Tag::Sym, Some(idx));
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

    pub fn hydrate_ptr(&mut self, _ptr: Ptr<F>) -> AquaPtr<F> {
        todo!()
    }
}
