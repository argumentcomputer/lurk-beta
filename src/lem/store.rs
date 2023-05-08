use std::collections::HashMap;

use indexmap::IndexSet;
use itertools::Itertools;

use crate::{field::LurkField, lem::tag::Tag};

use super::{
    pointers::{AquaPtr, LurkData},
    symbol::Symbol,
};

pub struct Store<F: LurkField> {
    pub data2: IndexSet<(LurkData<F>, LurkData<F>)>,
    pub data3: IndexSet<(LurkData<F>, LurkData<F>, LurkData<F>)>,
    pub data4: IndexSet<(LurkData<F>, LurkData<F>, LurkData<F>, LurkData<F>)>,

    vec_char_cache: HashMap<Vec<char>, LurkData<F>>,
    vec_str_cache: HashMap<Vec<String>, LurkData<F>>,
}

impl<F: LurkField + std::hash::Hash> Store<F> {
    pub fn index_string(&mut self, s: String) -> LurkData<F> {
        let mut chars = s.chars().rev().collect_vec();
        let mut ptr;
        let mut heads = vec![];
        loop {
            // try a cache hit until no char is left while accumulating the heads
            if chars.is_empty() {
                ptr = LurkData::Tag(Tag::Str);
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
            let (idx, _) = self.data2.insert_full((LurkData::Char(head), ptr));
            ptr = LurkData::Ptr(Tag::Str, idx);
            chars.push(head);
            self.vec_char_cache.insert(chars.clone(), ptr);
        }
        ptr
    }

    pub fn index_symbol_path(&mut self, path: Vec<String>) -> LurkData<F> {
        let mut components = path.clone();
        components.reverse();
        let mut ptr;
        let mut heads = vec![];
        loop {
            // try a cache hit until no char is left while accumulating the heads
            if components.is_empty() {
                ptr = LurkData::Tag(Tag::Sym);
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
            ptr = LurkData::Ptr(Tag::Sym, idx);
            components.push(head);
            self.vec_str_cache.insert(components.clone(), ptr);
        }
        ptr
    }

    pub fn index_symbol(&mut self, s: Symbol) -> LurkData<F> {
        match s {
            Symbol::Sym(path) => self.index_symbol_path(path),
            Symbol::Key(path) => self.index_symbol_path(path).try_sym_to_key_ptr(),
        }
    }

    pub fn hydrate_ptr(&mut self, _ptr: LurkData<F>) -> AquaPtr<F> {
        todo!()
    }
}
