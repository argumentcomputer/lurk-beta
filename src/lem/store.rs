use std::collections::HashMap;

use indexmap::IndexSet;
use itertools::Itertools;

use crate::lem::{pointers::PtrVal, tag::Tag};

use super::pointers::Ptr;

pub struct Store {
    pub ptr2_store: IndexSet<(Ptr, Ptr)>,
    pub ptr3_store: IndexSet<(Ptr, Ptr, Ptr)>,
    pub ptr4_store: IndexSet<(Ptr, Ptr, Ptr, Ptr)>,

    vec_char_cache: HashMap<Vec<char>, Ptr>,
}

impl Store {
    pub fn put_string(&mut self, s: String) -> Ptr {
        let mut chars = s.chars().rev().collect_vec();
        let mut ptr;
        let mut heads: Vec<char> = Vec::default();
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
            let (idx, _) = self.ptr2_store.insert_full((
                Ptr {
                    tag: Tag::Char,
                    val: PtrVal::Char(head),
                },
                ptr,
            ));
            ptr = Ptr {
                tag: Tag::Str,
                val: PtrVal::Idx(idx),
            };
            chars.push(head);
            self.vec_char_cache.insert(chars.clone(), ptr);
        }
        ptr
    }
}
