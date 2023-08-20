use anyhow::{bail, Result};
use std::collections::BTreeMap;

use crate::field::LurkField;

use super::{
    pointers::{Ptr, ZChildren, ZPtr},
    store::Store,
};

pub struct ZStore<F: LurkField>(BTreeMap<ZPtr<F>, ZChildren<F>>);

impl<F: LurkField> ZStore<F> {
    pub fn populate(&mut self, ptr: &Ptr<F>, store: &Store<F>) -> Result<ZPtr<F>> {
        match ptr {
            Ptr::Leaf(tag, f) => {
                let z_ptr = ZPtr {
                    tag: *tag,
                    hash: *f,
                };
                self.0.insert(z_ptr, ZChildren::Leaf);
                Ok(z_ptr)
            }
            Ptr::Tuple2(tag, idx) => {
                let Some((a, b)) = store.fetch_2_ptrs(*idx) else {
                    bail!("Index {idx} not found on tuple2")
                };
                let a = self.populate(a, store)?;
                let b = self.populate(b, store)?;
                let z_ptr = ZPtr {
                    tag: *tag,
                    hash: store.poseidon_cache.hash4(&[
                        a.tag.to_field(),
                        a.hash,
                        b.tag.to_field(),
                        b.hash,
                    ]),
                };
                self.0.insert(z_ptr, ZChildren::Tuple2(a, b));
                Ok(z_ptr)
            }
            Ptr::Tuple3(tag, idx) => {
                let Some((a, b, c)) = store.fetch_3_ptrs(*idx) else {
                    bail!("Index {idx} not found on tuple3")
                };
                let a = self.populate(a, store)?;
                let b = self.populate(b, store)?;
                let c = self.populate(c, store)?;
                let z_ptr = ZPtr {
                    tag: *tag,
                    hash: store.poseidon_cache.hash6(&[
                        a.tag.to_field(),
                        a.hash,
                        b.tag.to_field(),
                        b.hash,
                        c.tag.to_field(),
                        c.hash,
                    ]),
                };
                self.0.insert(z_ptr, ZChildren::Tuple3(a, b, c));
                Ok(z_ptr)
            }
            Ptr::Tuple4(tag, idx) => {
                let Some((a, b, c, d)) = store.fetch_4_ptrs(*idx) else {
                    bail!("Index {idx} not found on tuple4")
                };
                let a = self.populate(a, store)?;
                let b = self.populate(b, store)?;
                let c = self.populate(c, store)?;
                let d = self.populate(d, store)?;
                let z_ptr = ZPtr {
                    tag: *tag,
                    hash: store.poseidon_cache.hash8(&[
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
                self.0.insert(z_ptr, ZChildren::Tuple4(a, b, c, d));
                Ok(z_ptr)
            }
        }
    }
}
