use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap};

use crate::field::{FWrap, LurkField};

use super::{
    pointers::{Ptr, ZChildren, ZPtr},
    store::Store,
};

#[derive(Default)]
pub struct ZStore<F: LurkField> {
    dag: BTreeMap<ZPtr<F>, ZChildren<F>>,
    comms: HashMap<FWrap<F>, (F, ZPtr<F>)>, // hash -> (secret, src)
    z_cache: HashMap<Ptr<F>, ZPtr<F>>,
}

impl<F: LurkField + Serialize> Serialize for ZStore<F> {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        Serialize::serialize(&(&self.dag, &self.comms), serializer)
    }
}

impl<'a, F: LurkField + Deserialize<'a>> Deserialize<'a> for ZStore<F> {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: serde::Deserializer<'a>,
    {
        let (dag, comms) = Deserialize::deserialize(deserializer)?;
        let z_cache = HashMap::default();
        Ok(Self {
            dag,
            comms,
            z_cache,
        })
    }
}

impl<F: LurkField> ZStore<F> {
    pub fn populate(&mut self, ptr: &Ptr<F>, store: &Store<F>) -> Result<ZPtr<F>> {
        match self.z_cache.get(ptr) {
            Some(z_ptr) => Ok(*z_ptr),
            None => {
                let z_ptr = match ptr {
                    Ptr::Leaf(tag, f) => {
                        let z_ptr = ZPtr {
                            tag: *tag,
                            hash: *f,
                        };
                        self.dag.insert(z_ptr, ZChildren::Leaf);
                        z_ptr
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
                        self.dag.insert(z_ptr, ZChildren::Tuple2(a, b));
                        z_ptr
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
                        self.dag.insert(z_ptr, ZChildren::Tuple3(a, b, c));
                        z_ptr
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
                        self.dag.insert(z_ptr, ZChildren::Tuple4(a, b, c, d));
                        z_ptr
                    }
                };
                self.z_cache.insert(*ptr, z_ptr);
                Ok(z_ptr)
            }
        }
    }

    #[inline]
    pub fn add_comm(&mut self, hash: F, secret: F, payload: ZPtr<F>) {
        self.comms.insert(FWrap(hash), (secret, payload));
    }
}
