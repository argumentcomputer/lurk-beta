use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::{
    field::{FWrap, LurkField},
    lem::{
        pointers::{Ptr, ZPtr},
        store::Store,
    },
};

use super::field_data::HasFieldModulus;

/// `ZPtrType` holds information about the `Ptr` that originated a certain `ZPtr`.
/// If the `Ptr` was not atomic, `ZPtrType` can refer to its children once they
/// have already been turned into `ZPtr`s.
#[derive(Debug, Serialize, Deserialize)]
pub(crate) enum ZPtrType<F: LurkField> {
    Atom,
    Tuple2(ZPtr<F>, ZPtr<F>),
    Tuple3(ZPtr<F>, ZPtr<F>, ZPtr<F>),
    Tuple4(ZPtr<F>, ZPtr<F>, ZPtr<F>, ZPtr<F>),
}

/// Holds a mapping from `ZPtr`s to their `ZPtrType`s
#[derive(Debug, Default, Serialize, Deserialize)]
pub(crate) struct ZDag<F: LurkField>(BTreeMap<ZPtr<F>, ZPtrType<F>>);

impl<F: LurkField> ZDag<F> {
    pub(crate) fn populate_with(
        &mut self,
        ptr: &Ptr<F>,
        store: &Store<F>,
        cache: &mut HashMap<Ptr<F>, ZPtr<F>>,
    ) -> ZPtr<F> {
        let mut recurse = |ptr: &Ptr<F>| -> ZPtr<F> {
            if let Some(z_ptr) = cache.get(ptr) {
                *z_ptr
            } else {
                let z_ptr = match ptr {
                    Ptr::Atom(tag, f) => {
                        let z_ptr = ZPtr::from_parts(*tag, *f);
                        self.0.insert(z_ptr, ZPtrType::Atom);
                        z_ptr
                    }
                    Ptr::Tuple2(tag, idx) => {
                        let (a, b) = store.expect_2_ptrs(*idx);
                        let a = self.populate_with(a, store, cache);
                        let b = self.populate_with(b, store, cache);
                        let z_ptr = ZPtr::from_parts(
                            *tag,
                            store.poseidon_cache.hash4(&[
                                a.tag_field(),
                                *a.value(),
                                b.tag_field(),
                                *b.value(),
                            ]),
                        );
                        self.0.insert(z_ptr, ZPtrType::Tuple2(a, b));
                        z_ptr
                    }
                    Ptr::Tuple3(tag, idx) => {
                        let (a, b, c) = store.expect_3_ptrs(*idx);
                        let a = self.populate_with(a, store, cache);
                        let b = self.populate_with(b, store, cache);
                        let c = self.populate_with(c, store, cache);
                        let z_ptr = ZPtr::from_parts(
                            *tag,
                            store.poseidon_cache.hash6(&[
                                a.tag_field(),
                                *a.value(),
                                b.tag_field(),
                                *b.value(),
                                c.tag_field(),
                                *c.value(),
                            ]),
                        );
                        self.0.insert(z_ptr, ZPtrType::Tuple3(a, b, c));
                        z_ptr
                    }
                    Ptr::Tuple4(tag, idx) => {
                        let (a, b, c, d) = store.expect_4_ptrs(*idx);
                        let a = self.populate_with(a, store, cache);
                        let b = self.populate_with(b, store, cache);
                        let c = self.populate_with(c, store, cache);
                        let d = self.populate_with(d, store, cache);
                        let z_ptr = ZPtr::from_parts(
                            *tag,
                            store.poseidon_cache.hash8(&[
                                a.tag_field(),
                                *a.value(),
                                b.tag_field(),
                                *b.value(),
                                c.tag_field(),
                                *c.value(),
                                d.tag_field(),
                                *d.value(),
                            ]),
                        );
                        self.0.insert(z_ptr, ZPtrType::Tuple4(a, b, c, d));
                        z_ptr
                    }
                };
                cache.insert(*ptr, z_ptr);
                z_ptr
            }
        };
        recurse(ptr)
    }

    fn get_type(&self, z_ptr: &ZPtr<F>) -> Option<&ZPtrType<F>> {
        self.0.get(z_ptr)
    }

    pub(crate) fn populate_store(
        &self,
        z_ptr: &ZPtr<F>,
        store: &Store<F>,
        cache: &mut HashMap<ZPtr<F>, Ptr<F>>,
    ) -> Result<Ptr<F>> {
        let mut recurse = |z_ptr: &ZPtr<F>| -> Result<Ptr<F>> {
            if let Some(z_ptr) = cache.get(z_ptr) {
                Ok(*z_ptr)
            } else {
                let ptr = match self.get_type(z_ptr) {
                    None => bail!("Couldn't find ZPtr on ZStore"),
                    Some(ZPtrType::Atom) => Ptr::Atom(*z_ptr.tag(), *z_ptr.value()),
                    Some(ZPtrType::Tuple2(z1, z2)) => {
                        let ptr1 = self.populate_store(z1, store, cache)?;
                        let ptr2 = self.populate_store(z2, store, cache)?;
                        store.intern_2_ptrs_hydrated(*z_ptr.tag(), ptr1, ptr2, *z_ptr)
                    }
                    Some(ZPtrType::Tuple3(z1, z2, z3)) => {
                        let ptr1 = self.populate_store(z1, store, cache)?;
                        let ptr2 = self.populate_store(z2, store, cache)?;
                        let ptr3 = self.populate_store(z3, store, cache)?;
                        store.intern_3_ptrs_hydrated(*z_ptr.tag(), ptr1, ptr2, ptr3, *z_ptr)
                    }
                    Some(ZPtrType::Tuple4(z1, z2, z3, z4)) => {
                        let ptr1 = self.populate_store(z1, store, cache)?;
                        let ptr2 = self.populate_store(z2, store, cache)?;
                        let ptr3 = self.populate_store(z3, store, cache)?;
                        let ptr4 = self.populate_store(z4, store, cache)?;
                        store.intern_4_ptrs_hydrated(*z_ptr.tag(), ptr1, ptr2, ptr3, ptr4, *z_ptr)
                    }
                };
                cache.insert(*z_ptr, ptr);
                Ok(ptr)
            }
        };
        recurse(z_ptr)
    }

    /// Populates a `ZDag` with data from self
    pub(crate) fn populate_z_dag(
        &self,
        z_ptr: &ZPtr<F>,
        z_dag: &mut ZDag<F>,
        cache: &mut HashSet<ZPtr<F>>,
    ) -> Result<()> {
        let mut recurse = |z_ptr: &ZPtr<F>| -> Result<()> {
            if !cache.contains(z_ptr) {
                match self.get_type(z_ptr) {
                    None => bail!("Couldn't find ZPtr on ZStore"),
                    Some(ZPtrType::Atom) => {
                        z_dag.0.insert(*z_ptr, ZPtrType::Atom);
                    }
                    Some(ZPtrType::Tuple2(z1, z2)) => {
                        self.populate_z_dag(z1, z_dag, cache)?;
                        self.populate_z_dag(z2, z_dag, cache)?;
                        z_dag.0.insert(*z_ptr, ZPtrType::Tuple2(*z1, *z2));
                    }
                    Some(ZPtrType::Tuple3(z1, z2, z3)) => {
                        self.populate_z_dag(z1, z_dag, cache)?;
                        self.populate_z_dag(z2, z_dag, cache)?;
                        self.populate_z_dag(z3, z_dag, cache)?;
                        z_dag.0.insert(*z_ptr, ZPtrType::Tuple3(*z1, *z2, *z3));
                    }
                    Some(ZPtrType::Tuple4(z1, z2, z3, z4)) => {
                        self.populate_z_dag(z1, z_dag, cache)?;
                        self.populate_z_dag(z2, z_dag, cache)?;
                        self.populate_z_dag(z3, z_dag, cache)?;
                        self.populate_z_dag(z4, z_dag, cache)?;
                        z_dag.0.insert(*z_ptr, ZPtrType::Tuple4(*z1, *z2, *z3, *z4));
                    }
                };
                cache.insert(*z_ptr);
            }
            Ok(())
        };
        recurse(z_ptr)
    }

    pub(crate) fn filtered(&self, z_ptrs: &[&ZPtr<F>]) -> Result<Self> {
        let mut z_dag_new = ZDag::default();
        let mut cache = HashSet::default();
        for z_ptr in z_ptrs {
            self.populate_z_dag(z_ptr, &mut z_dag_new, &mut cache)?;
        }
        Ok(z_dag_new)
    }
}

/// A `ZStore` is a stable IO format for `Store`, without index-based references
#[derive(Debug, Default, Serialize, Deserialize)]
pub(crate) struct ZStore<F: LurkField> {
    z_dag: ZDag<F>,
    comms: BTreeMap<FWrap<F>, (F, ZPtr<F>)>,
}

impl<F: LurkField> HasFieldModulus for ZStore<F> {
    fn field_modulus() -> String {
        F::MODULUS.to_owned()
    }
}

impl<F: LurkField> ZStore<F> {
    #[inline]
    pub(crate) fn add_comm(&mut self, hash: F, secret: F, payload: ZPtr<F>) {
        self.comms.insert(FWrap(hash), (secret, payload));
    }

    #[inline]
    pub(crate) fn open(&self, hash: F) -> Option<&(F, ZPtr<F>)> {
        self.comms.get(&FWrap(hash))
    }

    pub(crate) fn to_store(&self) -> Result<Store<F>> {
        let store = Store::default();
        let mut cache = HashMap::default();
        for z_ptr in self.z_dag.0.keys() {
            self.populate_store(z_ptr, &store, &mut cache)?;
        }
        for (hash, (secret, z_payload)) in &self.comms {
            let payload = self.populate_store(z_payload, &store, &mut cache)?;
            store.add_comm(hash.0, *secret, payload);
        }
        Ok(store)
    }

    #[inline]
    pub(crate) fn populate_with(
        &mut self,
        ptr: &Ptr<F>,
        store: &Store<F>,
        cache: &mut HashMap<Ptr<F>, ZPtr<F>>,
    ) -> ZPtr<F> {
        self.z_dag.populate_with(ptr, store, cache)
    }

    pub(crate) fn populate_store(
        &self,
        z_ptr: &ZPtr<F>,
        store: &Store<F>,
        cache: &mut HashMap<ZPtr<F>, Ptr<F>>,
    ) -> Result<Ptr<F>> {
        self.z_dag.populate_store(z_ptr, store, cache)
    }
}
