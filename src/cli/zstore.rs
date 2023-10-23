use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap};

use crate::{
    field::{FWrap, LurkField},
    lem::{
        pointers::{Ptr, ZChildren, ZPtr},
        store::Store,
        Tag,
    },
    tag::ContTag::{Dummy, Error, Outermost, Terminal},
};

use super::field_data::HasFieldModulus;

#[derive(Debug, Default, Serialize, Deserialize)]
pub(crate) struct ZStore<F: LurkField> {
    dag: BTreeMap<ZPtr<F>, ZChildren<F>>,
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

    #[inline]
    pub(crate) fn get_children(&self, z_ptr: &ZPtr<F>) -> Option<&ZChildren<F>> {
        self.dag.get(z_ptr)
    }

    pub(crate) fn to_store(&self) -> Result<Store<F>> {
        let store = Store::default();
        let mut cache = HashMap::default();
        for z_ptr in self.dag.keys() {
            populate_store(&store, z_ptr, self, &mut cache)?;
        }
        for (hash, (secret, z_payload)) in &self.comms {
            let payload = populate_store(&store, z_payload, self, &mut cache)?;
            store.add_comm(hash.0, *secret, payload);
        }
        Ok(store)
    }
}

pub(crate) fn populate_z_store<F: LurkField>(
    z_store: &mut ZStore<F>,
    ptr: &Ptr<F>,
    store: &Store<F>,
    cache: &mut HashMap<Ptr<F>, ZPtr<F>>,
) -> Result<ZPtr<F>> {
    let mut recurse = |ptr: &Ptr<F>| -> Result<ZPtr<F>> {
        if let Some(z_ptr) = cache.get(ptr) {
            Ok(*z_ptr)
        } else {
            let z_ptr = match ptr {
                Ptr::Atom(tag, f) => {
                    let z_ptr = match tag {
                        Tag::Cont(Outermost | Error | Dummy | Terminal) => {
                            // temporary shim for compatibility with Lurk Alpha
                            ZPtr::from_parts(*tag, store.poseidon_cache.hash8(&[F::ZERO; 8]))
                        }
                        _ => ZPtr::from_parts(*tag, *f),
                    };
                    z_store.dag.insert(z_ptr, ZChildren::Atom);
                    z_ptr
                }
                Ptr::Tuple2(tag, idx) => {
                    let Some((a, b)) = store.fetch_2_ptrs(*idx) else {
                        bail!("Index {idx} not found on tuple2")
                    };
                    let a = populate_z_store(z_store, a, store, cache)?;
                    let b = populate_z_store(z_store, b, store, cache)?;
                    let z_ptr = ZPtr::from_parts(
                        *tag,
                        store.poseidon_cache.hash4(&[
                            a.tag_field(),
                            *a.value(),
                            b.tag_field(),
                            *b.value(),
                        ]),
                    );
                    z_store.dag.insert(z_ptr, ZChildren::Tuple2(a, b));
                    z_ptr
                }
                Ptr::Tuple3(tag, idx) => {
                    let Some((a, b, c)) = store.fetch_3_ptrs(*idx) else {
                        bail!("Index {idx} not found on tuple3")
                    };
                    let a = populate_z_store(z_store, a, store, cache)?;
                    let b = populate_z_store(z_store, b, store, cache)?;
                    let c = populate_z_store(z_store, c, store, cache)?;
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
                    z_store.dag.insert(z_ptr, ZChildren::Tuple3(a, b, c));
                    z_ptr
                }
                Ptr::Tuple4(tag, idx) => {
                    let Some((a, b, c, d)) = store.fetch_4_ptrs(*idx) else {
                        bail!("Index {idx} not found on tuple4")
                    };
                    let a = populate_z_store(z_store, a, store, cache)?;
                    let b = populate_z_store(z_store, b, store, cache)?;
                    let c = populate_z_store(z_store, c, store, cache)?;
                    let d = populate_z_store(z_store, d, store, cache)?;
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
                    z_store.dag.insert(z_ptr, ZChildren::Tuple4(a, b, c, d));
                    z_ptr
                }
            };
            cache.insert(*ptr, z_ptr);
            Ok(z_ptr)
        }
    };
    recurse(ptr)
}

pub(crate) fn populate_store<F: LurkField>(
    store: &Store<F>,
    z_ptr: &ZPtr<F>,
    z_store: &ZStore<F>,
    cache: &mut HashMap<ZPtr<F>, Ptr<F>>,
) -> Result<Ptr<F>> {
    let mut recurse = |z_ptr: &ZPtr<F>| -> Result<Ptr<F>> {
        if let Some(z_ptr) = cache.get(z_ptr) {
            Ok(*z_ptr)
        } else {
            let ptr = match z_store.get_children(z_ptr) {
                None => bail!("Couldn't find ZPtr"),
                Some(ZChildren::Atom) => Ptr::Atom(z_ptr.tag(), *z_ptr.value()),
                Some(ZChildren::Tuple2(z1, z2)) => {
                    let ptr1 = populate_store(store, z1, z_store, cache)?;
                    let ptr2 = populate_store(store, z2, z_store, cache)?;
                    store.intern_2_ptrs_hydrated(z_ptr.tag(), ptr1, ptr2, *z_ptr)
                }
                Some(ZChildren::Tuple3(z1, z2, z3)) => {
                    let ptr1 = populate_store(store, z1, z_store, cache)?;
                    let ptr2 = populate_store(store, z2, z_store, cache)?;
                    let ptr3 = populate_store(store, z3, z_store, cache)?;
                    store.intern_3_ptrs_hydrated(z_ptr.tag(), ptr1, ptr2, ptr3, *z_ptr)
                }
                Some(ZChildren::Tuple4(z1, z2, z3, z4)) => {
                    let ptr1 = populate_store(store, z1, z_store, cache)?;
                    let ptr2 = populate_store(store, z2, z_store, cache)?;
                    let ptr3 = populate_store(store, z3, z_store, cache)?;
                    let ptr4 = populate_store(store, z4, z_store, cache)?;
                    store.intern_4_ptrs_hydrated(z_ptr.tag(), ptr1, ptr2, ptr3, ptr4, *z_ptr)
                }
            };
            cache.insert(*z_ptr, ptr);
            Ok(ptr)
        }
    };
    recurse(z_ptr)
}
