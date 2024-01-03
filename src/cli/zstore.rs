use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::{
    field::{FWrap, LurkField},
    lem::{
        pointers::{Ptr, RawPtr, ZPtr},
        store::{expect_ptrs, intern_ptrs_hydrated, Store},
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
        ptr: &Ptr,
        store: &Store<F>,
        cache: &mut HashMap<Ptr, ZPtr<F>>,
    ) -> ZPtr<F> {
        let mut recurse = |ptr: &Ptr| -> ZPtr<F> {
            if let Some(z_ptr) = cache.get(ptr) {
                *z_ptr
            } else {
                let tag = ptr.tag();
                let z_ptr = match ptr.raw() {
                    RawPtr::Atom(idx) => {
                        let f = store.expect_f(*idx);
                        let z_ptr = ZPtr::from_parts(*tag, *f);
                        self.0.insert(z_ptr, ZPtrType::Atom);
                        z_ptr
                    }
                    RawPtr::Hash4(idx) => {
                        let [a, b] = expect_ptrs!(store, 2, *idx);
                        let a = self.populate_with(&a, store, cache);
                        let b = self.populate_with(&b, store, cache);
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
                    RawPtr::Hash6(idx) => {
                        let [a, b, c] = expect_ptrs!(store, 3, *idx);
                        let a = self.populate_with(&a, store, cache);
                        let b = self.populate_with(&b, store, cache);
                        let c = self.populate_with(&c, store, cache);
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
                    RawPtr::Hash8(idx) => {
                        let [a, b, c, d] = expect_ptrs!(store, 4, *idx);
                        let a = self.populate_with(&a, store, cache);
                        let b = self.populate_with(&b, store, cache);
                        let c = self.populate_with(&c, store, cache);
                        let d = self.populate_with(&d, store, cache);
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
        cache: &mut HashMap<ZPtr<F>, Ptr>,
    ) -> Result<Ptr> {
        let mut recurse = |z_ptr: &ZPtr<F>| -> Result<Ptr> {
            if let Some(z_ptr) = cache.get(z_ptr) {
                Ok(*z_ptr)
            } else {
                let ptr = match self.get_type(z_ptr) {
                    None => bail!("Couldn't find ZPtr on ZStore"),
                    Some(ZPtrType::Atom) => store.intern_atom(*z_ptr.tag(), *z_ptr.value()),
                    Some(ZPtrType::Tuple2(z1, z2)) => {
                        let ptr1 = self.populate_store(z1, store, cache)?;
                        let ptr2 = self.populate_store(z2, store, cache)?;
                        intern_ptrs_hydrated!(store, *z_ptr.tag(), *z_ptr, ptr1, ptr2)
                    }
                    Some(ZPtrType::Tuple3(z1, z2, z3)) => {
                        let ptr1 = self.populate_store(z1, store, cache)?;
                        let ptr2 = self.populate_store(z2, store, cache)?;
                        let ptr3 = self.populate_store(z3, store, cache)?;
                        intern_ptrs_hydrated!(store, *z_ptr.tag(), *z_ptr, ptr1, ptr2, ptr3)
                    }
                    Some(ZPtrType::Tuple4(z1, z2, z3, z4)) => {
                        let ptr1 = self.populate_store(z1, store, cache)?;
                        let ptr2 = self.populate_store(z2, store, cache)?;
                        let ptr3 = self.populate_store(z3, store, cache)?;
                        let ptr4 = self.populate_store(z4, store, cache)?;
                        intern_ptrs_hydrated!(store, *z_ptr.tag(), *z_ptr, ptr1, ptr2, ptr3, ptr4)
                    }
                };
                cache.insert(*z_ptr, ptr);
                Ok(ptr)
            }
        };
        recurse(z_ptr)
    }

    /// Populates a `ZDag` with data from self
    #[allow(dead_code)]
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

    /// Returns a `ZDag` containing only enough data to represent the `z_ptrs`,
    /// which must be recoverable from `self`
    #[allow(dead_code)]
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
        ptr: &Ptr,
        store: &Store<F>,
        cache: &mut HashMap<Ptr, ZPtr<F>>,
    ) -> ZPtr<F> {
        self.z_dag.populate_with(ptr, store, cache)
    }

    pub(crate) fn populate_store(
        &self,
        z_ptr: &ZPtr<F>,
        store: &Store<F>,
        cache: &mut HashMap<ZPtr<F>, Ptr>,
    ) -> Result<Ptr> {
        self.z_dag.populate_store(z_ptr, store, cache)
    }
}

#[cfg(test)]
mod tests {
    use pasta_curves::Fp;
    use rand::{rngs::StdRng, Rng};
    use rand_core::SeedableRng;
    use rayon::prelude::{IntoParallelIterator, ParallelIterator};
    use std::collections::HashMap;

    use crate::{
        field::LurkField,
        lem::{
            pointers::Ptr,
            store::{intern_ptrs, Store},
            Tag,
        },
        tag::{ContTag, ExprTag, Op1, Op2},
    };

    use super::{ZDag, ZStore};

    /// helper function that interns random data into a store
    fn rng_interner(rng: &mut StdRng, max_depth: usize, store: &Store<Fp>) -> Ptr {
        let rnd = rng.gen::<u64>();
        let tag = match rnd % 4 {
            0 => Tag::Expr(ExprTag::try_from((rnd % 11) as u16).unwrap()),
            1 => Tag::Cont(ContTag::try_from((rnd % 17) as u16 + 4096).unwrap()),
            2 => Tag::Op1(Op1::try_from((rnd % 12) as u16 + 8192).unwrap()),
            3 => Tag::Op2(Op2::try_from((rnd % 16) as u16 + 12288).unwrap()),
            _ => unreachable!(),
        };
        if max_depth == 0 {
            store.intern_atom(tag, Fp::from_u64(rnd))
        } else {
            match rnd % 4 {
                0 => store.intern_atom(tag, Fp::from_u64(rnd)),
                1 => intern_ptrs!(
                    store,
                    tag,
                    rng_interner(rng, max_depth - 1, store),
                    rng_interner(rng, max_depth - 1, store)
                ),
                2 => intern_ptrs!(
                    store,
                    tag,
                    rng_interner(rng, max_depth - 1, store),
                    rng_interner(rng, max_depth - 1, store),
                    rng_interner(rng, max_depth - 1, store)
                ),
                3 => intern_ptrs!(
                    store,
                    tag,
                    rng_interner(rng, max_depth - 1, store),
                    rng_interner(rng, max_depth - 1, store),
                    rng_interner(rng, max_depth - 1, store),
                    rng_interner(rng, max_depth - 1, store)
                ),
                _ => unreachable!(),
            }
        }
    }

    #[test]
    fn test_z_store_roundtrip() {
        const NUM_TESTS: u64 = 192;
        const MAX_DEPTH: usize = 10;

        (0..NUM_TESTS).into_par_iter().for_each(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let store1 = Store::default();
            let ptr1 = rng_interner(&mut rng, MAX_DEPTH, &store1);

            let mut z_store = ZStore::default();
            let mut cache_into = HashMap::default();
            let z_ptr = z_store.populate_with(&ptr1, &store1, &mut cache_into);

            let mut cache_from = HashMap::default();
            let store2 = Store::default();
            let ptr2 = z_store
                .populate_store(&z_ptr, &store2, &mut cache_from)
                .unwrap();

            assert_eq!(store1.hash_ptr(&ptr1), store2.hash_ptr(&ptr2))
        });
    }

    #[test]
    fn test_filtered_dag() {
        let store = Store::<Fp>::default();
        let one = store.num_u64(1);
        let two = store.num_u64(2);
        let thr = store.num_u64(3);
        let one_two = store.cons(one, two);
        let two_thr = store.cons(two, thr);
        let mut z_dag = ZDag::default();
        let mut cache = HashMap::default();
        z_dag.populate_with(&one_two, &store, &mut cache);
        z_dag.populate_with(&two_thr, &store, &mut cache);

        let z_one_two = store.hash_ptr(&one_two);
        let z_two_thr = store.hash_ptr(&two_thr);
        let z_dag_new = z_dag.filtered(&[&z_one_two]).unwrap();

        // data for `z_two_thr` exists in `z_dag`
        assert!(z_dag.get_type(&z_two_thr).is_some());
        // but not in `z_dag_new`
        assert!(z_dag_new.get_type(&z_two_thr).is_none());
    }
}
