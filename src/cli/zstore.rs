use anyhow::{bail, Result};
use indexmap::IndexSet;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::{
    field::{FWrap, LurkField},
    lem::{
        pointers::{IVal, Ptr, ZPtr},
        store::Store,
        store_core::StoreHasher,
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
    Compact(ZPtr<F>, ZPtr<F>, ZPtr<F>),
}

/// Holds a mapping from `ZPtr`s to their `ZPtrType`s
#[derive(Debug, Default, Serialize, Deserialize)]
pub struct ZDag<F: LurkField>(BTreeMap<ZPtr<F>, ZPtrType<F>>);

impl<F: LurkField> ZDag<F> {
    pub fn populate_with(
        &mut self,
        ptr: &Ptr,
        store: &Store<F>,
        cache: &mut HashMap<Ptr, ZPtr<F>>,
    ) -> ZPtr<F> {
        let mut recurse = |ptr: &Ptr, cache: &mut HashMap<_, _>| -> ZPtr<F> {
            if let Some(z_ptr) = cache.get(ptr) {
                *z_ptr
            } else {
                let tag = ptr.tag();
                let z_ptr = match ptr.val() {
                    IVal::Atom(idx) => {
                        let f = store.expect_f(*idx);
                        let z_ptr = ZPtr::from_parts(*tag, *f);
                        self.0.insert(z_ptr, ZPtrType::Atom);
                        z_ptr
                    }
                    IVal::Tuple2(idx) => {
                        let [a, b] = store.expect_tuple2(*idx);
                        let a = self.populate_with(a, store, cache);
                        let b = self.populate_with(b, store, cache);
                        let z_ptr = ZPtr::new(*tag, store.core.hasher.hash_ptrs(vec![a, b]));
                        self.0.insert(z_ptr, ZPtrType::Tuple2(a, b));
                        z_ptr
                    }
                    IVal::Tuple3(idx) => {
                        let [a, b, c] = store.expect_tuple3(*idx);
                        let a = self.populate_with(a, store, cache);
                        let b = self.populate_with(b, store, cache);
                        let c = self.populate_with(c, store, cache);
                        let z_ptr = ZPtr::new(*tag, store.core.hasher.hash_ptrs(vec![a, b, c]));
                        self.0.insert(z_ptr, ZPtrType::Tuple3(a, b, c));
                        z_ptr
                    }
                    IVal::Tuple4(idx) => {
                        let [a, b, c, d] = store.expect_tuple4(*idx);
                        let a = self.populate_with(a, store, cache);
                        let b = self.populate_with(b, store, cache);
                        let c = self.populate_with(c, store, cache);
                        let d = self.populate_with(d, store, cache);
                        let z_ptr = ZPtr::new(*tag, store.core.hasher.hash_ptrs(vec![a, b, c, d]));
                        self.0.insert(z_ptr, ZPtrType::Tuple4(a, b, c, d));
                        z_ptr
                    }
                    IVal::Compact(idx) => {
                        let [a, b, c] = store.expect_tuple3(*idx);
                        let a = self.populate_with(a, store, cache);
                        let b = self.populate_with(b, store, cache);
                        let c = self.populate_with(c, store, cache);
                        let (b_tag, b_val) = b.into_parts();
                        let z_ptr = ZPtr::new(
                            *tag,
                            store
                                .core
                                .hasher
                                .hash_compact(*a.val(), b_tag, b_val, *c.val()),
                        );
                        self.0.insert(z_ptr, ZPtrType::Compact(a, b, c));
                        z_ptr
                    }
                };
                cache.insert(*ptr, z_ptr);
                z_ptr
            }
        };
        let mut dag = IndexSet::from([*ptr]);
        let mut stack = vec![*ptr];
        macro_rules! feed_loop {
            ($x:expr) => {
                if $x.val().is_compound() {
                    if !cache.contains_key(&$x) {
                        if dag.insert($x) {
                            stack.push($x);
                        }
                    }
                }
            };
        }
        while let Some(ptr) = stack.pop() {
            match ptr.val() {
                IVal::Atom(..) => (),
                IVal::Tuple2(idx) => {
                    for ptr in store.expect_tuple2(*idx) {
                        feed_loop!(*ptr)
                    }
                }
                IVal::Tuple3(idx) | IVal::Compact(idx) => {
                    for ptr in store.expect_tuple3(*idx) {
                        feed_loop!(*ptr)
                    }
                }
                IVal::Tuple4(idx) => {
                    for ptr in store.expect_tuple4(*idx) {
                        feed_loop!(*ptr)
                    }
                }
            }
        }
        dag.iter()
            .rev()
            .map(|ptr| recurse(ptr, cache))
            .last()
            .expect("dag doesn't start empty")
    }

    #[inline]
    pub fn populate_with_simple(&mut self, ptr: &Ptr, store: &Store<F>) -> ZPtr<F> {
        self.populate_with(ptr, store, &mut HashMap::default())
    }

    #[inline]
    fn get_type(&self, z_ptr: &ZPtr<F>) -> Option<&ZPtrType<F>> {
        self.0.get(z_ptr)
    }

    fn get_children(&self, z_ptr: &ZPtr<F>) -> Result<Vec<&ZPtr<F>>> {
        match self.get_type(z_ptr) {
            None => bail!("Couldn't find ZPtr on ZStore"),
            Some(ZPtrType::Atom) => Ok(vec![]),
            Some(ZPtrType::Tuple2(z1, z2)) => Ok(vec![z1, z2]),
            Some(ZPtrType::Tuple3(z1, z2, z3) | ZPtrType::Compact(z1, z2, z3)) => {
                Ok(vec![z1, z2, z3])
            }
            Some(ZPtrType::Tuple4(z1, z2, z3, z4)) => Ok(vec![z1, z2, z3, z4]),
        }
    }

    pub fn populate_store(
        &self,
        z_ptr: &ZPtr<F>,
        store: &Store<F>,
        cache: &mut HashMap<ZPtr<F>, Ptr>,
    ) -> Result<Ptr> {
        let recurse = |z_ptr: &ZPtr<F>, cache: &mut HashMap<_, _>| -> Result<Ptr> {
            if let Some(z_ptr) = cache.get(z_ptr) {
                Ok(*z_ptr)
            } else {
                let ptr = match self.get_type(z_ptr) {
                    None => bail!("Couldn't find ZPtr on ZStore"),
                    Some(ZPtrType::Atom) => store.intern_atom(*z_ptr.tag(), *z_ptr.hash()),
                    Some(ZPtrType::Tuple2(z1, z2)) => {
                        let ptr1 = self.populate_store(z1, store, cache)?;
                        let ptr2 = self.populate_store(z2, store, cache)?;
                        store.intern_tuple2([ptr1, ptr2], *z_ptr.tag(), Some(*z_ptr.hash()))
                    }
                    Some(ZPtrType::Tuple3(z1, z2, z3)) => {
                        let ptr1 = self.populate_store(z1, store, cache)?;
                        let ptr2 = self.populate_store(z2, store, cache)?;
                        let ptr3 = self.populate_store(z3, store, cache)?;
                        store.intern_tuple3([ptr1, ptr2, ptr3], *z_ptr.tag(), Some(*z_ptr.hash()))
                    }
                    Some(ZPtrType::Tuple4(z1, z2, z3, z4)) => {
                        let ptr1 = self.populate_store(z1, store, cache)?;
                        let ptr2 = self.populate_store(z2, store, cache)?;
                        let ptr3 = self.populate_store(z3, store, cache)?;
                        let ptr4 = self.populate_store(z4, store, cache)?;
                        store.intern_tuple4(
                            [ptr1, ptr2, ptr3, ptr4],
                            *z_ptr.tag(),
                            Some(*z_ptr.hash()),
                        )
                    }
                    Some(ZPtrType::Compact(z1, z2, z3)) => {
                        let ptr1 = self.populate_store(z1, store, cache)?;
                        let ptr2 = self.populate_store(z2, store, cache)?;
                        let ptr3 = self.populate_store(z3, store, cache)?;
                        store.intern_compact([ptr1, ptr2, ptr3], *z_ptr.tag(), Some(*z_ptr.hash()))
                    }
                };
                cache.insert(*z_ptr, ptr);
                Ok(ptr)
            }
        };
        let mut dag = IndexSet::from([z_ptr]);
        let mut stack = vec![z_ptr];
        macro_rules! feed_loop {
            ($x:expr) => {
                if !cache.contains_key($x) {
                    if dag.insert($x) {
                        stack.push($x);
                    }
                }
            };
        }
        while let Some(z_ptr) = stack.pop() {
            for z_ptr in self.get_children(z_ptr)? {
                feed_loop!(z_ptr)
            }
        }
        dag.iter()
            .rev()
            .map(|z_ptr| recurse(z_ptr, cache))
            .last()
            .expect("dag doesn't start empty")
    }

    #[inline]
    pub fn populate_store_simple(&self, z_ptr: &ZPtr<F>, store: &Store<F>) -> Result<Ptr> {
        self.populate_store(z_ptr, store, &mut HashMap::default())
    }

    /// Populates a `ZDag` with data from self
    ///
    /// # Warning
    /// This function is recursive and might reach Rust's recursion depth limit
    // TODO: solve this issue if we actually use this function
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
                    Some(ZPtrType::Compact(z1, z2, z3)) => {
                        self.populate_z_dag(z1, z_dag, cache)?;
                        self.populate_z_dag(z2, z_dag, cache)?;
                        self.populate_z_dag(z3, z_dag, cache)?;
                        z_dag.0.insert(*z_ptr, ZPtrType::Compact(*z1, *z2, *z3));
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
pub struct ZStore<F: LurkField> {
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
    pub fn add_comm(&mut self, hash: F, secret: F, payload: ZPtr<F>) {
        self.comms.insert(FWrap(hash), (secret, payload));
    }

    #[inline]
    pub fn open(&self, hash: F) -> Option<&(F, ZPtr<F>)> {
        self.comms.get(&FWrap(hash))
    }

    pub fn to_store(&self) -> Result<Store<F>> {
        let store = Store::default();
        let cache = &mut HashMap::default();
        for (hash, (secret, z_payload)) in &self.comms {
            let payload = self.populate_store(z_payload, &store, cache)?;
            store.add_comm(hash.0, *secret, payload);
        }
        Ok(store)
    }

    pub fn to_store_and_ptr(
        &self,
        z_ptr: &ZPtr<F>,
    ) -> Result<(Store<F>, Ptr, HashMap<ZPtr<F>, Ptr>)> {
        let store = Store::default();
        let mut cache = HashMap::default();
        for (FWrap(hash), (secret, z_payload)) in &self.comms {
            let payload = self.populate_store(z_payload, &store, &mut cache)?;
            store.add_comm(*hash, *secret, payload);
        }
        let ptr = self.populate_store(z_ptr, &store, &mut cache)?;
        Ok((store, ptr, cache))
    }

    pub fn from_store_and_ptr(
        store: &Store<F>,
        ptr: &Ptr,
    ) -> (Self, ZPtr<F>, HashMap<Ptr, ZPtr<F>>) {
        let mut z_store = ZStore::default();
        let mut cache = HashMap::default();
        for (FWrap(hash), img) in store.core.comms.clone().into_tuple_vec() {
            let payload = z_store.populate_with(&img.1, store, &mut cache);
            z_store.add_comm(hash, img.0 .0, payload)
        }
        let z_ptr = z_store.populate_with(ptr, store, &mut cache);
        (z_store, z_ptr, cache)
    }

    #[inline]
    pub fn populate_with(
        &mut self,
        ptr: &Ptr,
        store: &Store<F>,
        cache: &mut HashMap<Ptr, ZPtr<F>>,
    ) -> ZPtr<F> {
        self.z_dag.populate_with(ptr, store, cache)
    }

    #[inline]
    pub(crate) fn populate_with_simple(&mut self, ptr: &Ptr, store: &Store<F>) -> ZPtr<F> {
        self.z_dag
            .populate_with(ptr, store, &mut HashMap::default())
    }

    #[inline]
    pub fn populate_store(
        &self,
        z_ptr: &ZPtr<F>,
        store: &Store<F>,
        cache: &mut HashMap<ZPtr<F>, Ptr>,
    ) -> Result<Ptr> {
        self.z_dag.populate_store(z_ptr, store, cache)
    }

    #[inline]
    pub(crate) fn populate_store_simple(&self, z_ptr: &ZPtr<F>, store: &Store<F>) -> Result<Ptr> {
        self.z_dag.populate_store_simple(z_ptr, store)
    }
}

#[cfg(test)]
mod tests {
    use halo2curves::bn256::Fr as Bn;
    use rand::{rngs::StdRng, Rng};
    use rand_core::SeedableRng;
    use rayon::prelude::{IntoParallelIterator, ParallelIterator};
    use std::collections::HashMap;
    use strum::EnumCount;

    use crate::{
        field::LurkField,
        lem::{pointers::Ptr, store::Store, tag::Tag},
        tag::{
            ContTag, ExprTag, Op1, Op2, CONT_TAG_INIT, EXPR_TAG_INIT, OP1_TAG_INIT, OP2_TAG_INIT,
        },
    };

    use super::{ZDag, ZStore};

    /// helper function that interns random data into a store
    fn rng_interner(rng: &mut StdRng, max_depth: usize, store: &Store<Bn>) -> Ptr {
        let rnd = rng.gen::<usize>();
        let tag = match rnd % 4 {
            0 => {
                Tag::Expr(ExprTag::try_from((rnd % ExprTag::COUNT) as u16 + EXPR_TAG_INIT).unwrap())
            }
            1 => {
                Tag::Cont(ContTag::try_from((rnd % ContTag::COUNT) as u16 + CONT_TAG_INIT).unwrap())
            }
            2 => Tag::Op1(Op1::try_from((rnd % Op1::COUNT) as u16 + OP1_TAG_INIT).unwrap()),
            3 => Tag::Op2(Op2::try_from((rnd % Op2::COUNT) as u16 + OP2_TAG_INIT).unwrap()),
            _ => unreachable!(),
        };
        if max_depth == 0 {
            store.intern_atom(tag, Bn::from_u64(rnd.try_into().unwrap()))
        } else {
            match rnd % 5 {
                0 => store.intern_atom(tag, Bn::from_u64(rnd.try_into().unwrap())),
                1 => store.intern_tuple2(
                    [
                        rng_interner(rng, max_depth - 1, store),
                        rng_interner(rng, max_depth - 1, store),
                    ],
                    tag,
                    None,
                ),
                2 => store.intern_tuple3(
                    [
                        rng_interner(rng, max_depth - 1, store),
                        rng_interner(rng, max_depth - 1, store),
                        rng_interner(rng, max_depth - 1, store),
                    ],
                    tag,
                    None,
                ),
                3 => store.intern_tuple4(
                    [
                        rng_interner(rng, max_depth - 1, store),
                        rng_interner(rng, max_depth - 1, store),
                        rng_interner(rng, max_depth - 1, store),
                        rng_interner(rng, max_depth - 1, store),
                    ],
                    tag,
                    None,
                ),
                4 => store.intern_compact(
                    [
                        rng_interner(rng, max_depth - 1, store),
                        rng_interner(rng, max_depth - 1, store),
                        rng_interner(rng, max_depth - 1, store),
                    ],
                    tag,
                    None,
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
    fn test_env_roundtrip() {
        let store = Store::<Bn>::default();
        let val = store.num_u64(1);
        let sym = store.intern_user_symbol("a");
        let env = store.intern_empty_env();
        let env = store.push_binding(sym, val, env);
        let mut z_dag = ZDag::default();
        let z_env = z_dag.populate_with(&env, &store, &mut Default::default());
        let store2 = Store::<Bn>::default();
        let env2 = z_dag
            .populate_store(&z_env, &store2, &mut Default::default())
            .unwrap();
        assert_eq!(store.hash_ptr(&env), store2.hash_ptr(&env2));
    }

    #[test]
    fn test_filtered_dag() {
        let store = Store::<Bn>::default();
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

    #[test]
    fn test_deep_lurk_data_roundtrip() {
        let string = String::from_utf8(vec![b'0'; 8192]).unwrap();
        let store = Store::<Bn>::default();
        let ptr = store.intern_string(&string);
        let mut z_dag = ZDag::default();
        let z_ptr = z_dag.populate_with(&ptr, &store, &mut HashMap::default());

        let store = Store::<Bn>::default();
        z_dag
            .populate_store(&z_ptr, &store, &mut HashMap::default())
            .unwrap();
    }
}
