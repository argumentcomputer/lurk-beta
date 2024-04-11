use arc_swap::ArcSwap;
use elsa::sync::{index_set::FrozenIndexSet, FrozenMap, FrozenVec};
use indexmap::IndexSet;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use std::sync::Arc;

use super::pointers::{GPtr, IPtr, IVal};

/// Trait that teaches the `StoreCore` how to perform custom hashing operations
pub trait StoreHasher<T, D> {
    fn hash_ptrs(&self, ptrs: Vec<GPtr<T, D>>) -> D;
    fn hash_compact(&self, d1: D, t2: T, d2: D, d3: D) -> D;
    fn hash_commitment(&self, secret: D, payload: GPtr<T, D>) -> D;
}

/// A data structure used to efficiently encode data as DAGs of tagged pointers
/// that can eventually be content-addressed by a custom hasher
#[derive(Debug)]
pub struct StoreCore<T, D, H: StoreHasher<T, D>> {
    /// Holds leaf (non-compound) data
    atom: FrozenIndexSet<Box<D>>,

    /// Holds compound data with 2 children
    tuple2: FrozenIndexSet<Box<[IPtr<T>; 2]>>,

    /// Holds compound data with 3 children
    tuple3: FrozenIndexSet<Box<[IPtr<T>; 3]>>,

    /// Holds compound data with 4 children
    tuple4: FrozenIndexSet<Box<[IPtr<T>; 4]>>,

    /// `StoreHasher` implementer
    pub hasher: H,

    /// Holds the commitments performed with the store
    pub comms: FrozenMap<D, Box<(D, IPtr<T>)>>, // digest -> (secret, payload)

    /// Keeps track of data that hasn't been hashed yet for future parallel hashing
    dehydrated: ArcSwap<FrozenVec<Box<IVal>>>,

    /// Memoized hashes
    z_cache: FrozenMap<IVal, Box<D>>,

    /// Inverse hashes to enable the retrieval of the original data from their
    /// digests
    inverse_z_cache: FrozenMap<D, Box<IVal>>,
}

impl<
        T: PartialEq + std::cmp::Eq + std::hash::Hash,
        D: PartialEq + std::cmp::Eq + std::hash::Hash,
        H: StoreHasher<T, D> + Default,
    > Default for StoreCore<T, D, H>
{
    fn default() -> Self {
        Self {
            atom: Default::default(),
            tuple2: Default::default(),
            tuple3: Default::default(),
            tuple4: Default::default(),
            hasher: Default::default(),
            comms: Default::default(),
            dehydrated: Default::default(),
            z_cache: Default::default(),
            inverse_z_cache: Default::default(),
        }
    }
}

impl<
        T: Copy + PartialEq + std::cmp::Eq + std::hash::Hash + Send + Sync,
        D: Copy + PartialEq + std::cmp::Eq + std::hash::Hash + Send + Sync,
        H: StoreHasher<T, D> + Sync,
    > StoreCore<T, D, H>
{
    #[inline]
    pub fn intern_digest(&self, d: D) -> (usize, bool) {
        self.atom.insert_probe(Box::new(d))
    }

    #[inline]
    pub fn fetch_digest(&self, idx: usize) -> Option<&D> {
        self.atom.get_index(idx)
    }

    #[inline]
    pub fn expect_digest(&self, idx: usize) -> &D {
        self.fetch_digest(idx).expect("Digest wasn't interned")
    }

    pub fn intern_tuple2(&self, ptrs: [IPtr<T>; 2], tag: T, digest: Option<D>) -> IPtr<T> {
        let (idx, inserted) = self.tuple2.insert_probe(Box::new(ptrs));
        let ptr = IPtr::new(tag, IVal::Tuple2(idx));
        if let Some(digest) = digest {
            let val = *ptr.val();
            self.z_cache.insert(val, Box::new(digest));
            self.inverse_z_cache.insert(digest, Box::new(val));
        } else if inserted {
            self.dehydrated.load().push(Box::new(*ptr.val()));
        }
        ptr
    }

    #[inline]
    pub fn fetch_tuple2(&self, idx: usize) -> Option<&[IPtr<T>; 2]> {
        self.tuple2.get_index(idx)
    }

    #[inline]
    pub fn expect_tuple2(&self, idx: usize) -> &[IPtr<T>; 2] {
        self.fetch_tuple2(idx).expect("Tuple2 not interned")
    }

    fn intern_tuple3_common(
        &self,
        ptrs: [IPtr<T>; 3],
        tag: T,
        digest: Option<D>,
        compact: bool,
    ) -> IPtr<T> {
        let (idx, inserted) = self.tuple3.insert_probe(Box::new(ptrs));
        let ptr = if compact {
            IPtr::new(tag, IVal::Compact(idx))
        } else {
            IPtr::new(tag, IVal::Tuple3(idx))
        };
        if let Some(digest) = digest {
            let val = *ptr.val();
            self.z_cache.insert(val, Box::new(digest));
            self.inverse_z_cache.insert(digest, Box::new(val));
        } else if inserted {
            self.dehydrated.load().push(Box::new(*ptr.val()));
        }
        ptr
    }

    #[inline]
    pub fn intern_tuple3(&self, ptrs: [IPtr<T>; 3], tag: T, digest: Option<D>) -> IPtr<T> {
        self.intern_tuple3_common(ptrs, tag, digest, false)
    }

    #[inline]
    pub fn fetch_tuple3(&self, idx: usize) -> Option<&[IPtr<T>; 3]> {
        self.tuple3.get_index(idx)
    }

    #[inline]
    pub fn expect_tuple3(&self, idx: usize) -> &[IPtr<T>; 3] {
        self.fetch_tuple3(idx).expect("Tuple3 not interned")
    }

    pub fn intern_tuple4(&self, ptrs: [IPtr<T>; 4], tag: T, digest: Option<D>) -> IPtr<T> {
        let (idx, inserted) = self.tuple4.insert_probe(Box::new(ptrs));
        let ptr = IPtr::new(tag, IVal::Tuple4(idx));
        if let Some(digest) = digest {
            let val = *ptr.val();
            self.z_cache.insert(val, Box::new(digest));
            self.inverse_z_cache.insert(digest, Box::new(val));
        } else if inserted {
            self.dehydrated.load().push(Box::new(*ptr.val()));
        }
        ptr
    }

    #[inline]
    pub fn fetch_tuple4(&self, idx: usize) -> Option<&[IPtr<T>; 4]> {
        self.tuple4.get_index(idx)
    }

    #[inline]
    pub fn expect_tuple4(&self, idx: usize) -> &[IPtr<T>; 4] {
        self.fetch_tuple4(idx).expect("Tuple4 not interned")
    }

    #[inline]
    pub fn intern_compact(&self, ptrs: [IPtr<T>; 3], tag: T, digest: Option<D>) -> IPtr<T> {
        self.intern_tuple3_common(ptrs, tag, digest, true)
    }

    #[inline]
    pub fn fetch_compact(&self, idx: usize) -> Option<&[IPtr<T>; 3]> {
        self.fetch_tuple3(idx)
    }

    #[inline]
    pub fn fetch_compact_by_val(&self, ptr_val: &IVal) -> Option<&[IPtr<T>; 3]> {
        ptr_val
            .get_compact_idx()
            .and_then(|idx| self.fetch_compact(idx))
    }

    #[inline]
    pub fn expect_compact(&self, idx: usize) -> &[IPtr<T>; 3] {
        self.fetch_compact(idx).expect("Compact not interned")
    }

    /// Recursively hashes the children of a `IVal` in order to obtain its
    /// corresponding digest. While traversing the tree, it consults the cache
    /// of `IVal`s that have already been hashed and also populates this cache
    /// for the new `IVal`s.
    ///
    /// Warning: without cache hits, this function might blow up Rust's recursion
    /// depth limit. This limitation is circumvented by calling `hydrate_z_cache`
    /// beforehand or by using `hash_ptr` instead, which might be slightly slower.
    pub fn hash_ptr_val_unsafe(&self, ptr_val: &IVal) -> D {
        if let Some(digest) = self.z_cache.get(ptr_val) {
            *digest
        } else {
            let digest = match *ptr_val {
                IVal::Atom(idx) => *self.fetch_digest(idx).expect("Atom not interned"),
                IVal::Tuple2(idx) => {
                    let [a, b] = self.expect_tuple2(idx);
                    let a_digest = self.hash_ptr_val_unsafe(a.val());
                    let b_digest = self.hash_ptr_val_unsafe(b.val());
                    let a = GPtr::new(*a.tag(), a_digest);
                    let b = GPtr::new(*b.tag(), b_digest);
                    self.hasher.hash_ptrs(vec![a, b])
                }
                IVal::Tuple3(idx) => {
                    let [a, b, c] = self.expect_tuple3(idx);
                    let a_digest = self.hash_ptr_val_unsafe(a.val());
                    let b_digest = self.hash_ptr_val_unsafe(b.val());
                    let c_digest = self.hash_ptr_val_unsafe(c.val());
                    let a = GPtr::new(*a.tag(), a_digest);
                    let b = GPtr::new(*b.tag(), b_digest);
                    let c = GPtr::new(*c.tag(), c_digest);
                    self.hasher.hash_ptrs(vec![a, b, c])
                }
                IVal::Tuple4(idx) => {
                    let [a, b, c, d] = self.expect_tuple4(idx);
                    let a_digest = self.hash_ptr_val_unsafe(a.val());
                    let b_digest = self.hash_ptr_val_unsafe(b.val());
                    let c_digest = self.hash_ptr_val_unsafe(c.val());
                    let d_digest = self.hash_ptr_val_unsafe(d.val());
                    let a = GPtr::new(*a.tag(), a_digest);
                    let b = GPtr::new(*b.tag(), b_digest);
                    let c = GPtr::new(*c.tag(), c_digest);
                    let d = GPtr::new(*d.tag(), d_digest);
                    self.hasher.hash_ptrs(vec![a, b, c, d])
                }
                IVal::Compact(idx) => {
                    let [a, b, c] = self.expect_compact(idx);
                    let a_digest = self.hash_ptr_val_unsafe(a.val());
                    let b_digest = self.hash_ptr_val_unsafe(b.val());
                    let c_digest = self.hash_ptr_val_unsafe(c.val());
                    self.hasher
                        .hash_compact(a_digest, *b.tag(), b_digest, c_digest)
                }
            };
            self.z_cache.insert(*ptr_val, Box::new(digest));
            self.inverse_z_cache.insert(digest, Box::new(*ptr_val));
            digest
        }
    }

    /// Hashes `IVal`s in parallel, consuming chunks of length 256, which is a
    /// reasonably safe limit. The danger of longer chunks is that the rightmost
    /// pointers are the ones which are more likely to reach the recursion depth
    /// limit in `hash_ptr_val_unsafe`. So we move in smaller chunks from left to
    /// right, populating the `z_cache`, which can rescue `hash_ptr_val_unsafe`
    /// from deep recursions
    fn hydrate_z_cache_with_ptr_vals(&self, ptrs: &[&IVal]) {
        ptrs.chunks(256).for_each(|chunk| {
            chunk.par_iter().for_each(|ptr| {
                self.hash_ptr_val_unsafe(ptr);
            });
        });
    }

    /// Hashes enqueued `Ptr` trees in chunks, avoiding deep recursions in
    /// `hash_ptr_val_unsafe`. Resets the `dehydrated` queue afterwards.
    pub fn hydrate_z_cache(&self) {
        self.hydrate_z_cache_with_ptr_vals(&self.dehydrated.load().iter().collect::<Vec<_>>());
        self.dehydrated.swap(Arc::new(FrozenVec::default()));
    }

    /// Whether the length of the dehydrated queue is within the safe limit.
    /// Note: these values are experimental and may be machine dependant.
    #[inline]
    fn is_below_safe_threshold(&self) -> bool {
        if cfg!(debug_assertions) {
            // not release mode
            self.dehydrated.load().len() < 443
        } else {
            // release mode
            self.dehydrated.load().len() < 2497
        }
    }

    /// Safe version of `hash_ptr_val_unsafe` that doesn't hit a stack overflow
    /// by precomputing the pointers that need to be hashed in order to hash the
    /// provided `ptr`
    pub fn hash_ptr_val(&self, ptr_val: &IVal) -> D {
        if self.is_below_safe_threshold() {
            // just run `hash_ptr_val_unsafe` for extra speed when the dehydrated
            // queue is small enough
            return self.hash_ptr_val_unsafe(ptr_val);
        }
        let mut ptrs_vals: IndexSet<&IVal> = IndexSet::default();
        let mut stack = vec![ptr_val];
        macro_rules! feed_loop {
            ($x:expr) => {
                if $x.is_compound() {
                    if self.z_cache.get($x).is_none() {
                        if ptrs_vals.insert($x) {
                            stack.push($x);
                        }
                    }
                }
            };
        }
        while let Some(ptr_val) = stack.pop() {
            match ptr_val {
                IVal::Atom(..) => (),
                IVal::Tuple2(idx) => {
                    for ptr in self.expect_tuple2(*idx) {
                        feed_loop!(ptr.val())
                    }
                }
                IVal::Tuple3(idx) | IVal::Compact(idx) => {
                    for ptr in self.expect_tuple3(*idx) {
                        feed_loop!(ptr.val())
                    }
                }
                IVal::Tuple4(idx) => {
                    for ptr in self.expect_tuple4(*idx) {
                        feed_loop!(ptr.val())
                    }
                }
            }
        }
        ptrs_vals.reverse();
        self.hydrate_z_cache_with_ptr_vals(&ptrs_vals.into_iter().collect::<Vec<_>>());
        // now it's okay to call `hash_ptr_val_unsafe`
        self.hash_ptr_val_unsafe(ptr_val)
    }

    #[inline]
    pub fn hash_ptr(&self, ptr: &IPtr<T>) -> GPtr<T, D> {
        GPtr::new(*ptr.tag(), self.hash_ptr_val(ptr.val()))
    }

    #[inline]
    pub fn add_comm(&self, digest: D, secret: D, payload: IPtr<T>) {
        self.comms.insert(digest, Box::new((secret, payload)));
    }

    pub fn hide(&self, secret: D, payload: IPtr<T>) -> (D, GPtr<T, D>) {
        let z = self.hash_ptr(&payload);
        let digest = self.hasher.hash_commitment(secret, z);
        self.add_comm(digest, secret, payload);
        (digest, z)
    }

    #[inline]
    pub fn open(&self, digest: &D) -> Option<&(D, IPtr<T>)> {
        self.comms.get(digest)
    }

    #[inline]
    pub fn can_open(&self, digest: &D) -> bool {
        self.open(digest).is_some()
    }

    /// `IPtr` equality w.r.t. their content-addressed versions
    #[inline]
    pub fn ptr_eq(&self, a: &IPtr<T>, b: &IPtr<T>) -> bool {
        self.hash_ptr(a) == self.hash_ptr(b)
    }

    #[inline]
    pub fn intern_atom(&self, tag: T, d: D) -> IPtr<T> {
        IPtr::new(tag, IVal::Atom(self.intern_digest(d).0))
    }

    /// Creates an atom pointer from a ZPtr, with its hash. Hashing
    /// such pointer will result on the same original ZPtr
    #[inline]
    pub fn opaque(&self, z: GPtr<T, D>) -> IPtr<T> {
        let (tag, value) = z.into_parts();
        self.intern_atom(tag, value)
    }

    #[inline]
    pub fn to_ptr_val(&self, digest: &D) -> IVal {
        self.inverse_z_cache
            .get(digest)
            .cloned()
            .unwrap_or_else(|| IVal::Atom(self.intern_digest(*digest).0))
    }

    /// Attempts to recover the `Ptr` from `inverse_z_cache`. If the mapping is
    /// not there, returns the corresponding opaque pointer instead
    #[inline]
    pub fn to_ptr(&self, z: &GPtr<T, D>) -> IPtr<T> {
        GPtr::new(*z.tag(), self.to_ptr_val(z.val()))
    }
}
