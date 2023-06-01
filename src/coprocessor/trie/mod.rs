//! The `trie` module implements a Trie with the following properties:
//! Big-endian bits of the (field element) key are taken N at a time, where the underlying hash has arity 2^N. This
//! forms a fixed-length path whose final element is either zero or some non-zero payload. If the payload is assumed to
//! be a commitment, then zero can be used as a hash whose preimage is undiscoverable, and hence empty. To optimize
//! creation of an empty tree, we precompute the empty subtree at each row rather than trying to actually construct the
//! tree with a vast number of redundant hashes.
//!
//! The non-circuit implementation appears to do the unnecessary work of returning not only lookup and insertion results
//! but also Merkle inclusion *proofs* of correctness. That's because the circuit implementation, which represents a
//! proof, will actually be a proof *verifying* that the vanilla operation was correctly performed. Therefore, the
//! vanilla operation needs to provide such a proof so the circuit can verify it.

// TODO:
//  - Implement circuit (https://github.com/lurk-lab/lurk-rs/issues/421).
//  - Adapt to ongoing changes to general coprocessor API, most importantly, absorb
//    https://github.com/lurk-lab/lurk-rs/issues/398. - If #398 is smooth enough, no actual implementation changes
//    should be required here, but the test in src/eval/tests/trie.rs can and should be updated.
use std::marker::PhantomData;

use lurk_macros::Coproc;
use serde::{Deserialize, Serialize};

use crate as lurk;

use crate::coprocessor::{CoCircuit, Coprocessor};
use crate::eval::lang::Lang;
use crate::field::{FWrap, LurkField};
use crate::hash::{InversePoseidonCache, PoseidonCache};
use crate::num::Num;
use crate::ptr::Ptr;
use crate::store::Store;

#[derive(Debug)]
pub enum Error<F> {
    MissingPreimage(F),
}

pub type PreimagePath<F, const ARITY: usize> = Vec<[F; ARITY]>;

pub type HashPreimagePath<F, const ARITY: usize> = Vec<(F, [F; ARITY])>;

#[derive(Clone, Coproc, Debug)]
pub enum TrieCoproc<F: LurkField> {
    New(NewCoprocessor<F>),
    Lookup(LookupCoprocessor<F>),
    Insert(InsertCoprocessor<F>),
}

#[derive(Clone, Debug, Serialize, Default, Deserialize)]
pub struct NewCoprocessor<F: LurkField> {
    _p: PhantomData<F>,
}

impl<F: LurkField> Coprocessor<F> for NewCoprocessor<F> {
    fn eval_arity(&self) -> usize {
        0
    }

    fn simple_evaluate(&self, s: &mut Store<F>, _args: &[Ptr<F>]) -> Ptr<F> {
        let trie: Trie<'_, F, 8, 85> = Trie::new(s);

        let root = trie.root;

        // FIXME: Use a custom type.
        s.intern_num(Num::Scalar(root))
    }
}

impl<F: LurkField> CoCircuit<F> for NewCoprocessor<F> {}

#[derive(Clone, Debug, Serialize, Default, Deserialize)]
pub struct LookupCoprocessor<F: LurkField> {
    _p: PhantomData<F>,
}

impl<F: LurkField> Coprocessor<F> for LookupCoprocessor<F> {
    fn eval_arity(&self) -> usize {
        2
    }

    fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
        let root_ptr = args[0];
        let key_ptr = args[1];
        let root_scalar = *s.get_expr_hash(&root_ptr).unwrap().value();
        let key_scalar = *s.get_expr_hash(&key_ptr).unwrap().value();
        let trie: Trie<'_, F, 8, 85> = Trie::new_with_root(s, root_scalar);

        let found = trie.lookup_aux(key_scalar).unwrap();

        s.intern_maybe_opaque_comm(found)
    }
}

impl<F: LurkField> CoCircuit<F> for LookupCoprocessor<F> {}

#[derive(Clone, Debug, Serialize, Default, Deserialize)]
pub struct InsertCoprocessor<F: LurkField> {
    _p: PhantomData<F>,
}

impl<F: LurkField> Coprocessor<F> for InsertCoprocessor<F> {
    fn eval_arity(&self) -> usize {
        3
    }

    fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
        let root_ptr = args[0];
        let key_ptr = args[1];
        let val_ptr = args[2];
        let root_scalar = *s.get_expr_hash(&root_ptr).unwrap().value();
        let key_scalar = *s.get_expr_hash(&key_ptr).unwrap().value();
        let val_scalar = *s.get_expr_hash(&val_ptr).unwrap().value();
        let mut trie: Trie<'_, F, 8, 85> = Trie::new_with_root(s, root_scalar);
        trie.insert(key_scalar, val_scalar).unwrap();

        let new_root = trie.root;
        s.intern_num(Num::Scalar(new_root))
    }
}

impl<F: LurkField> CoCircuit<F> for InsertCoprocessor<F> {}

/// Add the `Trie`-associated functions to a `Lang` with standard bindings.
// TODO: define standard patterns for such modularity.
pub fn install<F: LurkField>(s: &mut Store<F>, lang: &mut Lang<F, TrieCoproc<F>>) {
    lang.add_binding((".lurk.trie.new", NewCoprocessor::default().into()), s);
    lang.add_binding(
        (".lurk.trie.lookup", LookupCoprocessor::default().into()),
        s,
    );
    lang.add_binding(
        (".lurk.trie.insert", InsertCoprocessor::default().into()),
        s,
    );
}

//pub type ChildMap<F: LurkField, const ARITY: usize> = HashMap<FWrap<F>, [F; ARITY]>;
pub type ChildMap<F, const ARITY: usize> = InversePoseidonCache<F>;

/// A sparse Trie.
pub struct Trie<'a, F: LurkField, const ARITY: usize, const HEIGHT: usize> {
    root: F,
    empty_roots: [F; HEIGHT],
    hash_cache: &'a PoseidonCache<F>,
    children: &'a mut ChildMap<F, ARITY>,
}

pub struct LookupProof<F: LurkField, const ARITY: usize, const HEIGHT: usize> {
    preimage_path: PreimagePath<F, ARITY>,
}

impl<F: LurkField, const ARITY: usize, const HEIGHT: usize> LookupProof<F, ARITY, HEIGHT> {
    fn new(preimage_path: PreimagePath<F, ARITY>) -> Self {
        Self { preimage_path }
    }

    /// Verify a `LookupProof`. Note that this verification is exactly what must be proved in the circuit.
    pub fn verify(&self, root: F, key: F, value: F, hash_cache: &PoseidonCache<F>) -> bool {
        let path = Trie::<F, ARITY, HEIGHT>::path(key);

        let mut next = root;
        for (k, preimage) in path.iter().zip(&self.preimage_path) {
            let computed_hash = Trie::<F, ARITY, HEIGHT>::compute_hash(hash_cache, *preimage);

            if next != computed_hash {
                return false;
            }
            next = preimage[*k];
        }
        next == value
    }
}

pub struct InsertProof<F: LurkField, const ARITY: usize, const HEIGHT: usize> {
    old_proof: LookupProof<F, ARITY, HEIGHT>,
    new_proof: LookupProof<F, ARITY, HEIGHT>,
}

impl<F: LurkField, const ARITY: usize, const HEIGHT: usize> InsertProof<F, ARITY, HEIGHT> {
    fn new(
        old_proof: LookupProof<F, ARITY, HEIGHT>,
        new_proof: LookupProof<F, ARITY, HEIGHT>,
    ) -> Self {
        Self {
            old_proof,
            new_proof,
        }
    }

    /// Verify an `InsertProof`. Note that this verification is exactly what must be proved in the circuit.
    pub fn verify(
        &self,
        old_root: F,
        new_root: F,
        key: F,
        old_value: Option<F>,
        new_value: F,
        hash_cache: &PoseidonCache<F>,
    ) -> bool {
        let old_verified = self.old_proof.verify(
            old_root,
            key,
            old_value.unwrap_or_else(|| F::zero()),
            hash_cache,
        );

        let new_verified = self.new_proof.verify(new_root, key, new_value, hash_cache);

        let paths_differ_by_at_most_one = self
            .old_proof
            .preimage_path
            .iter()
            .zip(&self.new_proof.preimage_path)
            .all(|(a, b)| {
                let differing_postition_count = a
                    .iter()
                    .zip(b)
                    .map(|(x, y)| x != y)
                    .fold(0, |acc, are_diff| acc + are_diff as usize);
                differing_postition_count == 1 || differing_postition_count == 0
            });

        old_verified && new_verified && paths_differ_by_at_most_one
    }
}

impl<'a, F: LurkField, const ARITY: usize, const HEIGHT: usize> Trie<'a, F, ARITY, HEIGHT> {
    fn compute_hash(hash_cache: &PoseidonCache<F>, preimage: [F; ARITY]) -> F {
        macro_rules! hash {
            ($hash_name:ident, $n:expr) => {{
                let mut buffer = [F::zero(); $n];
                buffer.copy_from_slice(&preimage);

                hash_cache.$hash_name(&buffer)
            }};
        }
        match ARITY {
            3 => hash!(hash3, 3),
            4 => hash!(hash4, 4),
            6 => hash!(hash6, 6),
            8 => hash!(hash8, 8),
            _ => unimplemented!(),
        }
    }

    pub fn root(&self) -> F {
        self.root
    }

    /// How many leaves does this `Trie` have?
    pub const fn leaves(&self) -> usize {
        self.row_size(HEIGHT)
    }

    /// How many nodes does the `row`th row have?
    pub const fn row_size(&self, row: usize) -> usize {
        debug_assert!(row <= HEIGHT);
        (ARITY as u32).pow(row as u32) as usize
    }

    fn register_hash(&mut self, preimage: [F; ARITY]) -> F {
        let hash = Self::compute_hash(self.hash_cache, preimage);

        self.children.insert(FWrap(hash), preimage);
        hash
    }

    fn get_hash_preimage(children: &ChildMap<F, ARITY>, hash: F) -> Option<&[F; ARITY]> {
        children.get(&FWrap(hash))
    }

    // TODO: This is expensive and can be cached for the type.
    fn init_empty(&mut self) {
        self.empty_roots = [F::zero(); HEIGHT];

        if HEIGHT == 0 {
            return;
        };

        let mut preimage = [self.empty_roots[0]; ARITY];

        for i in 0..HEIGHT {
            let hash = self.register_hash(preimage);

            self.empty_roots[i] = hash;

            preimage = [hash; ARITY];
            for elt in preimage.iter_mut().take(ARITY) {
                *elt = hash;
            }
        }
        self.root = self.empty_roots[HEIGHT - 1]
    }

    fn empty_root_for_height(&self, height: usize) -> F {
        self.empty_roots[height - 1]
    }

    pub fn empty_root(&mut self) -> F {
        self.empty_root_for_height(HEIGHT)
    }

    /// Creates a new `Trie`, saving preimage data in `store`.
    /// HEIGHT must be exactly that required to minimally store all elements of `F`.
    pub fn new(store: &'a mut Store<F>) -> Self {
        Self::new_aux(store, None)
    }

    /// Creates a new `Trie`, saving preimage data in `store`.
    /// Height must be at least that required to store `size` elements.
    pub fn new_with_capacity(store: &'a mut Store<F>, size: usize) -> Self {
        Self::new_aux(store, Some(size))
    }

    fn new_aux(store: &'a mut Store<F>, size: Option<usize>) -> Self {
        // ARITY must be a power of two.
        assert_eq!(1, ARITY.count_ones());

        let poseidon_cache = &store.poseidon_cache;
        let inverse_poseidon_cache = &mut store.inverse_poseidon_cache;

        let mut new = Self {
            root: Default::default(),
            empty_roots: [F::zero(); HEIGHT],
            hash_cache: poseidon_cache,
            children: inverse_poseidon_cache,
        };

        let (arity_bits, bits_needed_for_path) = Self::path_bit_dimensions();
        let bits_available_from_field = std::mem::size_of::<F>() * 8;

        // The path shape derived from HEIGHT and ARITY must not be greater than the number of bits the field supplies.
        assert!(bits_needed_for_path <= bits_available_from_field);

        match size {
            // No size specified means size must be 'exact'.
            None => {
                let field_significant_bits = F::NUM_BITS as usize;
                let height_needed_for_field = field_significant_bits / arity_bits
                    + ((field_significant_bits % arity_bits != 0) as usize);

                // HEIGHT must be exactly the minimum required so that every field element has a unique path.
                assert_eq!(height_needed_for_field, HEIGHT);
            }

            // A specified size must not require more than the available path bits.
            Some(size) => {
                let size_from_path = 1 << (arity_bits * HEIGHT);
                assert!(size <= size_from_path);
            }
        };

        new.init_empty();

        new
    }

    /// Create a new `Trie` with specified root.
    fn new_with_root(store: &'a mut Store<F>, root: F) -> Self {
        let mut new = Self::new(store);

        new.root = root;

        new
    }

    const fn arity_bits() -> usize {
        ARITY.trailing_zeros() as usize
    }

    /// (arity_bits, path_bits)
    const fn path_bit_dimensions() -> (usize, usize) {
        let arity_bits = Self::arity_bits();
        (arity_bits, arity_bits * HEIGHT)
    }

    fn path(key: F) -> Vec<usize> {
        let mut bits = key.to_le_bits();
        bits.reverse();

        let (arity_bits, bits_needed) = Self::path_bit_dimensions();
        let path = bits[bits.len() - bits_needed..]
            .chunks(arity_bits)
            .map(|chunk| {
                let mut acc = 0;
                for bit in chunk {
                    acc *= 2;
                    if *bit {
                        acc += 1
                    };
                }
                acc
            })
            .collect::<Vec<_>>();
        path
    }

    // Returns a value corresponding to the commitment associated with `key`, if any.
    // Note that this depends on the impossibility of discovering a value for which the commitment is zero.
    // We could alternately return `F::zero()` for missing values, but instead return an `Option` to more clearly
    // signal intent -- since the encoding of 'missing' values as `Fr::zero()` is significant.
    pub fn lookup(&self, key: F) -> Result<Option<F>, Error<F>> {
        self.lookup_aux(key)
            .map(|payload| (payload != F::zero()).then_some(payload))
    }

    fn lookup_aux(&self, key: F) -> Result<F, Error<F>> {
        let path = Self::path(key);
        let preimage_path = Self::prove_lookup_aux(self.root, self.children, &path)?.preimage_path;

        assert_eq!(path.len(), preimage_path.len());

        let final_preimage = preimage_path[preimage_path.len() - 1];
        let final_step = path[path.len() - 1];
        Ok(final_preimage[final_step])
    }

    /// Returns a slice of preimages, corresponding to the path.
    /// Final preimage contains payloads.
    pub fn prove_lookup(&self, key: F) -> Result<LookupProof<F, ARITY, HEIGHT>, Error<F>> {
        let path = Self::path(key);
        Self::prove_lookup_aux(self.root, self.children, &path)
    }

    /// Returns a slice of preimages, corresponding to the path.
    /// Final preimage contains payloads.
    fn prove_lookup_aux(
        root: F,
        children: &ChildMap<F, ARITY>,
        path: &[usize],
    ) -> Result<LookupProof<F, ARITY, HEIGHT>, Error<F>> {
        let mut preimages = Vec::with_capacity(path.len());

        path.iter().try_fold(root, |next, k| {
            if let Some(preimage) = Self::get_hash_preimage(children, next) {
                preimages.push(*preimage);
                Ok((*preimage)[*k])
            } else {
                Err(Error::MissingPreimage(next))
            }
        })?;

        Ok(LookupProof::new(preimages))
    }

    pub fn insert(&mut self, key: F, value: F) -> Result<bool, Error<F>> {
        let path = Self::path(key);
        let (_insert_proof, inserted) = self.prove_insert_aux(&path, value)?;

        Ok(inserted)
    }

    pub fn prove_insert(
        &mut self,
        key: F,
        value: F,
    ) -> Result<(InsertProof<F, ARITY, HEIGHT>, bool), Error<F>> {
        let path = Self::path(key);
        self.prove_insert_aux(&path, value)
    }

    fn prove_insert_aux(
        &mut self,
        path: &[usize],
        value: F,
    ) -> Result<(InsertProof<F, ARITY, HEIGHT>, bool), Error<F>> {
        let old_proof = Self::prove_lookup_aux(self.root, self.children, path)?;

        let mut new_value = value;
        let mut proof = path
            .iter()
            .zip(&old_proof.preimage_path)
            .rev()
            .map(|(path_index, existing_preimage)| {
                let mut new_preimage = *existing_preimage;
                new_preimage[*path_index] = new_value;
                let new_hash = self.register_hash(new_preimage);
                new_value = new_hash;
                new_preimage
            })
            .collect::<Vec<_>>();

        proof.reverse();

        let new_root = new_value;
        let inserted = new_root != self.root;

        self.root = new_root;

        let new_proof = LookupProof::new(proof);

        Ok((InsertProof::new(old_proof, new_proof), inserted))
    }
}

impl<'a, F: LurkField, const ARITY: usize, const HEIGHT: usize> Default
    for Trie<'a, F, ARITY, HEIGHT>
{
    fn default() -> Self {
        todo!();
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ff::PrimeField;
    use pasta_curves::pallas::Scalar as Fr;

    #[test]
    fn test_sizes() {
        let s = &mut Store::new();
        {
            let t: Trie<'_, Fr, 8, 1> = Trie::new_with_capacity(s, 8);
            assert_eq!(8, t.leaves());
        }

        {
            let t: Trie<'_, Fr, 8, 2> = Trie::new_with_capacity(s, 64);
            assert_eq!(64, t.leaves());
        }

        {
            let t: Trie<'_, Fr, 8, 3> = Trie::new_with_capacity(s, 512);
            assert_eq!(512, t.leaves());
        }

        {
            let t: Trie<'_, Fr, 8, 4> = Trie::new_with_capacity(s, 4096);
            assert_eq!(1, t.row_size(0));
            assert_eq!(8, t.row_size(1));
            assert_eq!(64, t.row_size(2));
            assert_eq!(512, t.row_size(3));
            assert_eq!(4096, t.row_size(4));
            assert_eq!(4096, t.leaves());
        }
    }

    #[cfg(test)]
    pub(crate) fn scalar_from_u64s(parts: [u64; 4]) -> Fr {
        let mut le_bytes = [0u8; 32];
        le_bytes[0..8].copy_from_slice(&parts[0].to_le_bytes());
        le_bytes[8..16].copy_from_slice(&parts[1].to_le_bytes());
        le_bytes[16..24].copy_from_slice(&parts[2].to_le_bytes());
        le_bytes[24..32].copy_from_slice(&parts[3].to_le_bytes());
        let mut repr = <Fr as PrimeField>::Repr::default();
        repr.as_mut().copy_from_slice(&le_bytes[..]);
        Fr::from_repr_vartime(repr).expect("u64s exceed scalar field modulus")
    }

    #[test]
    fn test_hashes() {
        let s = &mut Store::new();
        {
            let mut t0: Trie<'_, Fr, 8, 1> = Trie::new_with_capacity(s, 8);
            assert_eq!(
                scalar_from_u64s([
                    0xa81830c13a876b1c,
                    0x83b4610d346c2a33,
                    0x528056fe84bb9846,
                    0x0ef417527046e53c
                ]),
                t0.empty_root()
            );
            assert_eq!(t0.empty_root(), t0.root());
        }
        {
            let mut t1: Trie<'_, Fr, 8, 2> = Trie::new_with_capacity(s, 64);
            assert_eq!(
                scalar_from_u64s([
                    0x33ff39660bc554aa,
                    0xd85d92c9279a65e7,
                    0x8e0f305f27de3d65,
                    0x089120e96e4b6dc5
                ]),
                t1.empty_root()
            );
            assert_eq!(t1.empty_root(), t1.root());
        }
        {
            let mut t2: Trie<'_, Fr, 8, 3> = Trie::new_with_capacity(s, 512);
            assert_eq!(
                scalar_from_u64s([
                    0xa52e7d0bbbee086b,
                    0x06e4ba3d56dbd7fa,
                    0xed7adffde497af73,
                    0x2fd6f6c5e5d21d60
                ]),
                t2.empty_root()
            );
            assert_eq!(t2.empty_root(), t2.root());
        }
        {
            let mut t3: Trie<'_, Fr, 8, 4> = Trie::new_with_capacity(s, 4096);
            assert_eq!(
                scalar_from_u64s([
                    0xd95987b58e6c5852,
                    0x261c08dca064c6c3,
                    0x191320220a5d5d84,
                    0x2cdb105f591c0e94
                ]),
                t3.empty_root()
            );
            assert_eq!(t3.empty_root(), t3.root());
        }
    }

    #[test]
    fn test_path() {
        assert_eq!(vec![7, 6, 4], Trie::<Fr, 8, 3>::path(Fr::from_u64(500)));
    }

    #[test]
    fn test_lookup() {
        let s = &mut Store::new();
        {
            let t3: Trie<'_, Fr, 8, 3> = Trie::new_with_capacity(s, 512);

            let found = t3.lookup(Fr::from_u64(500)).unwrap();
            assert_eq!(None, found);
        }
    }
    #[test]
    fn test_lookup_proof() {
        let s = &mut Store::new();
        {
            let t3: Trie<'_, Fr, 8, 3> = Trie::new_with_capacity(s, 512);
            let root = t3.root();
            let key = Fr::from_u64(500);
            let proof = t3.prove_lookup(key).unwrap();

            let fresh_p = PoseidonCache::<Fr>::default();
            let verified = proof.verify(root, key, Fr::zero(), &fresh_p);
            assert_eq!(true, verified);
        }
    }

    #[test]
    fn test_insert() {
        // TODO: Use prop tests.

        let s = &mut Store::new();
        {
            let mut t3: Trie<'_, Fr, 8, 3> = Trie::new_with_capacity(s, 512);
            let key = Fr::from_u64(500);
            let val = Fr::from_u64(123);

            let key2 = Fr::from_u64(127);
            let val2 = Fr::from_u64(987);

            {
                let found = t3.lookup(key).unwrap();
                assert_eq!(None, found);
            }

            t3.insert(key, val).unwrap();

            {
                let found = t3.lookup(key).unwrap();
                assert_eq!(Some(val), found);
                let found2 = t3.lookup(key2).unwrap();
                assert_eq!(None, found2);
            }

            t3.insert(key2, val2).unwrap();
            {
                let found = t3.lookup(key).unwrap();
                assert_eq!(Some(val), found);
                let found2 = t3.lookup(key2).unwrap();
                assert_eq!(Some(val2), found2);
            }
        }
    }

    #[test]
    fn test_insert_proof() {
        let s = &mut Store::new();
        {
            let mut t3: Trie<'_, Fr, 8, 3> = Trie::new_with_capacity(s, 512);
            let key = Fr::from_u64(500);
            let val = Fr::from_u64(123);

            let key2 = Fr::from_u64(127);
            let val2 = Fr::from_u64(987);
            let val3 = Fr::from_u64(444);

            {
                let proof = t3.prove_lookup(key).unwrap();
                let root = t3.root;

                let fresh_p = PoseidonCache::<Fr>::default();
                let verified = proof.verify(root, key, Fr::zero(), &fresh_p);
                assert_eq!(true, verified);
            }

            let old_root = t3.root;
            let (insert_proof, inserted) = t3.prove_insert(key, val).unwrap();

            assert_eq!(true, inserted);

            {
                let root = t3.root;
                let fresh_p = PoseidonCache::<Fr>::default();

                let verified = insert_proof.verify(old_root, root, key, None, val, &fresh_p);
                assert_eq!(true, verified);

                {
                    let proof = t3.prove_lookup(key).unwrap();

                    let verified = proof.verify(root, key, val, &fresh_p);
                    assert_eq!(true, verified);
                }
                {
                    let proof2 = t3.prove_lookup(key2).unwrap();

                    let verified = proof2.verify(root, key2, Fr::zero(), &fresh_p);
                    assert_eq!(true, verified);
                }
            }

            let old_root = t3.root;
            let (insert_proof2, inserted2) = t3.prove_insert(key2, val2).unwrap();
            assert_eq!(true, inserted2);

            {
                let root = t3.root;
                let fresh_p = PoseidonCache::<Fr>::default();

                {
                    let verified = insert_proof2.verify(old_root, root, key2, None, val2, &fresh_p);
                    assert_eq!(true, verified);
                }
                {
                    let proof = t3.prove_lookup(key).unwrap();
                    let root = t3.root;

                    let fresh_p = PoseidonCache::<Fr>::default();
                    let verified = proof.verify(root, key, val, &fresh_p);
                    assert_eq!(true, verified);
                }
                {
                    let proof2 = t3.prove_lookup(key2).unwrap();
                    let root = t3.root;

                    let fresh_p = PoseidonCache::<Fr>::default();
                    let verified = proof2.verify(root, key2, val2, &fresh_p);
                    assert_eq!(true, verified);
                }
            }
            let (_, inserted2a) = t3.prove_insert(key2, val2).unwrap();
            assert_eq!(false, inserted2a);

            let old_root = t3.root;
            let (insert_proof3, inserted3) = t3.prove_insert(key2, val3).unwrap();
            assert_eq!(true, inserted3);
            {
                let root = t3.root;
                let fresh_p = PoseidonCache::<Fr>::default();

                let verified =
                    insert_proof3.verify(old_root, root, key2, Some(val2), val3, &fresh_p);
                assert_eq!(true, verified);

                {
                    let proof = t3.prove_lookup(key).unwrap();
                    let verified = proof.verify(root, key, val, &fresh_p);
                    assert_eq!(true, verified);
                }
                {
                    let proof2 = t3.prove_lookup(key2).unwrap();
                    let verified = proof2.verify(root, key2, val3, &fresh_p);
                    assert_eq!(true, verified);
                }
            }
        }
    }
}
