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

use std::cell::RefCell;
// TODO:
//  - Implement circuit (https://github.com/lurk-lab/lurk-rs/issues/421).
//  - Adapt to ongoing changes to general coprocessor API, most importantly, absorb
//    https://github.com/lurk-lab/lurk-rs/issues/398. - If #398 is smooth enough, no actual implementation changes
//    should be required here, but the test in src/eval/tests/trie.rs can and should be updated.
use std::marker::PhantomData;
use std::rc::Rc;

use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};

use lurk_macros::Coproc;
use serde::{Deserialize, Serialize};

use crate::package::Package;
use crate::state::State;
use crate::{self as lurk, Symbol};

use crate::circuit::gadgets::constraints::{enforce_equal, implies_equal, select};
use crate::circuit::gadgets::data::GlobalAllocations;
use crate::circuit::gadgets::pointer::{AllocatedContPtr, AllocatedPtr};
use crate::coprocessor::{CoCircuit, Coprocessor};
use crate::eval::lang::Lang;
use crate::field::{FWrap, LurkField};
use crate::hash::{HashArity, HashConstants, InversePoseidonCache, PoseidonCache};
use crate::lem::{pointers::Ptr as LEMPtr, store::Store as LEMStore};
use crate::num::Num;
use crate::ptr::Ptr;
use crate::store::Store;
use crate::tag::{ExprTag, Tag};

#[derive(Debug)]
pub enum Error<F> {
    MissingPreimage(F),
}

// TODO: As an optimization, PreimagePath and HashPreimagePath only actually need to hold the ARITY - 1 sibling hashes
// used to supplement the computed/supplied element at each step.
pub type PreimagePath<F, const ARITY: usize> = Vec<[F; ARITY]>;

pub type HashPreimagePath<F, const ARITY: usize> = Vec<(F, [F; ARITY])>;

pub type StandardTrie<'a, F> = Trie<'a, F, 8, 85>;

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

    fn simple_evaluate(&self, s: &Store<F>, _args: &[Ptr<F>]) -> Ptr<F> {
        let trie: StandardTrie<'_, F> = Trie::new(&s.poseidon_cache, &s.inverse_poseidon_cache);

        let root = trie.root;

        // TODO: Use a custom type.
        s.intern_num(Num::Scalar(root))
    }

    fn evaluate_lem_simple(&self, s: &LEMStore<F>, _args: &[LEMPtr<F>]) -> LEMPtr<F> {
        let trie: StandardTrie<'_, F> = Trie::new(&s.poseidon_cache, &s.inverse_poseidon_cache);
        LEMPtr::num(trie.root)
    }

    fn has_circuit(&self) -> bool {
        true
    }
}

impl<F: LurkField> CoCircuit<F> for NewCoprocessor<F> {
    fn arity(&self) -> usize {
        0
    }

    // This is so small, it would make sense to include in the Lurk reduction.
    // TODO: Allow `FoldingConfig` to specify whethere a given Coprocessor should have its own circuit or not.
    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _g: &GlobalAllocations<F>,
        store: &Store<F>,
        _input_exprs: &[AllocatedPtr<F>],
        input_env: &AllocatedPtr<F>,
        input_cont: &AllocatedContPtr<F>,
        _not_dummy: &Boolean,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        let trie: StandardTrie<'_, F> =
            Trie::new(&store.poseidon_cache, &store.inverse_poseidon_cache);

        // TODO: Use a custom type.
        let root = store.intern_num(Num::Scalar(trie.root));
        let root_zptr = store.hash_expr(&root).unwrap();

        Ok((
            AllocatedPtr::alloc_constant(cs, root_zptr)?,
            input_env.clone(),
            input_cont.clone(),
        ))
    }

    fn synthesize_lem_simple<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _g: &lurk::lem::circuit::GlobalAllocator<F>,
        s: &LEMStore<F>,
        _not_dummy: &Boolean,
        _args: &[AllocatedPtr<F>],
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        let trie: StandardTrie<'_, F> = Trie::new(&s.poseidon_cache, &s.inverse_poseidon_cache);

        // TODO: Use a custom type.
        let root = LEMPtr::num(trie.root);
        let root_z_ptr = s.hash_ptr(&root).unwrap();

        AllocatedPtr::alloc_constant(cs, root_z_ptr)
    }
}

#[derive(Clone, Debug, Serialize, Default, Deserialize)]
pub struct LookupCoprocessor<F: LurkField> {
    _p: PhantomData<F>,
}

impl<F: LurkField> Coprocessor<F> for LookupCoprocessor<F> {
    fn eval_arity(&self) -> usize {
        2
    }

    fn simple_evaluate(&self, s: &Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
        let root_ptr = args[0];
        let key_ptr = args[1];

        // TODO: Check tags.
        let root_scalar = *s.hash_expr(&root_ptr).unwrap().value();
        let key_scalar = *s.hash_expr(&key_ptr).unwrap().value();
        let trie: StandardTrie<'_, F> =
            Trie::new_with_root(&s.poseidon_cache, &s.inverse_poseidon_cache, root_scalar);

        let found = trie.lookup_aux(key_scalar).unwrap();

        s.intern_maybe_opaque_comm(found)
    }

    fn evaluate_lem_simple(&self, s: &LEMStore<F>, args: &[LEMPtr<F>]) -> LEMPtr<F> {
        let root_ptr = &args[0];
        let key_ptr = &args[1];

        // TODO: Check tags.
        let root_scalar = *s.hash_ptr(root_ptr).unwrap().value();
        let key_scalar = *s.hash_ptr(key_ptr).unwrap().value();
        let trie: StandardTrie<'_, F> =
            Trie::new_with_root(&s.poseidon_cache, &s.inverse_poseidon_cache, root_scalar);

        LEMPtr::comm(trie.lookup_aux(key_scalar).unwrap())
    }

    fn has_circuit(&self) -> bool {
        true
    }
}

fn synthesize_lookup_aux<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    root_ptr: &AllocatedPtr<F>,
    key_ptr: &AllocatedPtr<F>,
    not_dummy: &Boolean,
    poseidon_cache: &PoseidonCache<F>,
    inverse_poseidon_cache: &InversePoseidonCache<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    // TODO: Check tags.
    let supplied_root_value = root_ptr.hash();
    let root_value = supplied_root_value.get_value();
    let key_val = key_ptr.hash();
    let trie: StandardTrie<'_, F> = if not_dummy.get_value() == Some(true) {
        Trie::new_with_root(
            poseidon_cache,
            inverse_poseidon_cache,
            root_value.ok_or(SynthesisError::AssignmentMissing)?,
        )
    } else {
        Trie::new(poseidon_cache, inverse_poseidon_cache)
    };

    let allocated_root_value =
        AllocatedNum::alloc(&mut cs.namespace(|| "allocated_root_value"), || {
            Ok(trie.root)
        })?;

    implies_equal(
        &mut cs.namespace(|| "enforce_root"),
        not_dummy,
        supplied_root_value,
        &allocated_root_value,
    );

    trie.synthesize_lookup(
        cs,
        &poseidon_cache.constants,
        &allocated_root_value,
        key_val,
    )
}

impl<F: LurkField> CoCircuit<F> for LookupCoprocessor<F> {
    fn arity(&self) -> usize {
        2
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _g: &GlobalAllocations<F>,
        s: &Store<F>,
        args: &[AllocatedPtr<F>],
        input_env: &AllocatedPtr<F>,
        input_cont: &AllocatedContPtr<F>,
        not_dummy: &Boolean,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        let root_ptr = &args[0];
        let key_ptr = &args[1];

        let result_commitment_val = synthesize_lookup_aux(
            cs,
            root_ptr,
            key_ptr,
            not_dummy,
            &s.poseidon_cache,
            &s.inverse_poseidon_cache,
        )?;

        let result_commitment = AllocatedPtr::alloc_tag(
            &mut cs.namespace(|| "result_commitment"),
            ExprTag::Comm.to_field(),
            result_commitment_val,
        )?;

        Ok((result_commitment, input_env.clone(), input_cont.clone()))
    }

    fn synthesize_lem_simple<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &lurk::lem::circuit::GlobalAllocator<F>,
        s: &LEMStore<F>,
        not_dummy: &Boolean,
        args: &[AllocatedPtr<F>],
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        let root_ptr = &args[0];
        let key_ptr = &args[1];

        let result_commitment_val = synthesize_lookup_aux(
            cs,
            root_ptr,
            key_ptr,
            not_dummy,
            &s.poseidon_cache,
            &s.inverse_poseidon_cache,
        )?;

        let comm_tag = g
            .get_allocated_const(ExprTag::Comm.to_field())
            .expect("Comm tag should have been allocated");

        Ok(AllocatedPtr::from_parts(
            comm_tag.clone(),
            result_commitment_val,
        ))
    }
}

#[derive(Clone, Debug, Serialize, Default, Deserialize)]
pub struct InsertCoprocessor<F: LurkField> {
    _p: PhantomData<F>,
}

impl<F: LurkField> Coprocessor<F> for InsertCoprocessor<F> {
    fn eval_arity(&self) -> usize {
        3
    }

    fn simple_evaluate(&self, s: &Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
        let root_ptr = args[0];
        let key_ptr = args[1];
        let val_ptr = args[2];
        let root_scalar = *s.hash_expr(&root_ptr).unwrap().value();
        let key_scalar = *s.hash_expr(&key_ptr).unwrap().value();
        let val_scalar = *s.hash_expr(&val_ptr).unwrap().value();
        let mut trie: StandardTrie<'_, F> =
            Trie::new_with_root(&s.poseidon_cache, &s.inverse_poseidon_cache, root_scalar);
        trie.insert(key_scalar, val_scalar).unwrap();

        let new_root = trie.root;
        s.intern_num(Num::Scalar(new_root))
    }

    fn evaluate_lem_simple(&self, s: &LEMStore<F>, args: &[LEMPtr<F>]) -> LEMPtr<F> {
        let root_ptr = &args[0];
        let key_ptr = &args[1];
        let val_ptr = &args[2];
        let root_scalar = *s.hash_ptr(root_ptr).unwrap().value();
        let key_scalar = *s.hash_ptr(key_ptr).unwrap().value();
        let val_scalar = *s.hash_ptr(val_ptr).unwrap().value();
        let mut trie: StandardTrie<'_, F> =
            Trie::new_with_root(&s.poseidon_cache, &s.inverse_poseidon_cache, root_scalar);
        trie.insert(key_scalar, val_scalar).unwrap();

        LEMPtr::num(trie.root)
    }

    fn has_circuit(&self) -> bool {
        true
    }
}

fn synthesize_insert_aux<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    root_ptr: &AllocatedPtr<F>,
    key_ptr: &AllocatedPtr<F>,
    val_ptr: &AllocatedPtr<F>,
    not_dummy: &Boolean,
    poseidon_cache: &PoseidonCache<F>,
    inverse_poseidon_cache: &InversePoseidonCache<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    // TODO: Check tags.
    let supplied_root_value = root_ptr.hash();
    let root_value = supplied_root_value.get_value();
    let key_val = key_ptr.hash();
    let new_val = val_ptr.hash();
    let trie: StandardTrie<'_, F> = if not_dummy.get_value() == Some(true) {
        Trie::new_with_root(
            poseidon_cache,
            inverse_poseidon_cache,
            root_value.ok_or(SynthesisError::AssignmentMissing)?,
        )
    } else {
        Trie::new(poseidon_cache, inverse_poseidon_cache)
    };

    let allocated_root_value =
        AllocatedNum::alloc(&mut cs.namespace(|| "allocated_root_value"), || {
            Ok(trie.root)
        })?;

    implies_equal(
        &mut cs.namespace(|| "enforce_root"),
        not_dummy,
        supplied_root_value,
        &allocated_root_value,
    );

    trie.synthesize_insert(
        cs,
        &poseidon_cache.constants,
        &allocated_root_value,
        key_val,
        new_val.clone(),
    )
    .map_err(|_e| SynthesisError::Unsatisfiable)
}

impl<F: LurkField> CoCircuit<F> for InsertCoprocessor<F> {
    fn arity(&self) -> usize {
        3
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _g: &GlobalAllocations<F>,
        s: &Store<F>,
        args: &[AllocatedPtr<F>],
        input_env: &AllocatedPtr<F>,
        input_cont: &AllocatedContPtr<F>,
        not_dummy: &Boolean,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        let root_ptr = &args[0];
        let key_ptr = &args[1];
        let val_ptr = &args[2];

        assert_eq!(self.arity(), args.len());

        let new_root_val = synthesize_insert_aux(
            cs,
            root_ptr,
            key_ptr,
            val_ptr,
            not_dummy,
            &s.poseidon_cache,
            &s.inverse_poseidon_cache,
        )?;

        let new_allocated_trie = AllocatedPtr::alloc_tag(
            &mut cs.namespace(|| "new_commitment"),
            // TODO: Use a custom type
            ExprTag::Num.to_field(),
            new_root_val,
        )?;

        Ok((new_allocated_trie, input_env.clone(), input_cont.clone()))
    }

    fn synthesize_lem_simple<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &lurk::lem::circuit::GlobalAllocator<F>,
        s: &LEMStore<F>,
        not_dummy: &Boolean,
        args: &[AllocatedPtr<F>],
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        let root_ptr = &args[0];
        let key_ptr = &args[1];
        let val_ptr = &args[2];

        let new_root_val = synthesize_insert_aux(
            cs,
            root_ptr,
            key_ptr,
            val_ptr,
            not_dummy,
            &s.poseidon_cache,
            &s.inverse_poseidon_cache,
        )?;

        let num_tag = g
            .get_allocated_const(ExprTag::Num.to_field())
            .expect("Num tag should have been allocated");
        Ok(AllocatedPtr::from_parts(num_tag.clone(), new_root_val))
    }
}

/// Add the `Trie`-associated functions to a `Lang` with standard bindings.
// TODO: define standard patterns for such modularity.
pub fn install<F: LurkField>(
    s: &Store<F>,
    state: &Rc<RefCell<State>>,
    lang: &mut Lang<F, TrieCoproc<F>>,
) {
    lang.add_binding((".lurk.trie.new", NewCoprocessor::default().into()), s);
    lang.add_binding(
        (".lurk.trie.lookup", LookupCoprocessor::default().into()),
        s,
    );
    lang.add_binding(
        (".lurk.trie.insert", InsertCoprocessor::default().into()),
        s,
    );

    let name: Symbol = ".lurk.trie".into();
    let mut package = Package::new(name.into());
    ["new", "lookup", "insert"].into_iter().for_each(|name| {
        package.intern(name);
    });
    state.borrow_mut().add_package(package);
}

/// Add the `Trie`-associated functions to a `Lang` with standard bindings.
// TODO: define standard patterns for such modularity.
pub fn install_lem<F: LurkField>(
    s: &LEMStore<F>,
    state: &Rc<RefCell<State>>,
    lang: &mut Lang<F, TrieCoproc<F>>,
) {
    lang.add_coprocessor_lem(".lurk.trie.new", NewCoprocessor::default(), s);
    lang.add_coprocessor_lem(".lurk.trie.lookup", LookupCoprocessor::default(), s);
    lang.add_coprocessor_lem(".lurk.trie.insert", InsertCoprocessor::default(), s);

    let trie_package_name: Symbol = ".lurk.trie".into();
    let mut package = Package::new(trie_package_name.into());
    ["new", "lookup", "insert"].into_iter().for_each(|name| {
        package.intern(name);
    });
    state.borrow_mut().add_package(package);
}

pub type ChildMap<F, const ARITY: usize> = InversePoseidonCache<F>;

/// A sparse Trie.
#[derive(Debug)]
pub struct Trie<'a, F: LurkField, const ARITY: usize, const HEIGHT: usize> {
    root: F,
    empty_roots: [F; HEIGHT],
    hash_cache: &'a PoseidonCache<F>,
    children: &'a ChildMap<F, ARITY>,
}

#[derive(Debug)]
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

#[derive(Debug)]
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
        let old_value = old_value.unwrap_or_else(|| Trie::<'_, F, ARITY, HEIGHT>::empty_element());

        let old_verified = self.old_proof.verify(old_root, key, old_value, hash_cache);

        // This is purely an evaluation-time optimization. Don't try to reproduce in the circuit, which cannot shortcut.
        if !old_verified {
            return false;
        };

        let paths_differ_by_at_most_one = self
            .old_proof
            .preimage_path
            .iter()
            .zip(&self.new_proof.preimage_path)
            .all(|(a, b)| {
                if a == b {
                    // If the remaining trees are identical, then only one needs to be verified.
                    // This is purely an evaluation-time optimization. Don't try to reproduce in the circuit, which cannot shortcut.
                    return old_verified;
                }
                let differing_position_count: usize =
                    a.iter().zip(b).map(|(x, y)| usize::from(x != y)).sum();

                differing_position_count <= 1
            });

        // This is purely an evaluation-time optimization. Don't try to reproduce in the circuit, which cannot shortcut.
        if !paths_differ_by_at_most_one {
            return false;
        };

        self.new_proof.verify(new_root, key, new_value, hash_cache)
    }
}

impl<'a, F: LurkField, const ARITY: usize, const HEIGHT: usize> Trie<'a, F, ARITY, HEIGHT> {
    /// The empty element is specified to be zero. This is a natural choice. Crucially, the chosen value must have no known
    /// preimage.
    fn empty_element() -> F {
        F::ZERO
    }

    fn compute_hash(hash_cache: &PoseidonCache<F>, preimage: [F; ARITY]) -> F {
        hash_cache.compute_hash(preimage)
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

    fn init_empty(&mut self) {
        self.empty_roots = [Self::empty_element(); HEIGHT];

        if HEIGHT == 0 {
            return;
        };

        let mut preimage = [self.empty_roots[0]; ARITY];

        for i in 0..HEIGHT {
            let hash = self.register_hash(preimage);

            self.empty_roots[i] = hash;

            for elt in preimage.iter_mut().take(ARITY) {
                *elt = hash;
            }
        }
        self.root = self.empty_roots[HEIGHT - 1]
    }

    fn empty_root_for_height(&self, height: usize) -> F {
        if height == 0 {
            // This should probably never actually be used, but providing it clarifies the specification, and the
            // meaning of the `height` parameter with respect to the structure  of the trie.
            Self::empty_element()
        } else {
            self.empty_roots[height - 1]
        }
    }

    pub fn empty_root(&mut self) -> F {
        self.empty_root_for_height(HEIGHT)
    }

    /// Creates a new `Trie`, saving preimage data in `store`.
    /// HEIGHT must be exactly that required to minimally store all elements of `F`.
    pub fn new(
        poseidon_cache: &'a PoseidonCache<F>,
        inverse_poseidon_cache: &'a InversePoseidonCache<F>,
    ) -> Self {
        Self::new_aux(poseidon_cache, inverse_poseidon_cache, None)
    }

    /// Creates a new `Trie`, saving preimage data in `store`.
    /// Height must be at least that required to store `size` elements.
    pub fn new_with_capacity(
        poseidon_cache: &'a PoseidonCache<F>,
        inverse_poseidon_cache: &'a InversePoseidonCache<F>,
        size: usize,
    ) -> Self {
        Self::new_aux(poseidon_cache, inverse_poseidon_cache, Some(size))
    }

    fn new_aux(
        poseidon_cache: &'a PoseidonCache<F>,
        inverse_poseidon_cache: &'a InversePoseidonCache<F>,
        size: Option<usize>,
    ) -> Self {
        // ARITY must be a power of two.
        assert_eq!(1, ARITY.count_ones());

        // This will panic if ARITY is unsupporteed.
        let _ = HashArity::from(ARITY);

        let mut new = Self {
            root: Default::default(),
            empty_roots: [Self::empty_element(); HEIGHT],
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
                    + usize::from(field_significant_bits % arity_bits != 0);

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
    fn new_with_root(
        poseidon_cache: &'a PoseidonCache<F>,
        inverse_poseidon_cache: &'a InversePoseidonCache<F>,
        root: F,
    ) -> Self {
        let mut new = Self::new(poseidon_cache, inverse_poseidon_cache);

        new.root = root;

        new
    }

    const fn arity_bits() -> usize {
        // This assumes ARITY is a power of two, as checked in `new_aux()`.
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

    fn synthesize_path<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        key: &AllocatedNum<F>,
    ) -> Result<Vec<Vec<Boolean>>, SynthesisError> {
        let mut bits = key.to_bits_le_strict(&mut cs.namespace(|| "bits"))?;
        bits.reverse();

        let (arity_bits, bits_needed) = Self::path_bit_dimensions();
        let path = bits[bits.len() - bits_needed..]
            .chunks(arity_bits)
            .map(|chunk| chunk.iter().cloned().rev().collect())
            .collect();
        Ok(path)
    }

    // Returns a value corresponding to the commitment associated with `key`, if any.
    // Note that this depends on the impossibility of discovering a value for which the commitment is zero. We could
    // alternately return the empty element (`F::zero()`) for missing values, but instead return an `Option` to more
    // clearly signal intent -- since the encoding of 'missing' values as `Fr::zero()` is significant.
    pub fn lookup(&self, key: F) -> Result<Option<F>, Error<F>> {
        self.lookup_aux(key)
            .map(|payload| (payload != Self::empty_element()).then_some(payload))
    }

    fn lookup_aux(&self, key: F) -> Result<F, Error<F>> {
        let path = Self::path(key);
        let preimage_path =
            Self::prove_lookup_at_path(self.root, self.children, &path)?.preimage_path;

        assert_eq!(path.len(), preimage_path.len());

        let final_preimage = preimage_path[preimage_path.len() - 1];
        let final_step = path[path.len() - 1];
        Ok(final_preimage[final_step])
    }

    fn synthesize_lookup<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        hash_constants: &HashConstants<F>,
        allocated_root: &AllocatedNum<F>,
        key: &AllocatedNum<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let path = Self::synthesize_path(&mut cs.namespace(|| "path"), key)?;

        let val = self
            .synthesize_lookup_at_path(cs, hash_constants, allocated_root, &path)?
            .0;

        Ok(val)
    }

    fn synthesize_lookup_at_path<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        hash_constants: &HashConstants<F>,
        allocated_root: &AllocatedNum<F>,
        path: &[Vec<Boolean>],
    ) -> Result<(AllocatedNum<F>, Vec<Vec<AllocatedNum<F>>>), SynthesisError> {
        let mut preimage_path = Vec::with_capacity(HEIGHT);

        let found =
            path.iter()
                .enumerate()
                .try_fold(allocated_root.clone(), |next, (i, k_bits)| {
                    let next_val = next.get_value();
                    let preimage = next_val.and_then(|x| Self::get_hash_preimage(self.children, x));

                    let allocated_preimage = if let Some(p) = preimage {
                        p.iter()
                            .enumerate()
                            .map(|(j, f)| {
                                AllocatedNum::alloc(
                                    &mut cs.namespace(|| format!("preimage-{i}-{j}")),
                                    || Ok(*f),
                                )
                            })
                            .collect::<Result<Vec<_>, SynthesisError>>()?
                    } else {
                        (0..ARITY)
                            .map(|j| {
                                AllocatedNum::alloc(
                                    &mut cs.namespace(|| format!("preimage-{i}-{j}")),
                                    || Err(SynthesisError::AssignmentMissing),
                                )
                            })
                            .collect::<Result<Vec<_>, SynthesisError>>()?
                    };

                    preimage_path.push(allocated_preimage.clone());

                    let hashed = hash_constants.constants(ARITY.into()).hash(
                        &mut cs.namespace(|| format!("poseidon_hash_{i}")),
                        allocated_preimage.clone(),
                        None,
                    )?;

                    enforce_equal(cs, || format!("hashed equals next {i}"), &hashed, &next);

                    select(
                        &mut cs.namespace(|| format!("select-{i}")),
                        &allocated_preimage,
                        k_bits,
                    )
                })?;
        Ok((found, preimage_path))
    }

    /// Returns a slice of preimages, corresponding to the path.
    /// Final preimage contains payloads.
    pub fn prove_lookup(&self, key: F) -> Result<LookupProof<F, ARITY, HEIGHT>, Error<F>> {
        let path = Self::path(key);
        Self::prove_lookup_at_path(self.root, self.children, &path)
    }

    /// Returns a slice of preimages, corresponding to the path.
    /// Final preimage contains payloads.
    fn prove_lookup_at_path(
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
        let (_insert_proof, inserted) = self.prove_insert(key, value)?;

        Ok(inserted)
    }

    pub fn prove_insert(
        &mut self,
        key: F,
        value: F,
    ) -> Result<(InsertProof<F, ARITY, HEIGHT>, bool), Error<F>> {
        let path = Self::path(key);
        self.insert_at_path(&path, value)
    }

    fn insert_at_path(
        &mut self,
        path: &[usize],
        value: F,
    ) -> Result<(InsertProof<F, ARITY, HEIGHT>, bool), Error<F>> {
        let old_proof = Self::prove_lookup_at_path(self.root, self.children, path)?;

        let (proof, new_root) = self.modify_value_at_path(path, &old_proof.preimage_path, value);

        let inserted = new_root != self.root;

        self.root = new_root;

        let new_proof = LookupProof::new(proof);

        Ok((InsertProof::new(old_proof, new_proof), inserted))
    }

    fn modify_value_at_path(
        &mut self,
        path: &[usize],
        preimage_path: &PreimagePath<F, ARITY>,
        mut value: F,
    ) -> (PreimagePath<F, ARITY>, F) {
        let mut proof = path
            .iter()
            .zip(preimage_path)
            .rev()
            .enumerate()
            .map(|(_i, (path_index, existing_preimage))| {
                let mut new_preimage = *existing_preimage;
                new_preimage[*path_index] = value;
                let new_hash = self.register_hash(new_preimage);
                value = new_hash;
                new_preimage
            })
            .collect::<Vec<_>>();

        proof.reverse();

        (proof, value)
    }

    pub fn synthesize_insert<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        hash_constants: &HashConstants<F>,
        allocated_root: &AllocatedNum<F>,
        key: &AllocatedNum<F>,
        value: AllocatedNum<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let path = Self::synthesize_path(&mut cs.namespace(|| "path"), key)?;
        self.synthesize_insert_at_path(
            &mut cs.namespace(|| "insert_aux"),
            hash_constants,
            allocated_root,
            &path,
            value,
        )
    }

    fn synthesize_insert_at_path<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        hash_constants: &HashConstants<F>,
        allocated_root: &AllocatedNum<F>,
        path: &[Vec<Boolean>],
        value: AllocatedNum<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let preimage_path = self
            .synthesize_lookup_at_path(
                &mut cs.namespace(|| "found_value"),
                hash_constants,
                allocated_root,
                path,
            )?
            .1;

        Self::synthesize_modify_value_at_path(
            &mut cs.namespace(|| "new_root_value"),
            hash_constants,
            path,
            &preimage_path,
            value,
        )
    }

    fn synthesize_modify_value_at_path<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        hash_constants: &HashConstants<F>,
        path: &[Vec<Boolean>],
        preimage_path: &[Vec<AllocatedNum<F>>],
        mut value: AllocatedNum<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        for (i, (path_bits, existing_preimage)) in path.iter().zip(preimage_path).rev().enumerate()
        {
            let path_index = index_from_bits(path_bits);
            let new_preimage = existing_preimage
                .iter()
                .enumerate()
                .map(|(j, _x)| {
                    AllocatedNum::alloc(&mut cs.namespace(|| format!("preimage-{i}-{j}")), || {
                        if j == path_index {
                            value.get_value().ok_or(SynthesisError::AssignmentMissing)
                        } else {
                            existing_preimage[j]
                                .get_value()
                                .ok_or(SynthesisError::AssignmentMissing)
                        }
                    })
                })
                .collect::<Result<Vec<_>, SynthesisError>>()?;

            value = hash_constants.constants(ARITY.into()).hash(
                &mut cs.namespace(|| format!("poseidon_hash_{i}")),
                new_preimage,
                None,
            )?
        }

        Ok(value)
    }
}

fn index_from_bits(bits: &[Boolean]) -> usize {
    bits.iter().rev().fold(0, |mut acc, bit| {
        acc *= 2;
        if bit.get_value().unwrap_or(false) {
            acc += 1
        };
        acc
    })
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
    use once_cell::sync::OnceCell;
    use pasta_curves::pallas::Scalar as Fr;

    static POSEIDON_CACHE: OnceCell<PoseidonCache<Fr>> = OnceCell::new();
    static INVERSE_POSEIDON_CACHE: OnceCell<InversePoseidonCache<Fr>> = OnceCell::new();

    fn poseidon_cache() -> &'static PoseidonCache<Fr> {
        POSEIDON_CACHE.get_or_init(PoseidonCache::default)
    }

    fn inverse_poseidon_cache() -> &'static InversePoseidonCache<Fr> {
        INVERSE_POSEIDON_CACHE.get_or_init(InversePoseidonCache::default)
    }

    #[test]
    fn test_empty_roots() {
        let t: Trie<'_, Fr, 8, 3> =
            Trie::new_with_capacity(poseidon_cache(), inverse_poseidon_cache(), 512);
        assert_eq!(Fr::zero(), Trie::<'_, Fr, 8, 3>::empty_element());
        assert_eq!(Fr::zero(), t.empty_root_for_height(0));
        assert_eq!(
            scalar_from_u64s([
                0xa81830c13a876b1c,
                0x83b4610d346c2a33,
                0x528056fe84bb9846,
                0x0ef417527046e53c
            ]),
            t.empty_root_for_height(1)
        );

        assert_eq!(
            scalar_from_u64s([
                0x33ff39660bc554aa,
                0xd85d92c9279a65e7,
                0x8e0f305f27de3d65,
                0x089120e96e4b6dc5
            ]),
            t.empty_root_for_height(2)
        );
        assert_eq!(
            scalar_from_u64s([
                0xa52e7d0bbbee086b,
                0x06e4ba3d56dbd7fa,
                0xed7adffde497af73,
                0x2fd6f6c5e5d21d60
            ]),
            t.empty_root_for_height(3)
        );
    }

    #[test]
    fn test_sizes() {
        {
            let t: Trie<'_, Fr, 8, 1> =
                Trie::new_with_capacity(poseidon_cache(), inverse_poseidon_cache(), 8);
            assert_eq!(8, t.leaves());
        }

        {
            let t: Trie<'_, Fr, 8, 2> =
                Trie::new_with_capacity(poseidon_cache(), inverse_poseidon_cache(), 64);
            assert_eq!(64, t.leaves());
        }

        {
            let t: Trie<'_, Fr, 8, 3> =
                Trie::new_with_capacity(poseidon_cache(), inverse_poseidon_cache(), 512);
            assert_eq!(512, t.leaves());
        }

        {
            let t: Trie<'_, Fr, 8, 4> =
                Trie::new_with_capacity(poseidon_cache(), inverse_poseidon_cache(), 4096);
            assert_eq!(1, t.row_size(0));
            assert_eq!(8, t.row_size(1));
            assert_eq!(64, t.row_size(2));
            assert_eq!(512, t.row_size(3));
            assert_eq!(4096, t.row_size(4));
            assert_eq!(4096, t.leaves());
        }
    }

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
        {
            let mut t0: Trie<'_, Fr, 8, 1> =
                Trie::new_with_capacity(poseidon_cache(), inverse_poseidon_cache(), 8);
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
            let mut t1: Trie<'_, Fr, 8, 2> =
                Trie::new_with_capacity(poseidon_cache(), inverse_poseidon_cache(), 64);
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
            let mut t2: Trie<'_, Fr, 8, 3> =
                Trie::new_with_capacity(poseidon_cache(), inverse_poseidon_cache(), 512);
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
            let mut t3: Trie<'_, Fr, 8, 4> =
                Trie::new_with_capacity(poseidon_cache(), inverse_poseidon_cache(), 4096);
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
        {
            let t3: Trie<'_, Fr, 8, 3> =
                Trie::new_with_capacity(poseidon_cache(), inverse_poseidon_cache(), 512);

            let found = t3.lookup(Fr::from_u64(500)).unwrap();
            assert_eq!(None, found);
        }
    }
    #[test]
    fn test_lookup_proof() {
        {
            let t3: Trie<'_, Fr, 8, 3> =
                Trie::new_with_capacity(poseidon_cache(), inverse_poseidon_cache(), 512);
            let root = t3.root();
            let key = Fr::from_u64(500);
            let proof = t3.prove_lookup(key).unwrap();

            let fresh_p = PoseidonCache::<Fr>::default();
            let verified = proof.verify(root, key, Fr::zero(), &fresh_p);
            assert!(verified);
        }
    }

    #[test]
    fn test_insert() {
        // TODO: Use prop tests.
        {
            let mut t3: Trie<'_, Fr, 8, 3> =
                Trie::new_with_capacity(poseidon_cache(), inverse_poseidon_cache(), 512);
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
        {
            let mut t3: Trie<'_, Fr, 8, 3> =
                Trie::new_with_capacity(poseidon_cache(), inverse_poseidon_cache(), 512);
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
                assert!(verified);
            }

            let old_root = t3.root;
            let (insert_proof, inserted) = t3.prove_insert(key, val).unwrap();

            assert!(inserted);

            {
                let root = t3.root;
                let fresh_p = PoseidonCache::<Fr>::default();

                let verified = insert_proof.verify(old_root, root, key, None, val, &fresh_p);
                assert!(verified);

                {
                    let proof = t3.prove_lookup(key).unwrap();

                    let verified = proof.verify(root, key, val, &fresh_p);
                    assert!(verified);
                }
                {
                    let proof2 = t3.prove_lookup(key2).unwrap();

                    let verified = proof2.verify(root, key2, Fr::zero(), &fresh_p);
                    assert!(verified);
                }
            }

            let old_root = t3.root;
            let (insert_proof2, inserted2) = t3.prove_insert(key2, val2).unwrap();
            assert!(inserted2);

            {
                let root = t3.root;
                let fresh_p = PoseidonCache::<Fr>::default();

                {
                    let verified = insert_proof2.verify(old_root, root, key2, None, val2, &fresh_p);
                    assert!(verified);
                }
                {
                    let proof = t3.prove_lookup(key).unwrap();
                    let root = t3.root;

                    let fresh_p = PoseidonCache::<Fr>::default();
                    let verified = proof.verify(root, key, val, &fresh_p);
                    assert!(verified);
                }
                {
                    let proof2 = t3.prove_lookup(key2).unwrap();
                    let root = t3.root;

                    let fresh_p = PoseidonCache::<Fr>::default();
                    let verified = proof2.verify(root, key2, val2, &fresh_p);
                    assert!(verified);
                }
            }
            let (_, inserted2a) = t3.prove_insert(key2, val2).unwrap();
            assert!(!inserted2a);

            let old_root = t3.root;
            let (insert_proof3, inserted3) = t3.prove_insert(key2, val3).unwrap();
            assert!(inserted3);
            {
                let root = t3.root;
                let fresh_p = PoseidonCache::<Fr>::default();

                let verified =
                    insert_proof3.verify(old_root, root, key2, Some(val2), val3, &fresh_p);
                assert!(verified);

                {
                    let proof = t3.prove_lookup(key).unwrap();
                    let verified = proof.verify(root, key, val, &fresh_p);
                    assert!(verified);
                }
                {
                    let proof2 = t3.prove_lookup(key2).unwrap();
                    let verified = proof2.verify(root, key2, val3, &fresh_p);
                    assert!(verified);
                }
            }
        }
    }
}
