use std::hash::Hash;

use crate::field::LurkField;
use generic_array::typenum::{U3, U4, U6, U8};
use neptune::{poseidon::PoseidonConstants, Poseidon};
use once_cell::sync::OnceCell;

#[derive(Debug, Clone, Copy)]
pub enum HashArity {
    A3,
    A4,
    A6,
    A8,
}

impl From<usize> for HashArity {
    fn from(n: usize) -> Self {
        match n {
            3 => Self::A3,
            4 => Self::A4,
            6 => Self::A6,
            8 => Self::A8,
            _ => panic!("unsupported arity: {}", n),
        }
    }
}

pub enum HashConst<'a, F: LurkField> {
    A3(&'a PoseidonConstants<F, U3>),
    A4(&'a PoseidonConstants<F, U4>),
    A6(&'a PoseidonConstants<F, U6>),
    A8(&'a PoseidonConstants<F, U8>),
}

/// Holds the constants needed for poseidon hashing.
#[derive(Clone, Debug)]
pub struct HashConstants<F: LurkField> {
    c3: OnceCell<PoseidonConstants<F, U3>>,
    c4: OnceCell<PoseidonConstants<F, U4>>,
    c6: OnceCell<PoseidonConstants<F, U6>>,
    c8: OnceCell<PoseidonConstants<F, U8>>,
}

impl<F: LurkField> Default for HashConstants<F> {
    fn default() -> Self {
        Self {
            c3: OnceCell::new(),
            c4: OnceCell::new(),
            c6: OnceCell::new(),
            c8: OnceCell::new(),
        }
    }
}

impl<F: LurkField> HashConstants<F> {
    pub fn c3(&self) -> &PoseidonConstants<F, U3> {
        self.c3.get_or_init(|| PoseidonConstants::new())
    }

    pub fn c4(&self) -> &PoseidonConstants<F, U4> {
        self.c4.get_or_init(|| PoseidonConstants::new())
    }

    pub fn c6(&self) -> &PoseidonConstants<F, U6> {
        self.c6.get_or_init(|| PoseidonConstants::new())
    }

    pub fn c8(&self) -> &PoseidonConstants<F, U8> {
        self.c8.get_or_init(|| PoseidonConstants::new())
    }

    pub fn constants(&self, arity: HashArity) -> HashConst<'_, F> {
        match arity {
            HashArity::A3 => HashConst::A3(self.c3.get_or_init(|| PoseidonConstants::new())),
            HashArity::A4 => HashConst::A4(self.c4.get_or_init(|| PoseidonConstants::new())),
            HashArity::A6 => HashConst::A6(self.c6.get_or_init(|| PoseidonConstants::new())),
            HashArity::A8 => HashConst::A8(self.c8.get_or_init(|| PoseidonConstants::new())),
        }
    }
}

#[derive(Clone, Default, Debug)]
pub struct PoseidonCache<F: LurkField> {
    a3: dashmap::DashMap<CacheKey<F, 3>, F, ahash::RandomState>,
    a4: dashmap::DashMap<CacheKey<F, 4>, F, ahash::RandomState>,
    a6: dashmap::DashMap<CacheKey<F, 6>, F, ahash::RandomState>,
    a8: dashmap::DashMap<CacheKey<F, 8>, F, ahash::RandomState>,

    pub constants: HashConstants<F>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct CacheKey<F: LurkField, const N: usize>([F; N]);

#[allow(clippy::derived_hash_with_manual_eq)]
impl<F: LurkField, const N: usize> Hash for CacheKey<F, N> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for el in &self.0 {
            el.to_repr().as_ref().hash(state);
        }
    }
}

impl<F: LurkField> PoseidonCache<F> {
    pub fn hash3(&self, preimage: &[F; 3]) -> F {
        let hash = self
            .a3
            .entry(CacheKey(*preimage))
            .or_insert_with(|| Poseidon::new_with_preimage(preimage, self.constants.c3()).hash());

        *hash
    }

    pub fn hash4(&self, preimage: &[F; 4]) -> F {
        let hash = self
            .a4
            .entry(CacheKey(*preimage))
            .or_insert_with(|| Poseidon::new_with_preimage(preimage, self.constants.c4()).hash());

        *hash
    }

    pub fn hash6(&self, preimage: &[F; 6]) -> F {
        let hash = self
            .a6
            .entry(CacheKey(*preimage))
            .or_insert_with(|| Poseidon::new_with_preimage(preimage, self.constants.c6()).hash());
        *hash
    }

    pub fn hash8(&self, preimage: &[F; 8]) -> F {
        let hash = self
            .a8
            .entry(CacheKey(*preimage))
            .or_insert_with(|| Poseidon::new_with_preimage(preimage, self.constants.c8()).hash());
        *hash
    }
}

pub trait IntoHashComponents<F: LurkField> {
    fn into_hash_components(self) -> [F; 2];
}

impl<F: LurkField> IntoHashComponents<F> for [F; 2] {
    fn into_hash_components(self) -> [F; 2] {
        self
    }
}
