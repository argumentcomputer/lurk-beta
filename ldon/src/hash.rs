use std::hash::Hash;

use generic_array::typenum::{
  U3,
  U4,
  U6,
  U8,
};
use lurk_ff::field::LurkField;
use neptune::{
  poseidon::PoseidonConstants,
  Poseidon,
};
use once_cell::sync::OnceCell;

/// Holds the constants needed for poseidon hashing.
#[derive(Debug)]
pub struct HashConstants<F: LurkField> {
  pub c3: OnceCell<PoseidonConstants<F, U3>>,
  pub c4: OnceCell<PoseidonConstants<F, U4>>,
  pub c6: OnceCell<PoseidonConstants<F, U6>>,
  pub c8: OnceCell<PoseidonConstants<F, U8>>,
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
}

#[derive(Default, Debug)]
pub struct PoseidonCache<F: LurkField> {
  pub a3: dashmap::DashMap<CacheKey<F, 3>, F, ahash::RandomState>,
  pub a4: dashmap::DashMap<CacheKey<F, 4>, F, ahash::RandomState>,
  pub a6: dashmap::DashMap<CacheKey<F, 6>, F, ahash::RandomState>,
  pub a8: dashmap::DashMap<CacheKey<F, 8>, F, ahash::RandomState>,

  pub constants: HashConstants<F>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct CacheKey<F: LurkField, const N: usize>([F; N]);

#[allow(clippy::derive_hash_xor_eq)]
impl<F: LurkField, const N: usize> Hash for CacheKey<F, N> {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    for el in &self.0 {
      el.to_repr().as_ref().hash(state);
    }
  }
}

impl<F: LurkField> PoseidonCache<F> {
  pub fn hash3(&self, preimage: &[F; 3]) -> F {
    let hash = self.a3.entry(CacheKey(*preimage)).or_insert_with(|| {
      Poseidon::new_with_preimage(preimage, self.constants.c3()).hash()
    });

    *hash
  }

  pub fn hash4(&self, preimage: &[F; 4]) -> F {
    let hash = self.a4.entry(CacheKey(*preimage)).or_insert_with(|| {
      Poseidon::new_with_preimage(preimage, self.constants.c4()).hash()
    });

    *hash
  }

  pub fn hash6(&self, preimage: &[F; 6]) -> F {
    let hash = self.a6.entry(CacheKey(*preimage)).or_insert_with(|| {
      Poseidon::new_with_preimage(preimage, self.constants.c6()).hash()
    });
    *hash
  }

  pub fn hash8(&self, preimage: &[F; 8]) -> F {
    let hash = self.a8.entry(CacheKey(*preimage)).or_insert_with(|| {
      Poseidon::new_with_preimage(preimage, self.constants.c8()).hash()
    });
    *hash
  }
}
