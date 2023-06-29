use std::collections::HashMap;
use std::hash::Hash;
use std::sync::Arc;

use crate::cache_map::CacheMap;
use crate::field::{FWrap, LurkField};

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
    a3: Arc<CacheMap<CacheKey<F, 3>, F>>,
    a4: Arc<CacheMap<CacheKey<F, 4>, F>>,
    a6: Arc<CacheMap<CacheKey<F, 6>, F>>,
    a8: Arc<CacheMap<CacheKey<F, 8>, F>>,

    pub constants: HashConstants<F>,
}

impl<F: LurkField> PoseidonCache<F> {
    pub fn compute_hash<const ARITY: usize>(&self, preimage: [F; ARITY]) -> F {
        macro_rules! hash {
            ($hash_name:ident, $n:expr) => {{
                assert_eq!(ARITY, $n);
                // SAFETY: we are just teaching the compiler that the slice has size, ARITY, which is guaranteed by
                // the assertion above.
                self.$hash_name(unsafe { std::mem::transmute::<&[F; ARITY], &[F; $n]>(&preimage) })
            }};
        }
        match ARITY {
            3 => hash!(hash3, 3),
            4 => hash!(hash4, 4),
            6 => hash!(hash6, 6),
            8 => hash!(hash8, 8),
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Default, Debug)]
pub struct InversePoseidonCache<F: LurkField> {
    a3: HashMap<FWrap<F>, [F; 3]>,
    a4: HashMap<FWrap<F>, [F; 4]>,
    a6: HashMap<FWrap<F>, [F; 6]>,
    a8: HashMap<FWrap<F>, [F; 8]>,

    pub constants: HashConstants<F>,
}

impl<F: LurkField> InversePoseidonCache<F> {
    pub fn get<const ARITY: usize>(&self, key: &FWrap<F>) -> Option<&[F; ARITY]> {
        macro_rules! get {
            ($name:ident, $n: expr) => {{
                let preimage = self.$name.get(key);
                if let Some(p) = preimage {
                    assert_eq!(ARITY, $n);
                    // SAFETY: we are just teaching the compiler that the slice has size, ARITY, which is guaranteed by
                    // the assertion above.
                    Some(unsafe { std::mem::transmute::<&[F; $n], &[F; ARITY]>(p) })
                } else {
                    None
                }
            }};
        }

        match ARITY {
            3 => get!(a3, 3),
            4 => get!(a4, 4),
            6 => get!(a6, 6),
            8 => get!(a8, 8),
            _ => unreachable!(),
        }
    }
    pub fn insert<const ARITY: usize>(&mut self, key: FWrap<F>, preimage: [F; ARITY]) {
        macro_rules! insert {
            ($name:ident, $n:expr) => {{
                assert_eq!(ARITY, $n);
                // SAFETY: we are just teaching the compiler that the slice has size, ARITY, which is guaranteed by
                // the assertion above.
                self.$name.insert(key, unsafe {
                    *std::mem::transmute::<&[F; ARITY], &[F; $n]>(&preimage)
                });
            }};
        }

        match ARITY {
            3 => insert!(a3, 3),
            4 => insert!(a4, 4),
            6 => insert!(a6, 6),
            8 => insert!(a8, 8),
            _ => unreachable!(),
        }
    }
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
        self.a3.get_copy_or_insert_with(CacheKey(*preimage), || {
            Poseidon::new_with_preimage(preimage, self.constants.c3()).hash()
        })
    }

    pub fn hash4(&self, preimage: &[F; 4]) -> F {
        self.a4.get_copy_or_insert_with(CacheKey(*preimage), || {
            Poseidon::new_with_preimage(preimage, self.constants.c4()).hash()
        })
    }

    pub fn hash6(&self, preimage: &[F; 6]) -> F {
        self.a6.get_copy_or_insert_with(CacheKey(*preimage), || {
            Poseidon::new_with_preimage(preimage, self.constants.c6()).hash()
        })
    }

    pub fn hash8(&self, preimage: &[F; 8]) -> F {
        self.a8.get_copy_or_insert_with(CacheKey(*preimage), || {
            Poseidon::new_with_preimage(preimage, self.constants.c8()).hash()
        })
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
