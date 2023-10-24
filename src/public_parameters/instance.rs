//! # Instances
//!
//! We manage the various kinds of public parameters of Nova and SuperNova with [Instance]s.
//! Each instance is a unique key representing a unique parameter object cached in the file system.
//! The module provides the API to smoothly fetch/write/update params and sets of params.
//!
//! Currently, [::nova] defines three "kinds" of parameter objects that need to be cached.
//! The first kind corresponds to [::nova::PublicParams], which contain a full instance of public parameters
//! required for a Nova proof. The second and third kinds correspond to [::nova::supernova::AuxParams] and
//! [::nova::supernova::CircuitParams], which contain partial instances of public parameters required for
//! a SuperNova proof.
//!
//! ## Hashing
//!
//! When inserting an (instance, parameter) pair into the cache, we compute an unique cache key for the
//! instance to name the cached files. In this computation, we hash the unique identifying information
//! of the instance.
//! - For [::nova::PublicParams], this is the hash of the shape primary circuit
//! - For [::nova::supernova::AuxParams], this is the combine hash of all of the
//!   primary circuit hashes of the SuperNova instance.
//! - For [::nova::supernova::CircuitParams], this is the hash of the shape of its particular SuperNova circuit.
//!
//! Because the first primary circuit of Lurk will always be the universal Lurk circuit, which may get very large
//! at high `rc`, we instead hash an "ad-hoc" circuit that still uniquely represents the universal Lurk circuit,
//! but is much smaller and faster to hash.
//!
//! The idea is this: we have the large `rc` universal Lurk circuit as:
//! ```ignore
//! lurk-circuit(rc) = start bits -- frame -- glue -- frame -- glue ... -- end bits (repeat rc times)
//! ```
//! Instead we hash an ad-hoc circuit (`rc=2`, which allows capturing our "glue"):
//! ```ignore
//! lurk-circuit(2) = start bits -- frame -- glue -- frame -- end bits
//! ```
//! and hash `(lurk-circuit(2), rc)`. This ensures that we include all the information about circuit plumbing
//! done by `start-bits`, `end-bits`, and `glue` in the hash.

use std::{
    fs::File,
    io::{self, BufReader, BufWriter},
    marker::PhantomData,
    sync::Arc,
};

use ::nova::{
    constants::NUM_HASH_BITS,
    supernova::NonUniformCircuit,
    traits::{circuit_supernova::StepCircuit as SuperStepCircuit, Group},
};
use abomonation::Abomonation;
use camino::Utf8Path;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    coprocessor::Coprocessor,
    eval::lang::Lang,
    proof::MultiFrameTrait,
    proof::{
        nova::{self, CurveCycleEquipped, G1, G2},
        supernova::{self, C2},
    },
};

/// [Instance]s compute a cache-key for the objects they represent and are themselves hashed to be put
/// onto the file system. For each instance, we also have a [Metadata] json that contains useful
/// information about it.
///
/// An [Instance] represents exactly one distinct [nova::NovaPublicParams], [supernova::SuperNovaAuxParams],
/// or [supernova::SuperNovaCircuitParams], tagged by the [Kind] field.
///
/// When fetching a set of SuperNova public parameters, the "core" instance is the auxilliary parameters,
/// because it contains the digest of the entire set of public parameters. Then, from this core instance,
/// we derive the `num_circuits + 1` circuit param instances. This makes sure that we keep the SuperNova
/// instances as modular as possible, and reuse as much overlapping circuit params as possible.
#[derive(Debug)]
pub struct Instance<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a, M: MultiFrameTrait<'a, F, C>>
{
    pub rc: usize,
    pub lang: Arc<Lang<F, C>>,
    pub abomonated: bool,
    pub cache_key: F,
    pub kind: Kind,
    pub _p: PhantomData<&'a M>,
}

/// From [::nova], there are 3 "kinds" of public param objects that need to be cached.
/// The first kind corresponds to [nova::NovaPublicParams], which contain a full instance of public parameters
/// required for a Nova proof. The second and third kinds correspond to [supernova::SuperNovaAuxParams] and
/// [supernova::SuperNovaCircuitParams], which contain partial instances of public parameters required for
/// a SuperNova proof.
///
/// See [Instance] for more details on how [Kind] determines the caching behavior.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Kind {
    /// Tag for [nova::NovaPublicParams] instances
    NovaPublicParams,
    /// Tag for [supernova::SuperNovaAuxParams] instances
    SuperNovaAuxParams,
    /// Tag for [supernova::SuperNovaCircuitParams] instances
    SuperNovaCircuitParams(usize),
}

/// What we put into the cache
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Metadata {
    pub rc: usize,
    pub lang: String,
    pub abomonated: bool,
    pub cache_key: String,
    pub kind: Kind,
}

impl Metadata {
    fn from_instance<
        'a,
        F: CurveCycleEquipped,
        C: Coprocessor<F> + 'a,
        M: MultiFrameTrait<'a, F, C>,
    >(
        instance: &Instance<'a, F, C, M>,
    ) -> Self {
        Metadata {
            rc: instance.rc,
            lang: instance.lang.clone().key(),
            abomonated: instance.abomonated,
            cache_key: format!("{:?}", instance.cache_key),
            kind: instance.kind.clone(),
        }
    }
}

impl<
        'a,
        F: CurveCycleEquipped,
        C: Coprocessor<F>,
        M: MultiFrameTrait<'a, F, C> + SuperStepCircuit<F> + NonUniformCircuit<G1<F>, G2<F>, M, C2<F>>,
    > Instance<'a, F, C, M>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    pub fn new(rc: usize, lang: Arc<Lang<F, C>>, abomonated: bool, kind: Kind) -> Self {
        let cache_key = match kind {
            Kind::NovaPublicParams => nova::circuit_cache_key::<'a, F, C, M>(rc, lang.clone()),
            Kind::SuperNovaAuxParams => {
                supernova::circuit_cache_keys::<F, C, M>(rc, &lang).digest()
            }
            Kind::SuperNovaCircuitParams(circuit_index) => {
                supernova::circuit_cache_key::<'a, F, C, M>(rc, lang.clone(), circuit_index)
            }
        };
        Instance {
            rc,
            lang,
            abomonated,
            cache_key,
            kind,
            _p: PhantomData,
        }
    }

    /// If this [Instance] is of [Kind::SuperNovaAuxParams], then generate the `num_circuits + 1`
    /// circuit param instances that are determined by the internal [Lang].
    pub fn circuit_param_instances(&self) -> Vec<Self> {
        assert!(
            matches!(self.kind, Kind::SuperNovaAuxParams),
            "not a supernova instance"
        );
        let num_circuits = self.lang().coprocessors().len() + 1;
        (0..num_circuits)
            .map(|circuit_index| {
                Instance::new(
                    self.rc,
                    self.lang(),
                    self.abomonated,
                    Kind::SuperNovaCircuitParams(circuit_index),
                )
            })
            .collect::<Vec<_>>()
    }

    pub fn reindex(&self, circuit_index: usize) -> Self {
        match self.kind {
            Kind::SuperNovaAuxParams | Kind::SuperNovaCircuitParams(_) => Instance::new(
                self.rc,
                self.lang(),
                self.abomonated,
                Kind::SuperNovaCircuitParams(circuit_index),
            ),
            _ => panic!(),
        }
    }
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<'a, F, C>>
    Instance<'a, F, C, M>
where
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    /// The key (or cache_key) of this [Instance] used to retrieve it from the file cache
    pub fn lang(&self) -> Arc<Lang<F, C>> {
        self.lang.clone()
    }

    /// The key (or cache_key) of this [Instance] used to retrieve it from the file cache
    pub fn key(&self) -> String {
        let abomonated = if self.abomonated { " abomonated" } else { "" };
        let lang = self.lang();
        format!("{} (rc={}){}", lang.key(), self.rc, abomonated)
    }

    pub fn create(&self, disk_cache_path: &Utf8Path) -> io::Result<File> {
        let metadata = Metadata::from_instance(self);
        let cache_key: F = compute_cache_key(&metadata);
        let cache_key_str = format!("{:?}", cache_key);

        let instance_file = File::create(disk_cache_path.join(&cache_key_str))?;

        let metadata_file = disk_cache_path.join(cache_key_str).with_extension("json");
        let metadata_file = File::create(metadata_file)?;

        let writer = BufWriter::new(&metadata_file);
        serde_json::to_writer_pretty(writer, &metadata)?;

        Ok(instance_file)
    }

    pub fn open(&self, disk_cache_path: &Utf8Path) -> io::Result<File> {
        let metadata = Metadata::from_instance(self);
        let cache_key: F = compute_cache_key(&metadata);
        let cache_key_str = format!("{:?}", cache_key);

        let instance_file = File::open(disk_cache_path.join(&cache_key_str))?;

        let metadata_file = disk_cache_path.join(cache_key_str).with_extension("json");
        let metadata_file = File::open(metadata_file)?;

        let reader = BufReader::new(metadata_file);
        let expected_metadata: Metadata = serde_json::from_reader(reader)?;

        if metadata != expected_metadata {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                "public params: mistmatched instances",
            ));
        }

        Ok(instance_file)
    }
}

/// Compute the cache key of any serializable object
fn compute_cache_key<F: CurveCycleEquipped, T: Serialize>(o: &T) -> F {
    // obtain a vector of bytes representing public parameters
    let bytes = bincode::serialize(o).unwrap();

    let mut hasher = Sha256::new();
    hasher.update(&bytes);
    let cache_key = hasher.finalize();

    // truncate the cache_key to NUM_HASH_BITS bits
    let bv = (0..NUM_HASH_BITS).map(|i| {
        let (byte_pos, bit_pos) = (i / 8, i % 8);
        let bit = (cache_key[byte_pos] >> bit_pos) & 1;
        bit == 1
    });

    // turn the bit vector into a scalar
    let mut cache_key = F::ZERO;
    let mut coeff = F::ONE;
    for bit in bv {
        if bit {
            cache_key += coeff;
        }
        coeff += coeff;
    }
    cache_key
}
