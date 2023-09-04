use std::fs::{create_dir_all, File};
use std::io::{BufReader, BufWriter, Read};
use std::marker::PhantomData;

use abomonation::{encode, Abomonation};
use camino::{Utf8Path, Utf8PathBuf};
use nova::traits::Group;

use crate::coprocessor::Coprocessor;
use crate::proof::nova::{CurveCycleEquipped, PublicParams, G1, G2};
use crate::proof::MultiFrameTrait;
use crate::public_parameters::error::Error;

pub(crate) struct PublicParamDiskCache<F, C, M>
where
    F: CurveCycleEquipped,
    C: Coprocessor<F>,
    M: MultiFrameTrait<F, C>,
{
    dir: Utf8PathBuf,
    _t: PhantomData<(F, C, M)>,
}

impl<F: CurveCycleEquipped, C: Coprocessor<F>, M: MultiFrameTrait<F, C>>
    PublicParamDiskCache<F, C, M>
where
    // technical bounds that would disappear once associated_type_bounds stabilizes
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    pub(crate) fn new(disk_cache_path: &Utf8Path) -> Result<Self, Error> {
        create_dir_all(disk_cache_path)?;

        Ok(Self {
            dir: disk_cache_path.to_owned(),
            _t: Default::default(),
        })
    }

    fn key_path(&self, key: &str) -> Utf8PathBuf {
        self.dir.join(Utf8PathBuf::from(key))
    }

    pub(crate) fn get(&self, key: &str) -> Result<PublicParams<F, M>, Error> {
        let file = File::open(self.key_path(key))?;
        let reader = BufReader::new(file);
        bincode::deserialize_from(reader).map_err(|e| {
            Error::CacheError(format!("Public param cache deserialization error: {}", e))
        })
    }

    pub(crate) fn get_raw_bytes(&self, key: &str) -> Result<Vec<u8>, Error> {
        let file = File::open(self.key_path(key))?;
        let mut reader = BufReader::new(file);
        let mut bytes = Vec::new();
        reader.read_to_end(&mut bytes)?;
        Ok(bytes)
    }

    pub(crate) fn set(&self, key: &str, data: &PublicParams<F, M>) -> Result<(), Error> {
        let file = File::create(self.key_path(key)).expect("failed to create file");
        let writer = BufWriter::new(&file);
        bincode::serialize_into(writer, &data).map_err(|e| {
            Error::CacheError(format!("Public param cache serialization error: {}", e))
        })
    }

    pub(crate) fn set_abomonated<V: Abomonation>(&self, key: &str, data: &V) -> Result<(), Error> {
        let mut file = File::create(self.key_path(key))?;
        unsafe { encode(data, &mut file).expect("failed to encode") };
        Ok(())
    }
}
