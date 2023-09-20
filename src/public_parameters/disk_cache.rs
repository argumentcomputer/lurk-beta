use std::fs::{create_dir_all, File};
use std::io::{BufReader, BufWriter, Read};
use std::marker::PhantomData;

use abomonation::{encode, Abomonation};
use camino::{Utf8Path, Utf8PathBuf};
use nova::traits::Group;

use crate::coprocessor::Coprocessor;
use crate::proof::nova::{CurveCycleEquipped, PublicParams, G1, G2};
use crate::public_parameters::error::Error;

pub(crate) struct PublicParamDiskCache<F, C>
where
    F: CurveCycleEquipped,
    C: Coprocessor<F>,
{
    dir: Utf8PathBuf,
    _t: PhantomData<(F, C)>,
}

impl<F: CurveCycleEquipped, C: Coprocessor<F>> PublicParamDiskCache<F, C>
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

    pub(crate) fn get(&self, key: &str) -> Result<PublicParams<'static, F, C>, Error> {
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

    pub(crate) fn set(&self, key: &str, data: &PublicParams<'static, F, C>) -> Result<(), Error> {
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
