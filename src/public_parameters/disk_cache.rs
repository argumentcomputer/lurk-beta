use std::fs::create_dir_all;
use std::io::{BufReader, BufWriter, Read};
use std::marker::PhantomData;

use abomonation::{encode, Abomonation};
use camino::{Utf8Path, Utf8PathBuf};
use nova::traits::Group;

use crate::coprocessor::Coprocessor;
use crate::proof::nova::{CurveCycleEquipped, PublicParams, G1, G2};
use crate::public_parameters::error::Error;

use super::instance::Instance;

pub(crate) struct PublicParamDiskCache<F, C>
where
    F: CurveCycleEquipped,
    C: Coprocessor<F> + 'a,
    M: MultiFrameTrait<'a, F, C>,
{
    dir: Utf8PathBuf,
    _t: PhantomData<(&'a (), F, C, M)>,
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a, M: MultiFrameTrait<'a, F, C>>
    PublicParamDiskCache<'a, F, C, M>
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

    pub(crate) fn get(
        &self,
        instance: &Instance<F, C>,
    ) -> Result<PublicParams<'static, F, C>, Error> {
        let file = instance.open(&self.dir)?;
        let reader = BufReader::new(file);
        bincode::deserialize_from(reader).map_err(|e| {
            Error::CacheError(format!("Public param cache deserialization error: {}", e))
        })
    }

    pub(crate) fn get_raw_bytes(&self, instance: &Instance<F, C>) -> Result<Vec<u8>, Error> {
        let file = instance.open(&self.dir)?;
        let mut reader = BufReader::new(file);
        let mut bytes = Vec::new();
        reader.read_to_end(&mut bytes)?;
        Ok(bytes)
    }

    pub(crate) fn set(
        &self,
        instance: &Instance<F, C>,
        data: &PublicParams<'static, F, C>,
    ) -> Result<(), Error> {
        let file = instance.create(&self.dir)?;
        let writer = BufWriter::new(&file);
        bincode::serialize_into(writer, &data).map_err(|e| {
            Error::CacheError(format!("Public param cache serialization error: {}", e))
        })
    }

    pub(crate) fn set_abomonated<V: Abomonation>(
        &self,
        instance: &Instance<F, C>,
        data: &V,
    ) -> Result<(), Error> {
        let mut file = instance.create(&self.dir)?;
        unsafe { encode(data, &mut file).expect("failed to encode") };
        Ok(())
    }
}
