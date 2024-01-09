use std::fs::create_dir_all;
use std::io::{BufReader, BufWriter, Read};
use std::marker::PhantomData;

use abomonation::{encode, Abomonation};
use camino::{Utf8Path, Utf8PathBuf};
use nova::traits::Engine;

use crate::config::lurk_config;
use crate::coprocessor::Coprocessor;
use crate::proof::nova::{CurveCycleEquipped, PublicParams, C1LEM, E1, E2};
use crate::public_parameters::error::Error;

use super::instance::Instance;

/// Returns the public parameter disk cache directory, which has
/// either been configured or defaults to `$HOME/.lurk/public_params`
pub(crate) fn public_params_dir() -> &'static Utf8PathBuf {
    &lurk_config(None, None).public_params_dir
}

pub(crate) struct DiskCache<'a, F, C>
where
    F: CurveCycleEquipped,
    C: Coprocessor<F> + 'a,
{
    dir: Utf8PathBuf,
    _t: PhantomData<(&'a (), F, C)>,
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a> DiskCache<'a, F, C>
where
    // technical bounds that would disappear once associated_type_bounds stabilizes
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    pub(crate) fn new(disk_cache_path: &Utf8Path) -> Result<Self, Error> {
        create_dir_all(disk_cache_path)?;

        Ok(Self {
            dir: disk_cache_path.to_owned(),
            _t: Default::default(),
        })
    }

    pub(crate) fn read(
        &self,
        instance: &Instance<'a, F, C>,
    ) -> Result<PublicParams<F, C1LEM<'a, F, C>>, Error> {
        let file = instance.open(&self.dir)?;
        let reader = BufReader::new(file);
        bincode::deserialize_from(reader)
            .map_err(|e| Error::Cache(format!("Public param cache deserialization error: {}", e)))
    }

    pub(crate) fn read_bytes(
        &self,
        instance: &Instance<'a, F, C>,
        byte_sink: &mut Vec<u8>,
    ) -> Result<(), Error> {
        let file = instance.open(&self.dir)?;
        let mut reader = BufReader::new(file);
        reader.read_to_end(byte_sink)?;
        Ok(())
    }

    pub(crate) fn write(
        &self,
        instance: &Instance<'a, F, C>,
        data: &PublicParams<F, C1LEM<'a, F, C>>,
    ) -> Result<(), Error> {
        let file = instance.create(&self.dir)?;
        let writer = BufWriter::new(&file);
        bincode::serialize_into(writer, &data)
            .map_err(|e| Error::Cache(format!("Public param cache serialization error: {}", e)))
    }

    pub(crate) fn write_abomonated<V: Abomonation>(
        &self,
        instance: &Instance<'a, F, C>,
        data: &V,
    ) -> Result<(), Error> {
        let mut file = instance.create(&self.dir)?;
        unsafe { encode(data, &mut file).expect("failed to encode") };
        Ok(())
    }
}
