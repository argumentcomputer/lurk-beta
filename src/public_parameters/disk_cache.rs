use std::fs::create_dir_all;
use std::marker::PhantomData;

use abomonation::{decode, encode, Abomonation};
use camino::{Utf8Path, Utf8PathBuf};
use memmap::MmapMut;
use nova::traits::Group;

use crate::coprocessor::Coprocessor;
use crate::proof::nova::{CurveCycleEquipped, G1, G2};
use crate::proof::MultiFrameTrait;
use crate::public_parameters::error::Error;

use super::instance::Instance;

pub(crate) struct DiskCache<'a, F, C, M>
where
    F: CurveCycleEquipped,
    C: Coprocessor<F> + 'a,
    M: MultiFrameTrait<'a, F, C>,
{
    dir: Utf8PathBuf,
    _t: PhantomData<(&'a (), F, C, M)>,
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a, M: MultiFrameTrait<'a, F, C>>
    DiskCache<'a, F, C, M>
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

    #[tracing::instrument(skip_all, name = "read_abomonated")]
    pub(crate) fn read_abomonated<V: Abomonation + Clone>(
        &self,
        instance: &Instance<'a, F, C, M>,
    ) -> Result<V, Error> {
        let file = instance.open(&self.dir)?;
        unsafe {
            let mut mmap = MmapMut::map_mut(&file)?;
            let (data, rest) = tracing::info_span!("decode").in_scope(|| {
                decode::<V>(&mut mmap).ok_or(Error::CacheError("failed to decode bytes".into()))
            })?;
            assert!(rest.is_empty());
            Ok(tracing::info_span!("clone").in_scope(|| data.clone()))
        }
    }

    pub(crate) fn read_mmap(&self, instance: &Instance<'a, F, C, M>) -> Result<MmapMut, Error> {
        let file = instance.open(&self.dir)?;
        let mmap = unsafe { MmapMut::map_mut(&file)? };
        Ok(mmap)
    }

    pub(crate) fn write_abomonated<V: Abomonation>(
        &self,
        instance: &Instance<'a, F, C, M>,
        data: &V,
    ) -> Result<(), Error> {
        let mut file = instance.create(&self.dir)?;
        unsafe { encode(data, &mut file).expect("failed to encode") };
        Ok(())
    }
}
