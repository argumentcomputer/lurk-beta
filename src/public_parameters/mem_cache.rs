use std::{
    collections::{hash_map::Entry, HashMap},
    sync::{Arc, Mutex},
};

use abomonation::Abomonation;
use camino::Utf8Path;
use nova::traits::Group;
use once_cell::sync::Lazy;
use tap::TapFallible;
use tracing::{info, warn};

use crate::proof::MultiFrameTrait;
use crate::{
    coprocessor::Coprocessor,
    proof::nova::{PublicParams, G1, G2},
};
use crate::{proof::nova::CurveCycleEquipped, public_parameters::error::Error};

use super::{disk_cache::DiskCache, instance::Instance};

type AnyMap = anymap::Map<dyn core::any::Any + Send + Sync>;
type PublicParamMap<F, M> = HashMap<(usize, bool), Arc<PublicParams<F, M>>>;

/// This is a global registry for Coproc-specific parameters.
/// It is used to cache parameters for each Coproc, so that they are not
/// re-initialized on each call to `eval`.
/// The use of AnyMap is a workaround for the fact that we need static storage for generic parameters,
/// noting that this is not possible in Rust.
#[derive(Clone)]
pub(crate) struct PublicParamMemCache {
    mem_cache: Arc<Mutex<AnyMap>>,
}

pub(crate) static PUBLIC_PARAM_MEM_CACHE: Lazy<PublicParamMemCache> =
    Lazy::new(|| PublicParamMemCache {
        mem_cache: Arc::new(Mutex::new(AnyMap::new())),
    });

impl PublicParamMemCache {
    fn get_from_disk_cache_or_update_with<
        F: CurveCycleEquipped,
        C: Coprocessor<F> + 'static,
        M: MultiFrameTrait<'static, F, C>,
        Fn: FnOnce(&Instance<'static, F, C, M>) -> Arc<PublicParams<F, M>>,
    >(
        &'static self,
        instance: &Instance<'static, F, C, M>,
        default: Fn,
        disk_cache_path: &Utf8Path,
    ) -> Result<Arc<PublicParams<F, M>>, Error>
    where
        <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
        <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    {
        // subdirectory search
        let disk_cache = DiskCache::new(disk_cache_path).unwrap();

        // read the file if it exists, otherwise initialize
        if instance.abomonated {
            match disk_cache.read_abomonated(instance) {
                Ok(pp) => {
                    // info!("loading abomonated {}", instance.key());
                    Ok(Arc::new(pp))
                }
                Err(e) => {
                    warn!("{e}");
                    info!("Generating fresh public parameters");
                    let pp = default(instance);
                    // maybe just directly write
                    disk_cache
                        .write_abomonated(instance, &*pp)
                        .tap_ok(|_| {
                            info!("writing public params to disk-cache: {}", instance.key())
                        })
                        .map_err(|e| Error::CacheError(format!("Disk write error: {e}")))?;
                    Ok(pp)
                }
            }
        } else {
            todo!("not supported!")
        }
    }

    /// Check if params for this Coproc are in registry, if so, return them.
    /// Otherwise, initialize with the passed in function.
    pub(crate) fn get_from_mem_cache_or_update_with<
        F: CurveCycleEquipped,
        C: Coprocessor<F> + 'static,
        M: MultiFrameTrait<'static, F, C>,
        Fn: FnOnce(&Instance<'static, F, C, M>) -> Arc<PublicParams<F, M>>,
    >(
        &'static self,
        instance: &Instance<'static, F, C, M>,
        default: Fn,
        disk_cache_path: &Utf8Path,
    ) -> Result<Arc<PublicParams<F, M>>, Error>
    where
        F::CK1: Sync + Send,
        F::CK2: Sync + Send,
        <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
        <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    {
        // re-grab the lock
        let mut mem_cache = self.mem_cache.lock().unwrap();
        // retrieve the per-Coproc public param table
        let entry = mem_cache.entry::<PublicParamMap<F, M>>();
        // deduce the map and populate it if needed
        let param_entry = entry.or_insert_with(HashMap::new);
        match param_entry.entry((instance.rc, instance.abomonated)) {
            Entry::Occupied(o) => Ok(o.into_mut()),
            Entry::Vacant(v) => {
                let val =
                    self.get_from_disk_cache_or_update_with(instance, default, disk_cache_path)?;
                Ok(v.insert(val))
            }
        }
        .cloned() // this clone is VERY expensive
    }
}
