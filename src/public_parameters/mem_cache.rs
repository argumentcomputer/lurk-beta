use std::{
    collections::{hash_map::Entry, HashMap},
    sync::{Arc, Mutex},
};

use abomonation::{decode, Abomonation};
use nova::traits::Engine;
use once_cell::sync::Lazy;
use tap::TapFallible;
use tracing::{info, warn};

use crate::proof::nova::C1LEM;
use crate::{
    coprocessor::Coprocessor,
    proof::nova::{PublicParams, E1, E2},
};
use crate::{proof::nova::CurveCycleEquipped, public_parameters::error::Error};

use super::{
    disk_cache::{public_params_dir, DiskCache},
    instance::Instance,
};

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
        'a,
        F: CurveCycleEquipped,
        C: Coprocessor<F> + 'static,
        Fn: FnOnce(&Instance<'static, F, C>) -> Arc<PublicParams<F, C1LEM<'a, F, C>>>,
    >(
        &'static self,
        instance: &Instance<'static, F, C>,
        default: Fn,
    ) -> Result<Arc<PublicParams<F, C1LEM<'a, F, C>>>, Error>
    where
        <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
        <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    {
        // subdirectory search
        let disk_cache = DiskCache::new(public_params_dir()).unwrap();

        // read the file if it exists, otherwise initialize
        if instance.abomonated {
            let mut bytes = vec![];
            match disk_cache.read_bytes(instance, &mut bytes) {
                Ok(()) => {
                    info!("loading abomonated {}", instance.key());
                    let (pp, rest) =
                        unsafe { decode::<PublicParams<F, C1LEM<'a, F, C>>>(&mut bytes).unwrap() };
                    assert!(rest.is_empty());
                    Ok(Arc::new(pp.clone())) // this clone is VERY expensive
                }
                Err(Error::IO(e)) => {
                    warn!("{e}");
                    info!("Generating fresh public parameters");
                    let pp = default(instance);
                    // maybe just directly write
                    disk_cache
                        .write_abomonated(instance, &*pp)
                        .tap_ok(|_| {
                            info!("writing public params to disk-cache: {}", instance.key())
                        })
                        .map_err(|e| Error::Cache(format!("Disk write error: {e}")))?;
                    Ok(pp)
                }
                _ => unreachable!(),
            }
        } else {
            // read the file if it exists, otherwise initialize
            if let Ok(pp) = disk_cache.read(instance) {
                info!("loading abomonated {}", instance.key());
                Ok(Arc::new(pp))
            } else {
                let pp = default(instance);
                disk_cache
                    .write(instance, &*pp)
                    .tap_ok(|_| info!("writing public params to disk-cache: {}", instance.key()))
                    .map_err(|e| Error::Cache(format!("Disk write error: {e}")))?;
                Ok(pp)
            }
        }
    }

    /// Check if params for this Coproc are in registry, if so, return them.
    /// Otherwise, initialize with the passed in function.
    pub(crate) fn get_from_mem_cache_or_update_with<
        F: CurveCycleEquipped,
        C: Coprocessor<F> + 'static,
        Fn: FnOnce(&Instance<'static, F, C>) -> Arc<PublicParams<F, C1LEM<'static, F, C>>>,
    >(
        &'static self,
        instance: &Instance<'static, F, C>,
        default: Fn,
    ) -> Result<Arc<PublicParams<F, C1LEM<'static, F, C>>>, Error>
    where
        <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
        <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    {
        // re-grab the lock
        let mut mem_cache = self.mem_cache.lock().unwrap();
        // retrieve the per-Coproc public param table
        let entry = mem_cache.entry::<PublicParamMap<F, C1LEM<'static, F, C>>>();
        // deduce the map and populate it if needed
        let param_entry = entry.or_default();
        match param_entry.entry((instance.rc, instance.abomonated)) {
            Entry::Occupied(o) => Ok(o.into_mut()),
            Entry::Vacant(v) => {
                let val = self.get_from_disk_cache_or_update_with(instance, default)?;
                Ok(v.insert(val))
            }
        }
        .cloned() // this clone is VERY expensive
    }
}
