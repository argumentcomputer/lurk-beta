use std::{
    collections::{hash_map::Entry, HashMap},
    path::Path,
    sync::{Arc, Mutex},
};

use log::info;
use once_cell::sync::Lazy;
use tap::TapFallible;

use crate::{coprocessor::Coprocessor, eval::lang::Lang, proof::nova::PublicParams};
use crate::{proof::nova::CurveCycleEquipped, public_parameters::error::Error};

use super::disk_cache::PublicParamDiskCache;

type AnyMap = anymap::Map<dyn core::any::Any + Send + Sync>;
type PublicParamMap<F, C> = HashMap<usize, Arc<PublicParams<'static, F, C>>>;

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
        Fn: FnOnce(Arc<Lang<F, C>>) -> Arc<PublicParams<'static, F, C>>,
    >(
        &'static self,
        rc: usize,
        default: Fn,
        lang: Arc<Lang<F, C>>,
        disk_cache_path: Option<&Path>,
    ) -> Result<Arc<PublicParams<'static, F, C>>, Error> {
        // subdirectory search
        let disk_cache = PublicParamDiskCache::new(disk_cache_path).unwrap();
        // use the cached language key
        let lang_key = lang.key();
        // Sanity-check: we're about to use a lang-dependent disk cache, which should be specialized
        // for this lang/coprocessor.
        let key = format!("public-params-rc-{rc}-coproc-{lang_key}");
        // read the file if it exists, otherwise initialize
        if let Ok(pp) = disk_cache.get(&key) {
            info!("Using disk-cached public params for lang {lang_key}");
            Ok(Arc::new(pp))
        } else {
            let pp = default(lang);
            disk_cache
                .set(&key, &*pp)
                .tap_ok(|_| info!("Writing public params to disk-cache for lang {lang_key}"))?;
            Ok(pp)
        }
    }

    /// Check if params for this Coproc are in registry, if so, return them.
    /// Otherwise, initialize with the passed in function.
    pub(crate) fn get_from_mem_cache_or_update_with<
        F: CurveCycleEquipped,
        C: Coprocessor<F> + 'static,
        Fn: FnOnce(Arc<Lang<F, C>>) -> Arc<PublicParams<'static, F, C>>,
    >(
        &'static self,
        rc: usize,
        default: Fn,
        lang: Arc<Lang<F, C>>,
        disk_cache_path: Option<&Path>,
    ) -> Result<Arc<PublicParams<'static, F, C>>, Error>
    where
        F::CK1: Sync + Send,
        F::CK2: Sync + Send,
    {
        // re-grab the lock
        let mut mem_cache = self.mem_cache.lock().unwrap();
        // retrieve the per-Coproc public param table
        let entry = mem_cache.entry::<PublicParamMap<F, C>>();
        // deduce the map and populate it if needed
        let param_entry = entry.or_insert_with(HashMap::new);
        match param_entry.entry(rc) {
            Entry::Occupied(o) => Ok(o.into_mut()),
            Entry::Vacant(v) => {
                let val =
                    self.get_from_disk_cache_or_update_with(rc, default, lang, disk_cache_path)?;
                Ok(v.insert(val))
            }
        }
        .cloned()
    }
}
