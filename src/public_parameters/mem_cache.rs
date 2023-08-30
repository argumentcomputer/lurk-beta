use std::{
    collections::{hash_map::Entry, HashMap},
    sync::{Arc, Mutex},
};

use abomonation::{decode, Abomonation};
use camino::Utf8Path;
use log::info;
use nova::traits::Group;
use once_cell::sync::Lazy;
use tap::TapFallible;

use crate::{
    coprocessor::Coprocessor,
    eval::lang::Lang,
    proof::nova::{PublicParams, C1, G1, G2},
};
use crate::{proof::nova::CurveCycleEquipped, public_parameters::error::Error};

use super::disk_cache::PublicParamDiskCache;

type AnyMap = anymap::Map<dyn core::any::Any + Send + Sync>;
type PublicParamMap<F, C> = HashMap<(usize, bool), Arc<PublicParams<F, C1<'static, F, C>>>>;

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
        Fn: FnOnce(Arc<Lang<F, C>>) -> Arc<PublicParams<F, C1<'static, F, C>>>,
    >(
        &'static self,
        rc: usize,
        abomonated: bool,
        default: Fn,
        lang: Arc<Lang<F, C>>,
        disk_cache_path: &Utf8Path,
    ) -> Result<Arc<PublicParams<F, C1<'static, F, C>>>, Error>
    where
        <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
        <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    {
        // subdirectory search
        let disk_cache = PublicParamDiskCache::new(disk_cache_path).unwrap();
        // use the cached language key
        let lang_key = lang.key();
        let quick_suffix = if abomonated { "-abomonated" } else { "" };
        // Sanity-check: we're about to use a lang-dependent disk cache, which should be specialized
        // for this lang/coprocessor.
        let key = format!("public-params-rc-{rc}-coproc-{lang_key}{quick_suffix}");
        // read the file if it exists, otherwise initialize
        if abomonated {
            match disk_cache.get_raw_bytes(&key) {
                Ok(mut bytes) => {
                    info!("Using abomonated public params for lang {lang_key}");
                    let (pp, rest) =
                        unsafe { decode::<PublicParams<F, C1<'_, F, C>>>(&mut bytes).unwrap() };
                    assert!(rest.is_empty());
                    Ok(Arc::new(pp.clone())) // this clone is VERY expensive
                }
                Err(e) => {
                    eprintln!("{e}");
                    let pp = default(lang);
                    // maybe just directly write
                    disk_cache
                        .set_abomonated(&key, &*pp)
                        .tap_ok(|_| info!("Writing public params to disk-cache: {}", lang_key))
                        .map_err(|e| Error::CacheError(format!("Disk write error: {e}")))?;
                    Ok(pp)
                }
            }
        } else {
            // read the file if it exists, otherwise initialize
            if let Ok(pp) = disk_cache.get(&key) {
                info!("Using disk-cached public params for lang {lang_key}");
                Ok(Arc::new(pp))
            } else {
                let pp = default(lang);
                disk_cache
                    .set(&key, &*pp)
                    .tap_ok(|_| info!("Writing public params to disk-cache: {}", lang_key))
                    .map_err(|e| Error::CacheError(format!("Disk write error: {e}")))?;
                Ok(pp)
            }
        }
    }

    /// Check if params for this Coproc are in registry, if so, return them.
    /// Otherwise, initialize with the passed in function.
    pub(crate) fn get_from_mem_cache_or_update_with<
        F: CurveCycleEquipped,
        C: Coprocessor<F> + 'static,
        Fn: FnOnce(Arc<Lang<F, C>>) -> Arc<PublicParams<F, C1<'static, F, C>>>,
    >(
        &'static self,
        rc: usize,
        abomonated: bool,
        default: Fn,
        lang: Arc<Lang<F, C>>,
        disk_cache_path: &Utf8Path,
    ) -> Result<Arc<PublicParams<F, C1<'static, F, C>>>, Error>
    where
        F::CK1: Sync + Send,
        F::CK2: Sync + Send,
        <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
        <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    {
        // re-grab the lock
        let mut mem_cache = self.mem_cache.lock().unwrap();
        // retrieve the per-Coproc public param table
        let entry = mem_cache.entry::<PublicParamMap<F, C>>();
        // deduce the map and populate it if needed
        let param_entry = entry.or_insert_with(HashMap::new);
        match param_entry.entry((rc, abomonated)) {
            Entry::Occupied(o) => Ok(o.into_mut()),
            Entry::Vacant(v) => {
                let val = self.get_from_disk_cache_or_update_with(
                    rc,
                    true,
                    default,
                    lang,
                    disk_cache_path,
                )?;
                Ok(v.insert(val))
            }
        }
        .cloned() // this clone is VERY expensive
    }
}
