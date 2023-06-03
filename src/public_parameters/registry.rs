use std::{
    collections::{hash_map::Entry, HashMap},
    sync::{Arc, Mutex},
};

use abomonation::{decode, encode};
use bincode::config::WithOtherEndian;
use once_cell::sync::Lazy;
use pasta_curves::pallas;
use serde::{de::DeserializeOwned, Serialize};
use tap::TapFallible;

use crate::public_parameters::Error;
use crate::{coprocessor::Coprocessor, eval::lang::Lang, proof::nova::PublicParams};

use super::file_map::FileIndex;

type S1 = pallas::Scalar;
type AnyMap = anymap::Map<dyn anymap::any::Any + Send + Sync>;
type PublicParamMemCache<C> = HashMap<(usize, bool), Arc<PublicParams<'static, C>>>;

/// This is a global registry for Coproc-specific parameters.
/// It is used to cache parameters for each Coproc, so that they are not
/// re-initialized on each call to `eval`.
/// The use of AnyMap is a workaround for the fact that we need static storage for generic parameters,
/// noting that this is not possible in Rust.
#[derive(Clone)]
pub(crate) struct Registry {
    registry: Arc<Mutex<AnyMap>>,
}

pub(crate) static CACHE_REG: Lazy<Registry> = Lazy::new(|| Registry {
    registry: Arc::new(Mutex::new(AnyMap::new())),
});

impl Registry {
    fn get_from_file_cache_or_update_with<C, F, B, T>(
        &'static self,
        rc: usize,
        lang: Arc<Lang<S1, C>>,
        abomonated: bool,
        default: F,
        bind: B,
    ) -> Result<Arc<PublicParams<'static, C>>, Error>
    where
        C: Coprocessor<S1> + Serialize + DeserializeOwned + 'static,
        F: FnOnce(Arc<Lang<S1, C>>) -> Arc<PublicParams<'static, C>>,
        B: Fn(PublicParams<'static, C>) -> T,
    {
        // subdirectory search
        let disk_cache = FileIndex::new("public_params").unwrap();
        // use the cached language key
        let lang_key = lang.key();
        let quick_suffix = if quick { "-quick" } else { "" };
        // Sanity-check: we're about to use a lang-dependent disk cache, which should be specialized
        // for this lang/coprocessor.
        let key = format!("public-params-rc-{rc}-coproc-{lang_key}{quick_suffix}");
        if quick {
            if let Some(mut bytes) =
                disk_cache.get_mmap_bytes_with_timing(&key, &"public params".to_string())
            {
                let (pp, remaining) =
                    unsafe { decode::<PublicParams<'static, C>>(&mut bytes).unwrap() };
                assert!(remaining.len() == 0);
                Ok(Arc::new(pp.clone()))
            } else {
                let pp = default(lang);
                let mut bytes = Vec::new();
                unsafe { encode(&*pp, &mut bytes)? };
                // maybe just directly write
                disk_cache
                    .set::<Vec<u8>>(key, &bytes)
                    .tap_ok(|_| eprintln!("Writing public params to disk-cache: {}", lang_key))
                    .map_err(|e| Error::CacheError(format!("Disk write error: {e}")))?;
                Ok(pp)
            }
        } else {
            // read the file if it exists, otherwise initialize
            if let Some(pp) = disk_cache.get::<PublicParams<'static, C>>(&key) {
                eprintln!(
                    "Using disk-cached public params for lang {} (quick = {quick})",
                    lang_key
                );
                Ok(Arc::new(pp))
            } else {
                let pp = default(lang);
                disk_cache
                    .set(key, &*pp)
                    .tap_ok(|_| eprintln!("Writing public params to disk-cache: {}", lang_key))
                    .map_err(|e| Error::CacheError(format!("Disk write error: {e}")))?;
                Ok(pp)
            }
        }
    }

    /// Check if params for this Coproc are in registry, if so, return them.
    /// Otherwise, initialize with the passed in function.
    pub(crate) fn get_coprocessor_or_update_with<C, F, B, T>(
        &'static self,
        rc: usize,
        lang: Arc<Lang<S1, C>>,
        abomonated: bool,
        default: F,
        bind: B,
    ) -> T
    where
        C: Coprocessor<S1> + Serialize + DeserializeOwned + 'static,
        F: FnOnce(Arc<Lang<S1, C>>) -> Arc<PublicParams<'static, C>>,
        B: FnOnce(&PublicParams<'static, C>) -> T,
    {
        // re-grab the lock
        let mut registry = self.registry.lock().unwrap();
        // retrieve the per-Coproc public param table
        let entry = registry.entry::<PublicParamMemCache<C>>();
        // deduce the map and populate it if needed
        let param_entry = entry.or_insert_with(HashMap::new);
        match param_entry.entry((rc, abomonated)) {
            Entry::Occupied(o) => {
                let pp = o.into_mut().as_ref();
                bind(pp)
            },
            Entry::Vacant(v) => {
                let val = self.get_from_file_cache_or_update_with(rc, quick, default, lang)?;
                Ok(v.insert(val))
            }
        }
    }

    /// Check if params for this Coproc are in registry,
    /// if one exists, we proceed with the computation in `bind`
    /// otherwise, initialize with `default` and then proceed with `bind`
    pub(crate) fn with_get_coprocessor<
        C: Coprocessor<S1> + Serialize + DeserializeOwned + 'static,
        F: FnOnce(Arc<Lang<S1, C>>) -> Arc<PublicParams<'static, C>>,
        B: FnOnce(&PublicParams<'static, C>) -> T,
        T,
    >(
        &'static self,
        rc: usize,
        quick: bool,
        lang: Arc<Lang<S1, C>>,
        default: F,
        bind: B,
    ) -> T {
        let mut registry = self.registry.lock().unwrap();
        // retrieve the per-Coproc public param table
        let entry = registry.entry::<PublicParamMemCache<C>>();
        // deduce the map and populate it if needed
        let param_entry = entry.or_insert_with(HashMap::new);
        match param_entry.entry((rc, quick)) {
            Entry::Occupied(o) => {
                let pp = o.into_mut().as_ref();
                bind(pp)
            }
            Entry::Vacant(v) => {
                let val = self.get_from_file_cache_or_update_with(rc, quick, default, lang)?;
                Ok(v.insert(val))
            }
        }
        .cloned();
        unimplemented!()
    }
}
