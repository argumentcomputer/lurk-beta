use std::{
    collections::{hash_map::Entry, HashMap},
    sync::{Arc, Mutex},
};

use abomonation::decode;
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
    fn get_from_file_cache_or_update_with<
        C: Coprocessor<S1> + Serialize + DeserializeOwned + 'static,
        F: FnOnce(Arc<Lang<S1, C>>) -> Arc<PublicParams<'static, C>>,
    >(
        &'static self,
        rc: usize,
        abomonated: bool,
        default: F,
        lang: Arc<Lang<S1, C>>,
    ) -> Result<Arc<PublicParams<'static, C>>, Error> {
        // subdirectory search
        let disk_cache = FileIndex::new("public_params").unwrap();
        // use the cached language key
        let lang_key = lang.key();
        let quick_suffix = if abomonated { "-abomonated" } else { "" };
        // Sanity-check: we're about to use a lang-dependent disk cache, which should be specialized
        // for this lang/coprocessor.
        let key = format!("public-params-rc-{rc}-coproc-{lang_key}{quick_suffix}");
        if abomonated {
            match disk_cache.get_raw_bytes(&key) {
                Ok(mut bytes) => {
                    eprintln!("Using abomonated public params for lang {}", lang_key);
                    let (pp, rest) = unsafe { decode::<PublicParams<'_, C>>(&mut bytes).unwrap() };
                    assert!(rest.is_empty());
                    Ok(Arc::new(pp.clone())) // this clone is VERY expensive
                }
                Err(e) => {
                    eprintln!("{e}");
                    let pp = default(lang);
                    // maybe just directly write
                    disk_cache
                        .set_abomonated(&key, &*pp)
                        .tap_ok(|_| eprintln!("Writing public params to disk-cache: {}", lang_key))
                        .map_err(|e| Error::CacheError(format!("Disk write error: {e}")))?;
                    Ok(pp)
                }
            }
        } else {
            // read the file if it exists, otherwise initialize
            if let Some(pp) = disk_cache.get::<PublicParams<'static, C>>(&key) {
                eprintln!("Using disk-cached public params for lang {}", lang_key);
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
    pub(crate) fn get_coprocessor_or_update_with<
        C: Coprocessor<S1> + Serialize + DeserializeOwned + 'static,
        F: FnOnce(Arc<Lang<S1, C>>) -> Arc<PublicParams<'static, C>>,
    >(
        &'static self,
        rc: usize,
        abomonated: bool,
        default: F,
        lang: Arc<Lang<S1, C>>,
    ) -> Result<Arc<PublicParams<'static, C>>, Error> {
        // re-grab the lock
        let mut registry = self.registry.lock().unwrap();
        // retrieve the per-Coproc public param table
        let entry = registry.entry::<PublicParamMemCache<C>>();
        // deduce the map and populate it if needed
        let param_entry = entry.or_insert_with(HashMap::new);
        match param_entry.entry((rc, abomonated)) {
            Entry::Occupied(o) => Ok(o.into_mut()),
            Entry::Vacant(v) => {
                let val = self.get_from_file_cache_or_update_with(rc, abomonated, default, lang)?;
                Ok(v.insert(val))
            }
        }
        .cloned() // this clone is VERY expensive
    }
}
