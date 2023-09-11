use ::nova::traits::Group;
use abomonation::{decode, Abomonation};
use camino::{Utf8Path, Utf8PathBuf};
use std::sync::Arc;

use crate::coprocessor::Coprocessor;
use crate::proof::nova::{CurveCycleEquipped, G1, G2};
use crate::proof::MultiFrameTrait;
use crate::{
    eval::lang::Lang,
    proof::nova::{self, PublicParams},
};

mod disk_cache;
pub mod error;
mod mem_cache;

use crate::public_parameters::error::Error;

#[cfg(not(target_arch = "wasm32"))]
pub fn public_params_default_dir() -> Utf8PathBuf {
    let home = home::home_dir().unwrap();
    Utf8PathBuf::from_path_buf(home.join(".lurk/public_params"))
        .expect("path contains invalid Unicode")
}

#[cfg(target_arch = "wasm32")]
pub fn public_params_default_dir() -> Utf8PathBuf {
    Utf8PathBuf::from(".lurk/public_params")
}

pub fn public_params<F: CurveCycleEquipped, C: Coprocessor<F> + 'static, M: MultiFrameTrait<'static, F, C> + 'static>(
    rc: usize,
    abomonated: bool,
    lang: Arc<Lang<F, C>>,
    disk_cache_path: &Utf8Path,
) -> Result<Arc<PublicParams<F, M>>, Error>
where
    F::CK1: Sync + Send,
    F::CK2: Sync + Send,
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    let f = |lang: Arc<Lang<F, C>>| Arc::new(nova::public_params::<F, C, M>(rc, lang));
    mem_cache::PUBLIC_PARAM_MEM_CACHE.get_from_mem_cache_or_update_with(
        rc,
        abomonated,
        f,
        lang,
        disk_cache_path,
    )
}

/// Attempts to extract abomonated public parameters.
/// To avoid all copying overhead, we zerocopy all of the data within the file;
/// this leads to extremely high performance, but restricts the lifetime of the data
/// to the lifetime of the file. Thus, we cannot pass a reference out and must
/// rely on a closure to capture the data and continue the computation in `bind`.
pub fn with_public_params<'a, F: CurveCycleEquipped, C, M, Fn, T>(
    rc: usize,
    lang: Arc<Lang<F, C>>,
    bind: Fn,
) -> Result<T, Error>
where
    C: Coprocessor<F> + 'a,
    M: MultiFrameTrait<'a, F, C>,
    Fn: FnOnce(&PublicParams<F, M>) -> T,
    <<G1<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    let disk_cache =
        disk_cache::PublicParamDiskCache::<F, C, M>::new(&public_params_default_dir()).unwrap();
    // use the cached language key
    let lang_key = lang.key();
    // Sanity-check: we're about to use a lang-dependent disk cache, which should be specialized
    // for this lang/coprocessor.
    let key = format!("public-params-rc-{rc}-coproc-{lang_key}-abomonated");

    match disk_cache.get_raw_bytes(&key) {
        Ok(mut bytes) => {
            if let Some((pp, remaining)) = unsafe { decode(&mut bytes) } {
                assert!(remaining.is_empty());
                eprintln!("Using disk-cached public params for lang {}", lang_key);
                Ok(bind(pp))
            } else {
                eprintln!("failed to decode bytes");
                let pp = nova::public_params(rc, lang);
                let mut bytes = Vec::new();
                unsafe { abomonation::encode(&pp, &mut bytes)? };
                // maybe just directly write
                disk_cache
                    .set_abomonated(&key, &pp)
                    .map_err(|e| Error::CacheError(format!("Disk write error: {e}")))?;
                Ok(bind(&pp))
            }
        }
        Err(e) => {
            eprintln!("{e}");
            let pp = nova::public_params(rc, lang);
            // maybe just directly write
            disk_cache
                .set_abomonated(&key, &pp)
                .map_err(|e| Error::CacheError(format!("Disk write error: {e}")))?;
            Ok(bind(&pp))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::lang::Coproc;
    use pasta_curves::pallas::Scalar as S1;
    use tempfile::Builder;

    #[test]
    // Note: No Eq instance for PublicParams currently, just testing disk read/write
    fn serde_public_params_roundtrip() {
        let tmp_dir = Builder::new().prefix("tmp").tempdir().unwrap();
        let public_params_dir = Utf8Path::from_path(tmp_dir.path())
            .unwrap()
            .join("public_params");

        let lang: Arc<Lang<S1, Coproc<S1>>> = Arc::new(Lang::new());
        type OG = crate::proof::nova::C1<'static, S1, Coproc<S1>>;
        // Without disk cache, writes to tmpfile
        let _public_params =
            public_params::<S1, Coproc<S1>, OG>(10, true, lang.clone(), &public_params_dir)
                .unwrap();
        // With disk cache, reads from tmpfile
        let _public_params =
            public_params::<S1, Coproc<S1>, OG>(10, true, lang, &public_params_dir).unwrap();
    }
}
