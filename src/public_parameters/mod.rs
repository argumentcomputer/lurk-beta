use camino::{Utf8Path, Utf8PathBuf};
use std::sync::Arc;

use crate::coprocessor::Coprocessor;
use crate::proof::nova::CurveCycleEquipped;
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

pub fn public_params<F: CurveCycleEquipped, C: Coprocessor<F> + 'static>(
    rc: usize,
    lang: Arc<Lang<F, C>>,
    disk_cache_path: &Utf8Path,
) -> Result<Arc<PublicParams<'static, F, C>>, Error>
where
    F::CK1: Sync + Send,
    F::CK2: Sync + Send,
{
    let f = |lang: Arc<Lang<F, C>>| Arc::new(nova::public_params(rc, lang));
    mem_cache::PUBLIC_PARAM_MEM_CACHE.get_from_mem_cache_or_update_with(
        rc,
        f,
        lang,
        disk_cache_path,
    )
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
        // Without disk cache, writes to tmpfile
        let _public_params = public_params(10, lang.clone(), &public_params_dir).unwrap();
        // With disk cache, reads from tmpfile
        let _public_params = public_params(10, lang, &public_params_dir).unwrap();
    }
}
