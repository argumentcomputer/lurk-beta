use std::fs::{create_dir_all, File};
use std::io::{BufReader, BufWriter};
use std::marker::PhantomData;
use std::path::{Path, PathBuf};

use crate::coprocessor::Coprocessor;
use crate::proof::nova::{CurveCycleEquipped, PublicParams};
use crate::public_parameters::error::Error;

pub(crate) struct PublicParamDiskCache<F, C>
where
    F: CurveCycleEquipped,
    C: Coprocessor<F> + 'static,
{
    dir: PathBuf,
    _t: PhantomData<(F, C)>,
}

impl<F: CurveCycleEquipped, C: Coprocessor<F>> PublicParamDiskCache<F, C> {
    pub(crate) fn new(disk_cache_path: Option<&Path>) -> Result<Self, Error> {
        let dir = match disk_cache_path {
            Some(path) => path.to_owned(),
            None => {
                cfg_if::cfg_if! {
                    if #[cfg(not(target_arch = "wasm32"))] {
                        home::home_dir()
                            .expect("missing home directory")
                            .join(".lurk/public_params")
                    }
                    else {
                        PathBuf::from(".lurk/public_params")
                    }
                }
            }
        };
        create_dir_all(&dir)?;

        Ok(Self {
            dir,
            _t: Default::default(),
        })
    }

    fn key_path(&self, key: &str) -> PathBuf {
        self.dir.join(PathBuf::from(key))
    }

    pub(crate) fn get(&self, key: &str) -> Result<PublicParams<'static, F, C>, Error> {
        let file = File::open(self.key_path(key))?;
        let reader = BufReader::new(file);
        bincode::deserialize_from(reader).map_err(|e| {
            Error::CacheError(format!("Public param cache deserialization error: {}", e))
        })
    }

    pub(crate) fn set(&self, key: &str, data: &PublicParams<'static, F, C>) -> Result<(), Error> {
        let file = File::create(self.key_path(key)).expect("failed to create file");
        let writer = BufWriter::new(&file);
        bincode::serialize_into(writer, &data).map_err(|e| {
            Error::CacheError(format!("Public param cache serialization error: {}", e))
        })
    }
}
