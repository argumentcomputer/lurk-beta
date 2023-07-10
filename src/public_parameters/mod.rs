use std::fs::File;
use std::io::{self, BufReader, BufWriter};
use std::path::Path;
use std::sync::Arc;

use crate::coprocessor::Coprocessor;
use crate::{
    eval::lang::Lang,
    proof::nova::{self, PublicParams},
};
use pasta_curves::pallas;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

pub mod error;
pub mod file_map;
mod registry;

use crate::public_parameters::error::Error;

pub type S1 = pallas::Scalar;

pub fn public_params<C: Coprocessor<S1> + Serialize + DeserializeOwned + 'static>(
    rc: usize,
    lang: Arc<Lang<S1, C>>,
) -> Result<Arc<PublicParams<'static, C>>, Error> {
    let f = |lang: Arc<Lang<S1, C>>| Arc::new(nova::public_params(rc, lang));
    registry::CACHE_REG.get_coprocessor_or_update_with(rc, f, lang)
}

pub trait FileStore
where
    Self: Sized,
{
    fn write_to_path<P: AsRef<Path>>(&self, path: P);
    fn write_to_json_path<P: AsRef<Path>>(&self, path: P);
    fn read_from_path<P: AsRef<Path>>(path: P) -> Result<Self, Error>;
    fn read_from_json_path<P: AsRef<Path>>(path: P) -> Result<Self, Error>;
    fn read_from_stdin() -> Result<Self, Error>;
}

impl<T: Serialize> FileStore for T
where
    for<'de> T: Deserialize<'de>,
{
    fn write_to_path<P: AsRef<Path>>(&self, path: P) {
        let file = File::create(path).expect("failed to create file");
        let writer = BufWriter::new(&file);

        bincode::serialize_into(writer, &self).expect("failed to write file");
    }

    fn write_to_json_path<P: AsRef<Path>>(&self, path: P) {
        let file = File::create(path).expect("failed to create file");
        let writer = BufWriter::new(&file);

        serde_json::to_writer(writer, &self).expect("failed to write file");
    }

    fn read_from_path<P: AsRef<Path>>(path: P) -> Result<Self, Error> {
        use std::io::Read;
        // FIXME: due to an bug in bincode, we must first copy out
        // all the bytes before passing to `bincode::deserialize`.
        // See: https://github.com/bincode-org/bincode/issues/633
        let mut file = File::open(path)?;
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes).unwrap();
        bincode::deserialize(&bytes).map_err(|e| {
            eprintln!("{}", e);
            Error::CacheError(e.to_string())
        })
    }
    //    let file = File::open(path)?;
    //    let reader = BufReader::new(file);
    //    bincode::deserialize_from(reader)
    //        .map_err(|e| Error::CacheError(format!("Cache deserialization error: {}", e)))
    //}

    fn read_from_json_path<P: AsRef<Path>>(path: P) -> Result<Self, Error> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        Ok(serde_json::from_reader(reader)?)
    }

    fn read_from_stdin() -> Result<Self, Error> {
        let reader = BufReader::new(io::stdin());
        Ok(serde_json::from_reader(reader).expect("failed to read from stdin"))
    }
}
