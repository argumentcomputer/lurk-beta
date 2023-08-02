use std::fs::create_dir_all;
use std::fs::File;
use std::io::{self, BufReader, BufWriter};
use std::marker::PhantomData;
use std::path::{Path, PathBuf};

use lurk::public_parameters::error::Error;

use serde::{Deserialize, Serialize};

pub(crate) fn data_dir() -> PathBuf {
    match std::env::var("FCOMM_DATA_PATH") {
        Ok(name) => name.into(),
        Err(_) => PathBuf::from("/var/tmp/fcomm_data/"),
    }
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
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        bincode::deserialize_from(reader)
            .map_err(|e| Error::CacheError(format!("Cache deserialization error: {}", e)))
    }

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

pub struct FileMap<K: ToString, V: FileStore> {
    dir: PathBuf,
    _t: PhantomData<(K, V)>,
}

impl<K: ToString, V: FileStore> FileMap<K, V> {
    pub fn new<P: AsRef<Path>>(name: P) -> Result<Self, Error> {
        let data_dir = data_dir();
        let dir = PathBuf::from(&data_dir).join(name.as_ref());
        create_dir_all(&dir)?;

        Ok(Self {
            dir,
            _t: Default::default(),
        })
    }

    fn key_path(&self, key: &K) -> PathBuf {
        self.dir.join(PathBuf::from(key.to_string()))
    }

    pub fn get(&self, key: &K) -> Option<V> {
        self.key_path(key);
        V::read_from_path(self.key_path(key)).ok()
    }

    pub fn set(&self, key: &K, data: &V) -> Result<(), Error> {
        data.write_to_path(self.key_path(key));
        Ok(())
    }
}
