use std::fs::create_dir_all;
use std::io::Error;
use std::marker::PhantomData;
use std::path::{Path, PathBuf};

use crate::FileStore;

pub fn data_dir() -> PathBuf {
    match std::env::var("FCOMM_DATA_PATH") {
        Ok(name) => name.into(),
        Err(_) => PathBuf::from("/var/tmp/fcomm_data/"),
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

    pub fn set(&self, key: K, data: &V) -> Result<(), Error> {
        data.write_to_path(self.key_path(&key));
        Ok(())
    }
}
