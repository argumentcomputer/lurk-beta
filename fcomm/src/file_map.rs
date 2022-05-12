use std::fs::create_dir_all;
use std::io::Error;
use std::marker::PhantomData;
use std::path::{Path, PathBuf};

use crate::{FileStore, Key};

pub fn data_dir() -> PathBuf {
    match std::env::var("FCOMM_DATA_PATH") {
        Ok(name) => name.into(),
        Err(_) => PathBuf::from("/tmp/fcomm_data/"),
    }
}

pub struct FileMap<K: ToString, T: Key<K> + FileStore> {
    dir: PathBuf,
    _t: PhantomData<(K, T)>,
}

impl<'a, K: ToString + Copy, T: Key<K> + FileStore> FileMap<K, T> {
    pub fn new<P: AsRef<Path>>(name: P) -> Result<Self, Error> {
        let data_dir = data_dir();
        let dir = PathBuf::from(&data_dir).join(name.as_ref());
        create_dir_all(&dir)?;

        Ok(Self {
            dir,
            _t: Default::default(),
        })
    }

    fn key_path(&self, key: K) -> PathBuf {
        self.dir.join(PathBuf::from(key.to_string()))
    }

    pub fn get(&self, key: K) -> Option<T> {
        self.key_path(key);
        T::read_from_path(self.key_path(key)).ok()
    }

    pub fn set(&self, key: K, data: &T) -> Result<(), Error> {
        data.write_to_path(self.key_path(key));
        Ok(())
    }
}
