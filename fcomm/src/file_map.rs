use std::fs::create_dir_all;
use std::io::Error;
use std::marker::PhantomData;
use std::path::{Path, PathBuf};

use libipld::Cid;

use crate::{FileStore, Key};

pub fn data_dir() -> PathBuf {
    match std::env::var("FCOMM_DATA_PATH") {
        Ok(name) => name.into(),
        Err(_) => PathBuf::from("/tmp/fcomm_data/"),
    }
}

pub struct FileMap<T: Key + FileStore> {
    dir: PathBuf,
    _t: PhantomData<T>,
}

impl<'a, T: Key + FileStore> FileMap<T> {
    pub fn new<P: AsRef<Path>>(name: P) -> Result<Self, Error> {
        let data_dir = data_dir();
        let dir = PathBuf::from(&data_dir).join(name.as_ref());
        create_dir_all(&dir)?;

        Ok(Self {
            dir,
            _t: Default::default(),
        })
    }

    fn key_path(&self, key: Cid) -> PathBuf {
        self.dir.join(PathBuf::from(key.to_string()))
    }

    pub fn get(&self, key: Cid) -> Option<T> {
        dbg!(self.key_path(key));
        T::read_from_path(self.key_path(key)).ok()
    }

    pub fn set(&self, key: Cid, data: &T) -> Result<(), Error> {
        data.write_to_path(self.key_path(key));
        Ok(())
    }
}
