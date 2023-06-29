use std::fs::{create_dir_all, File};
use std::io::{BufReader, Read};
use std::marker::PhantomData;
use std::path::{Path, PathBuf};
use std::time::Instant;
use tap::TapFallible;

use abomonation::{encode, Abomonation};

use crate::public_parameters::error::Error;
use crate::public_parameters::FileStore;

pub(crate) fn data_dir() -> PathBuf {
    match std::env::var("FCOMM_DATA_PATH") {
        Ok(name) => name.into(),
        Err(_) => PathBuf::from("/var/tmp/fcomm_data/"),
    }
}

pub(crate) struct FileIndex<K: ToString> {
    dir: PathBuf,
    _t: PhantomData<K>,
}

impl<K: ToString> FileIndex<K> {
    pub(crate) fn new<P: AsRef<Path>>(name: P) -> Result<Self, Error> {
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

    pub(crate) fn get<V: FileStore>(&self, key: &K) -> Option<V> {
        V::read_from_path(self.key_path(key)).ok()
    }

    pub(crate) fn get_raw_bytes(&self, key: &K) -> Result<Vec<u8>, Error> {
        let file = File::open(self.key_path(key))?;
        let mut reader = BufReader::new(file);
        let mut bytes = Vec::new();
        reader.read_to_end(&mut bytes)?;
        Ok(bytes)
    }

    #[allow(dead_code)]
    pub(crate) fn get_with_timing<V: FileStore>(&self, key: &K, discr: &String) -> Option<V> {
        let start = Instant::now();
        let result = V::read_from_path(self.key_path(key)).tap_err(|e| eprintln!("{e}"));
        let end = start.elapsed();
        eprintln!("Reading {discr} from disk-cache in {:?}", end);
        result.ok()
    }

    pub(crate) fn set<V: FileStore>(&self, key: K, data: &V) -> Result<(), Error> {
        data.write_to_path(self.key_path(&key));
        Ok(())
    }

    pub(crate) fn set_abomonated<V: Abomonation>(&self, key: &K, data: &V) -> Result<(), Error> {
        let mut file = File::create(self.key_path(&key))?;
        unsafe { encode(data, &mut file).expect("failed to encode") };
        Ok(())
    }

    #[allow(dead_code)]
    pub(crate) fn set_with_timing<V: FileStore>(
        &self,
        key: &K,
        data: &V,
        discr: &String,
    ) -> Result<(), Error> {
        let start = Instant::now();
        data.write_to_path(self.key_path(key));
        let end = start.elapsed();
        eprintln!("Writing {discr} to disk-cache in {:?}", end);
        Ok(())
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
