use std::{
    fs::File,
    io::{self, BufReader, BufWriter},
    sync::Arc,
};

use camino::Utf8Path;
use ff::PrimeField;
use nova::digest::{DigestBuilder, Digestible, HasDigest, SimpleDigestible};
use serde::{Deserialize, Serialize};

use crate::{
    coprocessor::Coprocessor,
    eval::lang::Lang,
    proof::nova::{circuit_digest, CurveCycleEquipped},
};

/// Represents one instance of a set of public parameters,
/// parameterized by the reduction count, `Lang`, and abomonation flag.
/// The digest is also computed and distinguished, so `Lang`s with the
/// same name but different circuits (perhaps due to different versions,
/// bugfixes, etc) are also distinct.
///
/// Every [Instance] should correspond to *exactly* one set of [PublicParams].
pub struct Instance<F: CurveCycleEquipped, C: Coprocessor<F>> {
    pub rc: usize,
    pub lang: Option<Arc<Lang<F, C>>>,
    pub abomonated: bool,
    pub circuit_digest: F,
}

/// What we put into the cache
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Metadata {
    pub rc: usize,
    pub lang: String,
    pub abomonated: bool,
    pub circuit_digest: String,
}

impl Metadata {
    fn from_instance<F: CurveCycleEquipped, C: Coprocessor<F>>(instance: &Instance<F, C>) -> Self {
        Metadata {
            rc: instance.rc,
            lang: instance.lang().key(),
            abomonated: instance.abomonated,
            circuit_digest: format!("{:?}", instance.circuit_digest),
        }
    }
}

impl<F: PrimeField> HasDigest<F> for Metadata {
    fn set_digest(&mut self, digest: F) {
        self.circuit_digest = format!("{:?}", digest);
    }
}

impl SimpleDigestible for Metadata {}

impl<F: CurveCycleEquipped, C: Coprocessor<F>> Instance<F, C> {
    pub fn new(rc: usize, lang: Arc<Lang<F, C>>, abomonated: bool) -> Self {
        let circuit_digest = circuit_digest(rc, lang.clone());
        Instance {
            rc,
            lang: Some(lang),
            abomonated,
            circuit_digest,
        }
    }

    /// The key (or digest) of this [Instance] used to retrieve it from the file cache
    pub fn lang(&self) -> Arc<Lang<F, C>> {
        let lang = self
            .lang
            .as_ref()
            .expect("invalid instance; lang is `None`");
        lang.clone()
    }

    /// The key (or digest) of this [Instance] used to retrieve it from the file cache
    pub fn key(&self) -> String {
        let abomonated = if self.abomonated { " abomonated" } else { "" };
        let lang = self.lang();
        format!("{} (rc={}){}", lang.key(), self.rc, abomonated)
    }

    pub fn create(&self, disk_cache_path: &Utf8Path) -> io::Result<File> {
        let metadata = Metadata::from_instance(self);
        let mut bytes = metadata.to_bytes()?;
        let digest: F = DigestBuilder::<F, Metadata>::map_to_field(&mut bytes);
        let digest_str = format!("{:?}", digest);

        let instance_file = File::create(disk_cache_path.join(&digest_str))?;

        let metadata_file = disk_cache_path.join(digest_str).with_extension("json");
        let metadata_file = File::create(metadata_file)?;

        let writer = BufWriter::new(&metadata_file);
        serde_json::to_writer_pretty(writer, &metadata)?;

        Ok(instance_file)
    }

    pub fn open(&self, disk_cache_path: &Utf8Path) -> io::Result<File> {
        let metadata = Metadata::from_instance(self);
        let mut bytes = metadata.to_bytes()?;
        let digest: F = DigestBuilder::<F, Metadata>::map_to_field(&mut bytes);
        let digest_str = format!("{:?}", digest);

        let instance_file = File::open(disk_cache_path.join(&digest_str))?;

        let metadata_file = disk_cache_path.join(digest_str).with_extension("json");
        let metadata_file = File::open(metadata_file)?;

        let reader = BufReader::new(metadata_file);
        let expected_metadata: Metadata = serde_json::from_reader(reader)?;

        if metadata == expected_metadata {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                "public params: mistmatched instances",
            ));
        }

        Ok(instance_file)
    }
}
