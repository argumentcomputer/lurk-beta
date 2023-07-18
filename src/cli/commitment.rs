use std::{fs::File, io::{BufWriter, BufReader}};

use anyhow::{Result, bail};

use lurk::{field::LurkField, ptr::Ptr, store::Store, z_ptr::ZExprPtr, z_store::ZStore};
use serde::{Deserialize, Serialize};

use super::{field_data::FieldData, paths::commitment_path};

#[derive(Serialize, Deserialize)]
pub struct Commitment<F: LurkField> {
    pub hash: F,
    secret: F,
    hidden: ZExprPtr<F>,
    zstore: ZStore<F>,
}

impl<'a, F: LurkField + Serialize + Deserialize<'a>> Commitment<F> {
    pub fn new(secret: F, payload: Ptr<F>, store: &mut Store<F>) -> Result<Self> {
        let hidden = store.hide(secret, payload);
        let mut zstore = Some(ZStore::<F>::default());
        let hidden = store.get_z_expr(&hidden, &mut zstore)?.0;
        let hash = *hidden.value();
        let zstore = zstore.unwrap();
        Ok(Self {
            hash,
            secret,
            hidden,
            zstore,
        })
    }

    pub fn persist(&self, hash: &str) -> Result<()> {
        let fd = &FieldData::wrap::<F, Commitment<F>>(self)?;
        bincode::serialize_into(BufWriter::new(&File::create(commitment_path(hash))?), fd)?;
        Ok(())
    }

    pub fn load(hash: &str) -> Result<Self> {
        let file = File::open(commitment_path(hash))?;
        let fd: FieldData = bincode::deserialize_from(BufReader::new(file))?;
        if fd.field != F::FIELD {
            bail!("Invalid field: {}. Expected {}", &fd.field, &F::FIELD)
        } else {
            let commitment: Commitment<F> = fd.extract()?;
            if format!("0x{}", commitment.hash.hex_digits()) == hash {
                Ok(commitment)
            } else {
                bail!("Hash mismatch. Corrupted commitment file.")
            }
        }
    }
}
