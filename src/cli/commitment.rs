use std::{fs::File, io::BufWriter};

use anyhow::Result;

use lurk::{field::LurkField, ptr::Ptr, store::Store, z_ptr::ZExprPtr, z_store::ZStore};
use serde::{Deserialize, Serialize};

use super::{field_data::FieldData, paths::commitment_path};

#[derive(Serialize, Deserialize)]
pub struct Commitment<F: LurkField> {
    pub hash: F,
    secret: F,
    payload: ZExprPtr<F>,
    zstore: ZStore<F>,
}

impl<F: LurkField + Serialize> Commitment<F> {
    pub fn new(secret: F, payload: Ptr<F>, store: &mut Store<F>) -> Result<Self> {
        let payload = store.hide(secret, payload);
        let mut zstore = Some(ZStore::<F>::default());
        let payload = store.get_z_expr(&payload, &mut zstore)?.0;
        let hash = payload.value().clone();
        let zstore = zstore.unwrap();
        Ok(Self {
            hash,
            secret,
            payload,
            zstore,
        })
    }

    pub fn persist(&self, hash: &str) -> Result<()> {
        let fd = &FieldData::wrap::<F, Commitment<F>>(self)?;
        bincode::serialize_into(BufWriter::new(&File::create(commitment_path(hash))?), fd)?;
        Ok(())
    }

    pub fn load(hash: &str) -> Result<Self> {
        todo!()
    }
}
