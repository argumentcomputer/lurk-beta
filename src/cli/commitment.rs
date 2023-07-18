use std::{fs::File, io::BufWriter};

use anyhow::Result;

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
}
