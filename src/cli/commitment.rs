use anyhow::Result;

use lurk::{field::LurkField, ptr::Ptr, store::Store, z_ptr::ZExprPtr, z_store::ZStore};
use serde::{Deserialize, Serialize};

/// Holds data for commitments.
///
/// WARNING: CONTAINS PRIVATE DATA
#[derive(Serialize, Deserialize)]
pub struct Commitment<F: LurkField> {
    pub(crate) hidden: ZExprPtr<F>,
    pub(crate) zstore: ZStore<F>,
}

impl<F: LurkField> Commitment<F> {
    #[allow(dead_code)]
    pub fn new(secret: F, payload: Ptr<F>, store: &mut Store<F>) -> Result<Self> {
        let hidden = store.hide(secret, payload);
        let mut zstore = Some(ZStore::<F>::default());
        let hidden = store.get_z_expr(&hidden, &mut zstore)?.0;
        Ok(Self {
            hidden,
            zstore: zstore.unwrap(),
        })
    }
}

impl<F: LurkField + Serialize> Commitment<F> {
    #[cfg(not(target_arch = "wasm32"))]
    pub fn persist(&self, hash: &str) -> Result<()> {
        use super::{field_data::FieldData, paths::commitment_path};
        use std::{fs::File, io::BufWriter};

        let fd = &FieldData::wrap::<F, Commitment<F>>(self)?;
        bincode::serialize_into(BufWriter::new(&File::create(commitment_path(hash))?), fd)?;
        Ok(())
    }
}
