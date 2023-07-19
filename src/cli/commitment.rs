use lurk::{field::LurkField, z_ptr::ZExprPtr, z_store::ZStore};
use serde::{Deserialize, Serialize};

/// Holds data for commitments.
///
/// **Warning**: Holds private data. The `zstore` attribute contains the secret
/// used to hide the original payload.
#[derive(Serialize, Deserialize)]
pub struct Commitment<F: LurkField> {
    pub(crate) hidden: ZExprPtr<F>,
    pub(crate) zstore: ZStore<F>,
}

#[cfg(not(target_arch = "wasm32"))]
mod cli {
    use anyhow::Result;
    use lurk::{field::LurkField, ptr::Ptr, store::Store, z_store::ZStore};
    use serde::Serialize;
    use std::{fs::File, io::BufWriter};

    use crate::cli::{field_data::FieldData, paths::commitment_path};

    use super::Commitment;

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
        pub fn persist(&self, hash: &str) -> Result<()> {
            let fd = &FieldData::wrap::<F, Commitment<F>>(self)?;
            bincode::serialize_into(BufWriter::new(&File::create(commitment_path(hash))?), fd)?;
            Ok(())
        }
    }
}
