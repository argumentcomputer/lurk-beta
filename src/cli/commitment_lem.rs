use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};

use crate::{
    field::LurkField,
    lem::{
        pointers::{Ptr, ZPtr},
        store::Store,
        zstore::{populate_z_store, ZStore},
    },
};

use super::{
    field_data::{dump, HasFieldModulus},
    paths::commitment_path,
};

/// Holds data for commitments.
///
/// **Warning**: holds private data. The `ZStore` contains the secret used to
/// hide the original payload.
#[derive(Serialize, Deserialize)]
pub(crate) struct Commitment<F: LurkField> {
    pub(crate) hash: F,
    pub(crate) z_store: ZStore<F>,
}

impl<F: LurkField> HasFieldModulus for Commitment<F> {
    fn field_modulus() -> String {
        F::MODULUS.to_owned()
    }
}

impl<F: LurkField> Commitment<F> {
    pub(crate) fn new(secret: Option<F>, payload: Ptr<F>, store: &mut Store<F>) -> Result<Self> {
        let secret = secret.unwrap_or(F::NON_HIDING_COMMITMENT_SECRET);
        let (comm_ptr, z_payload) = store.hide_and_return_z_payload(secret, payload)?;
        let mut z_store = ZStore::<F>::default();
        let hash = populate_z_store(&mut z_store, &comm_ptr, store)?.hash;
        z_store.add_comm(hash, secret, z_payload);
        Ok(Self { hash, z_store })
    }

    pub(crate) fn open(&self) -> Result<&(F, ZPtr<F>)> {
        if let Some(pair) = self.z_store.open(self.hash) {
            Ok(pair)
        } else {
            bail!("Couldn't open commitment")
        }
    }
}

impl<F: LurkField + Serialize> Commitment<F> {
    #[inline]
    pub(crate) fn persist(self) -> Result<()> {
        let hash_str = &self.hash.hex_digits();
        dump(self, commitment_path(hash_str))
    }
}
