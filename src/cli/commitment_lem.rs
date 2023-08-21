use anyhow::Result;
use serde::{Deserialize, Serialize};

use crate::{
    field::LurkField,
    lem::{pointers::Ptr, store::Store, zstore::ZStore},
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
    pub(crate) zstore: ZStore<F>,
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
        let mut zstore = ZStore::<F>::default();
        let hash = zstore.populate(&comm_ptr, store)?.hash;
        zstore.add_comm(hash, secret, z_payload);
        Ok(Self { hash, zstore })
    }
}

impl<F: LurkField + Serialize> Commitment<F> {
    #[inline]
    pub(crate) fn persist(self) -> Result<()> {
        let hash_str = &self.hash.hex_digits();
        dump(self, commitment_path(hash_str))
    }
}
