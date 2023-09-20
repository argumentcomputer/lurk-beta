use anyhow::Result;
use serde::{Deserialize, Serialize};

use crate::field::LurkField;
use crate::z_store::ZStore;
use crate::{ptr::Ptr, store::Store};

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
    pub(crate) fn new(secret: Option<F>, payload: Ptr<F>, store: &Store<F>) -> Result<Self> {
        let comm_ptr = match secret {
            Some(secret) => store.hide(secret, payload),
            None => store.commit(payload),
        };
        let mut zstore = Some(ZStore::<F>::default());
        let hash = *store.get_z_expr(&comm_ptr, &mut zstore)?.0.value();
        let zstore = zstore.unwrap();
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
