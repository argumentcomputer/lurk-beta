use lurk::{field::LurkField, z_store::ZStore};
use serde::{Deserialize, Serialize};

use super::field_data::HasFieldModulus;

/// Holds data for commitments.
///
/// **Warning**: holds private data. The `ZStore` contains the secret used to
/// hide the original payload.
#[derive(Serialize, Deserialize)]
pub struct Commitment<F: LurkField> {
    pub(crate) hash: F,
    pub(crate) zstore: ZStore<F>,
}

impl<F: LurkField> HasFieldModulus for Commitment<F> {
    fn field_modulus() -> String {
        F::MODULUS.to_owned()
    }
}

use anyhow::Result;
use lurk::{ptr::Ptr, store::Store};

use crate::cli::{field_data::dump, paths::commitment_path};

impl<F: LurkField> Commitment<F> {
    pub fn new(secret: Option<F>, payload: Ptr<F>, store: &mut Store<F>) -> Result<Self> {
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
    pub fn persist(self) -> Result<()> {
        let hash_str = &self.hash.hex_digits();
        dump(self, commitment_path(hash_str))
    }
}
