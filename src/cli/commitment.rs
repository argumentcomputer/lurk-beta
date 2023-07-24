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

#[cfg(not(target_arch = "wasm32"))]
mod non_wasm {
    use anyhow::Result;
    use lurk::{field::LurkField, ptr::Ptr, store::Store, z_store::ZStore};
    use serde::Serialize;

    use crate::cli::{field_data::non_wasm::dump, paths::non_wasm::commitment_path};

    use super::Commitment;

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
}
