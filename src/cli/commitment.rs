use lurk::{field::LurkField, z_ptr::ZExprPtr, z_store::ZStore};
use serde::{Deserialize, Serialize};

use super::field_data::HasFieldModulus;

/// Holds data for commitments.
///
/// **Warning**: holds private data. The `ZStore` contains the secret used to
/// hide the original payload.
#[derive(Serialize, Deserialize)]
pub struct Commitment<F: LurkField> {
    pub(crate) hidden: ZExprPtr<F>,
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

    use crate::cli::{field_data::FieldData, paths::non_wasm::commitment_path};

    use super::Commitment;

    impl<F: LurkField> Commitment<F> {
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
        #[inline]
        pub fn persist(self, hash: &str) -> Result<()> {
            FieldData::dump(self, commitment_path(hash))
        }
    }
}
