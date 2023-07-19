use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};

use lurk::field::{LanguageField, LurkField};

/// A wrapper for data whose deserialization depends on a certain LurkField
#[derive(Serialize, Deserialize)]
pub struct FieldData {
    pub(crate) field: LanguageField,
    data: Vec<u8>,
}

#[allow(dead_code)]
impl FieldData {
    #[inline]
    pub fn wrap<F: LurkField, T: Serialize>(t: &T) -> Result<Self> {
        Ok(Self {
            field: F::FIELD,
            data: bincode::serialize(t)?,
        })
    }

    #[inline]
    pub fn extract<'a, F: LurkField, T: Deserialize<'a>>(&'a self) -> Result<T> {
        if self.field != F::FIELD {
            bail!("Invalid field: {}. Expected {}", &self.field, &F::FIELD)
        }
        Ok(bincode::deserialize(&self.data)?)
    }
}
