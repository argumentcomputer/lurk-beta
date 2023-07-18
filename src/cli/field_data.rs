use anyhow::Result;
use serde::{Deserialize, Serialize};

use lurk::field::{LanguageField, LurkField};

/// A wrapper for data whose deserialization depends on a certain LurkField
#[derive(Serialize, Deserialize)]
pub struct FieldData {
    field: LanguageField,
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
    pub fn extract<'a, T: Deserialize<'a>>(&'a self) -> Result<T> {
        Ok(bincode::deserialize(&self.data)?)
    }
}
