use anyhow::Result;

use serde::{de::DeserializeOwned, Deserialize, Serialize};

// This module implements a 2-step serde protocol for data that is parametrized
// on an arithmetic field in order to be properly deserialized.
//
// First, we serialize it to a vector of bytes. Then, we wrap the vector with a
// struct that contains the field modulus, which, in turn, is serialized to a
// vector of bytes.
//
// When deserializing, we unwrap the first layer and double check the field
// modulus for consistency. If everything goes well, we further unwrap the second
// layer of bytes.

pub(crate) trait HasFieldModulus {
    fn field_modulus() -> String;
}

#[allow(dead_code)]
pub(crate) fn to_bytes<T: Serialize + HasFieldModulus>(t: T) -> Result<Vec<u8>> {
    Ok(bincode::serialize(&FieldData(t))?)
}

#[allow(dead_code)]
pub(crate) fn from_bytes<T: DeserializeOwned + HasFieldModulus>(bytes: &[u8]) -> Result<T> {
    let FieldData(data) = bincode::deserialize(bytes)?;
    Ok(data)
}

#[derive(Debug, PartialEq, Eq)]
struct FieldData<T>(T);

#[derive(Deserialize, Serialize)]
struct FieldDataWrap {
    field_modulus: String,
    #[serde(with = "serde_bytes")]
    bytes: Vec<u8>,
}

impl<'de, T: DeserializeOwned + HasFieldModulus> Deserialize<'de> for FieldData<T> {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let fdw = FieldDataWrap::deserialize(deserializer)?;
        if fdw.field_modulus != T::field_modulus() {
            return Err(serde::de::Error::custom("Field mismatch"));
        };
        let t: T = bincode::deserialize(&fdw.bytes).map_err(serde::de::Error::custom)?;
        Ok(FieldData(t))
    }
}

impl<T: Serialize + HasFieldModulus> Serialize for FieldData<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let fdw = FieldDataWrap {
            field_modulus: T::field_modulus(),
            bytes: bincode::serialize(&self.0).map_err(serde::ser::Error::custom)?,
        };
        fdw.serialize(serializer)
    }
}

#[cfg(not(target_arch = "wasm32"))]
pub mod non_wasm {
    use super::{from_bytes, to_bytes, HasFieldModulus};
    use anyhow::Result;
    use serde::{de::DeserializeOwned, Serialize};
    use std::path::PathBuf;

    pub(crate) fn dump<T: Serialize + HasFieldModulus>(t: T, path: PathBuf) -> Result<()> {
        Ok(std::fs::write(path, to_bytes(t)?)?)
    }

    pub(crate) fn load<T: DeserializeOwned + HasFieldModulus>(path: PathBuf) -> Result<T> {
        from_bytes(&std::fs::read(path)?)
    }
}
