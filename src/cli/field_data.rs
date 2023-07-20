use anyhow::Result;

use serde::{de::DeserializeOwned, Deserialize, Serialize};

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct FieldData<T>(T);

pub(crate) trait HasFieldModulus {
    fn field_modulus() -> String;
}

#[derive(Deserialize, Serialize)]
struct Labeled {
    label: String,
    #[serde(with = "serde_bytes")]
    bytes: Vec<u8>,
}

impl<'de, T: DeserializeOwned + HasFieldModulus> Deserialize<'de> for FieldData<T> {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let level1_struct = Labeled::deserialize(deserializer)?;
        if level1_struct.label != T::field_modulus() {
            return Err(serde::de::Error::custom("Field mismatch"));
        };
        let t: T =
            bincode::deserialize(&level1_struct.bytes[..]).map_err(serde::de::Error::custom)?;
        Ok(FieldData(t))
    }
}

impl<T: Serialize + HasFieldModulus> Serialize for FieldData<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let bytes = bincode::serialize(&self.0).map_err(serde::ser::Error::custom)?;
        let labeled = Labeled {
            label: T::field_modulus(),
            bytes,
        };
        labeled.serialize(serializer)
    }
}

#[cfg(not(target_arch = "wasm32"))]
pub mod non_wasm {
    use super::{FieldData, HasFieldModulus};
    use anyhow::Result;
    use serde::{de::DeserializeOwned, Serialize};
    use std::path::PathBuf;

    impl<T: Serialize + HasFieldModulus> FieldData<T> {
        pub fn dump(t: T, path: PathBuf) -> Result<()> {
            let bytes = bincode::serialize(&FieldData(t))?;
            Ok(std::fs::write(path, bytes)?)
        }
    }

    impl<T: DeserializeOwned + HasFieldModulus> FieldData<T> {
        pub fn load(path: PathBuf) -> Result<T> {
            let bytes = std::fs::read(path)?;
            let fd: FieldData<T> = bincode::deserialize(&bytes)?;
            Ok(fd.0)
        }
    }
}
