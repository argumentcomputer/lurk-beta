use anyhow::Result;
use camino::Utf8PathBuf;
use serde::{de::DeserializeOwned, Deserialize, Serialize};

// This module implements a 2-step serde protocol for data that is parametrized
// on an arithmetic field in order to be properly deserialized.
//
// First, we serialize it to a vector of bytes. Then, we wrap the vector with a
// struct that contains the field modulus, which, in turn, is serialized to the
// final vector of bytes.
//
// When deserializing, we unwrap the vector of bytes and double check the field
// modulus for consistency. If everything goes well, we further unwrap the second
// vector of bytes.

pub(crate) trait HasFieldModulus {
    fn field_modulus() -> String;
}

#[allow(dead_code)]
pub(crate) fn ser<T: Serialize + HasFieldModulus>(t: T) -> Result<Vec<u8>> {
    Ok(bincode::serialize(&FieldData(t))?)
}

#[allow(dead_code)]
pub(crate) fn de<T: DeserializeOwned + HasFieldModulus>(bytes: &[u8]) -> Result<T> {
    let FieldData(data) = bincode::deserialize(bytes)?;
    Ok(data)
}

pub(crate) fn dump<T: Serialize + HasFieldModulus>(t: T, path: Utf8PathBuf) -> Result<()> {
    Ok(std::fs::write(path, ser(t)?)?)
}

pub(crate) fn load<T: DeserializeOwned + HasFieldModulus>(path: Utf8PathBuf) -> Result<T> {
    de(&std::fs::read(path)?)
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

#[cfg(test)]
mod tests {
    use crate::field::LurkField;
    use ff::Field;
    use pasta_curves::Fq;
    use serde::{Deserialize, Serialize};

    use super::{de, ser, HasFieldModulus};

    #[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
    struct Struct<F: LurkField> {
        str: String,
        int: i32,
        ff: F,
    }

    #[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
    enum Enum1<F: LurkField> {
        CaseStr(String),
        CaseInt(i32),
        CaseFF(F),
    }

    impl<F: LurkField> HasFieldModulus for Struct<F> {
        fn field_modulus() -> String {
            F::MODULUS.to_string()
        }
    }

    impl<F: LurkField> HasFieldModulus for Enum1<F> {
        fn field_modulus() -> String {
            F::MODULUS.to_string()
        }
    }

    #[test]
    fn struct_roundtrips() {
        let s = Struct {
            str: "hi".into(),
            int: 42,
            ff: Fq::double(&Fq::ONE),
        };
        assert_eq!(s, de(&ser(s.clone()).unwrap()).unwrap())
    }

    #[test]
    fn enum1_roundtrips() {
        let e11 = Enum1::CaseStr("bye".into());
        let e12 = Enum1::CaseInt(11);
        let e13 = Enum1::CaseFF(Fq::double(&Fq::double(&Fq::ONE)));
        for e in [e11, e12, e13] {
            assert_eq!(e, de(&ser(e.clone()).unwrap()).unwrap());
        }
    }

    /// An enum can be deserialized to another, if the enum constructor has the
    /// same index and uses the same inner data
    #[test]
    fn stable_enum() {
        #[derive(PartialEq, Debug, Clone, Serialize, Deserialize)]
        enum Enum2<F: LurkField> {
            CaseStr2(String),
            CaseInt2(i32),
            CaseFF2(F),
            Foo,
        }

        impl<F: LurkField> HasFieldModulus for Enum2<F> {
            fn field_modulus() -> String {
                F::MODULUS.to_string()
            }
        }
        let e11 = Enum1::CaseStr("bye".into());
        let e12 = Enum1::CaseInt(11);
        let e13 = Enum1::CaseFF(Fq::double(&Fq::double(&Fq::ONE)));

        let e21 = Enum2::CaseStr2("bye".into());
        let e22 = Enum2::CaseInt2(11);
        let e23 = Enum2::CaseFF2(Fq::double(&Fq::double(&Fq::ONE)));

        for (e1, e2) in [(e11, e21), (e12, e22), (e13, e23)] {
            assert_eq!(e2.clone(), de(&ser(e1.clone()).unwrap()).unwrap());
            assert_eq!(e1, de(&ser(e2).unwrap()).unwrap());
        }
    }
}
