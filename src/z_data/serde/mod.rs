use thiserror::Error;

mod de;
mod ser;

pub use de::from_z_data;
pub use ser::to_z_data;

#[derive(Error, Debug)]
pub enum SerdeError {
    #[error("Function error")]
    Function(String),
    #[error("Type error")]
    Type(String),
}

impl serde::ser::Error for SerdeError {
    fn custom<T: core::fmt::Display>(msg: T) -> Self {
        Self::Function(msg.to_string())
    }
}

impl serde::de::Error for SerdeError {
    fn custom<T: core::fmt::Display>(msg: T) -> Self {
        Self::Function(msg.to_string())
    }
}

#[cfg(test)]
mod tests {
    use crate::field::FWrap;
    use crate::z_data::{from_z_data, to_z_data};
    use pasta_curves::pallas::Scalar;
    use proptest::prelude::*;
    use serde::{Deserialize, Serialize};
    use std::collections::BTreeMap;

    fn test_roundtrip<T>(zd: &T)
    where
        T: Serialize + for<'de> Deserialize<'de> + PartialEq + std::fmt::Debug,
    {
        assert_eq!(*zd, from_z_data(&to_z_data(zd).unwrap()).unwrap());
    }

    #[test]
    fn serde_simple_roundtrip() {
        test_roundtrip(&(1u8, 2u8));
        test_roundtrip(&(1u32, 2u64));
        test_roundtrip(&String::from("Hello world"));
        test_roundtrip(&['a', 'b', 'c']);
        test_roundtrip(&[0u8, 1u8, 2u8]);
        test_roundtrip(&[String::from("Hello"), String::from("World")]);
        test_roundtrip(&BTreeMap::from([
            (String::from("Hello"), 0u8),
            (String::from("World"), 1u8),
        ]));
        let f = FWrap(Scalar::one());
        let ser = to_z_data(f).unwrap();
        assert_eq!(f, from_z_data(&ser).unwrap());
    }

    proptest! {
        #[test]
        fn ser_err_isize(x in any::<isize>()) {
            assert!(to_z_data(x).is_err());
        }

        #[test]
        fn ser_err_f32(x in any::<f32>()) {
            assert!(to_z_data(x).is_err());
        }
    }
}
