use serde::{
    de,
    de::{IntoDeserializer, Visitor},
    Deserialize,
};

use crate::z_data::serde::SerdeError;
use crate::z_data::ZData;

pub fn from_z_data<'a, T>(z: &'a ZData) -> Result<T, SerdeError>
where
    T: Deserialize<'a>,
{
    let mut deserializer = Deserializer::from_z_data(z);
    T::deserialize(&mut deserializer)
}

#[derive(Debug)]
pub struct Deserializer<'de> {
    input: &'de ZData,
}

impl<'de> Deserializer<'de> {
    pub fn from_z_data(input: &'de ZData) -> Self {
        Deserializer { input }
    }
}

impl<'de, 'a> de::Deserializer<'de> for &'a mut Deserializer<'de> {
    type Error = SerdeError;

    #[inline]
    fn deserialize_any<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Function(format!(
            "Function not supported: {}",
            self.input
        )))
    }

    #[inline]
    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.input {
            ZData::Atom(x) if x.len() == 1 => match x[0] {
                0u8 => visitor.visit_bool(false),
                1u8 => visitor.visit_bool(true),
                err => Err(SerdeError::Type(format!("expected bool, got: {}", err))),
            },
            err => Err(SerdeError::Type(format!("expected bool, got: {}", err))),
        }
    }

    #[inline]
    fn deserialize_i8<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type(format!(
            "Unsigned integers not supported: {}",
            self.input
        )))
    }

    #[inline]
    fn deserialize_i16<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type(format!(
            "Unsigned integers not supported: {}",
            self.input
        )))
    }

    #[inline]
    fn deserialize_i32<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type(format!(
            "Unsigned integers not supported: {}",
            self.input
        )))
    }
    #[inline]
    fn deserialize_i64<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type(format!(
            "Unsigned integers not supported: {}",
            self.input
        )))
    }

    #[inline]
    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.input {
            ZData::Atom(x) if x.len() == 1 => visitor.visit_u8(x[0]),
            err => Err(SerdeError::Type(format!("expected u8, got: {}", err))),
        }
    }

    #[inline]
    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.input {
            ZData::Atom(x) if x.len() == 2 => {
                let a: [u8; 2] = x.clone().try_into().unwrap();
                visitor.visit_u16(u16::from_le_bytes(a))
            }
            err => Err(SerdeError::Type(format!("expected u16, got: {}", err))),
        }
    }

    #[inline]
    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.input {
            ZData::Atom(x) if x.len() == 4 => {
                let a: [u8; 4] = x.clone().try_into().unwrap();
                visitor.visit_u32(u32::from_le_bytes(a))
            }
            err => Err(SerdeError::Type(format!("expected u32: got {}", err))),
        }
    }

    #[inline]
    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.input {
            ZData::Atom(x) if x.len() == 8 => {
                let a: [u8; 8] = x.clone().try_into().unwrap();
                visitor.visit_u64(u64::from_le_bytes(a))
            }
            err => Err(SerdeError::Type(format!("expected u64: got {}", err))),
        }
    }

    #[inline]
    fn deserialize_f32<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type(format!(
            "Floats not supported: {}",
            self.input
        )))
    }

    #[inline]
    fn deserialize_f64<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type(format!(
            "Floats not supported: {}",
            self.input
        )))
    }

    #[inline]
    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let num = u32::deserialize(self)
            .map_err(|e| SerdeError::Type(format!("expected char: {}", e)))?;
        match char::from_u32(num) {
            Some(a) => visitor.visit_char(a),
            None => Err(SerdeError::Type(format!(
                "failed to get char from: {}",
                num
            ))),
        }
    }

    #[inline]
    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let mut v: Vec<char> = vec![];
        match self.input {
            ZData::Cell(cell) => {
                for zd in cell {
                    match zd {
                        ZData::Atom(_atom) => {
                            v.push(char::deserialize(&mut Deserializer::from_z_data(zd))?)
                        }
                        err => {
                            return Err(SerdeError::Type(format!("expected string, got: {}", err)))
                        }
                    }
                }
            }
            err => return Err(SerdeError::Type(format!("expected string, got: {}", err))),
        }
        visitor.visit_str(&v.into_iter().collect::<String>())
    }

    #[inline]
    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_str(visitor)
    }

    #[inline]
    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.input {
            ZData::Atom(x) => visitor.visit_bytes(x),
            err => Err(SerdeError::Type(format!("expected bytes, got: {}", err))),
        }
    }

    #[inline]
    fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_bytes(visitor)
    }

    #[inline]
    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.input {
            ZData::Atom(x) => match x.as_slice() {
                [] => visitor.visit_none(),
                err => Err(SerdeError::Type(format!("expected Option, got: {:?}", err))),
            },
            ZData::Cell(xs) => match xs.as_slice() {
                [a] => visitor.visit_some(&mut Deserializer::from_z_data(a)),
                err => Err(SerdeError::Type(format!("expected Option, got: {:?}", err))),
            },
        }
    }

    #[inline]
    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.input {
            ZData::Atom(x) => match x.as_slice() {
                [] => visitor.visit_none(),
                err => Err(SerdeError::Type(format!(
                    "expected Unit (), got: {:?}",
                    err
                ))),
            },
            err => Err(SerdeError::Type(format!("expected Unit (), got: {}", err))),
        }
    }

    #[inline]
    fn deserialize_unit_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_unit(visitor)
    }

    #[inline]
    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    #[inline]
    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.input {
            ZData::Cell(xs) => visitor.visit_seq(SeqAccess::new(xs, 0)),
            err => Err(SerdeError::Type(format!("expected sequence, got: {}", err))),
        }
    }

    #[inline]
    fn deserialize_tuple<V>(self, _len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }

    #[inline]
    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }

    #[inline]
    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.input {
            ZData::Cell(xs) => visitor.visit_map(MapAccess::new(xs)),
            err => Err(SerdeError::Type(format!("expected map, got: {}", err))),
        }
    }

    #[inline]
    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_tuple(fields.len(), visitor)
    }

    #[inline]
    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.input {
            ZData::Cell(xs) if !xs.is_empty() => match &xs[0] {
                ZData::Atom(idx_vec) if idx_vec.len() == 1 => {
                    println!("Variants: {:?}", variants);
                    let variant = String::from(variants[idx_vec[0] as usize]);
                    visitor.visit_enum(Enum::new(self, variant, 1))
                }
                err => Err(SerdeError::Type(format!("expected enum, got: {}", err))),
            },
            err => Err(SerdeError::Type(format!("expected enum, got: {}", err))),
        }
    }

    #[inline]
    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_str(visitor)
    }

    #[inline]
    fn deserialize_ignored_any<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Function(format!(
            "Function not supported: {}",
            self.input
        )))
    }

    #[inline]
    fn is_human_readable(&self) -> bool {
        false
    }
}

struct SeqAccess<'a> {
    vec: &'a [ZData],
    index: usize,
}

impl<'a> SeqAccess<'a> {
    fn new(vec: &'a [ZData], index: usize) -> Self {
        Self { vec, index }
    }
}

impl<'de> de::SeqAccess<'de> for SeqAccess<'de> {
    type Error = SerdeError;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Self::Error>
    where
        T: de::DeserializeSeed<'de>,
    {
        if self.index >= self.vec.len() {
            Ok(None)
        } else {
            let value = seed.deserialize(&mut Deserializer::from_z_data(&self.vec[self.index]))?;
            self.index += 1;
            Ok(Some(value))
        }
    }
}

struct MapAccess<'a> {
    vec: &'a [ZData],
    index: usize,
}

impl<'a> MapAccess<'a> {
    fn new(vec: &'a [ZData]) -> Self {
        Self { vec, index: 0 }
    }
}

impl<'de> de::MapAccess<'de> for MapAccess<'de> {
    type Error = SerdeError;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>, Self::Error>
    where
        K: de::DeserializeSeed<'de>,
    {
        if self.index >= self.vec.len() {
            Ok(None)
        } else {
            let value = seed.deserialize(&mut Deserializer::from_z_data(&self.vec[self.index]))?;
            self.index += 1;
            Ok(Some(value))
        }
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, Self::Error>
    where
        V: de::DeserializeSeed<'de>,
    {
        if self.index >= self.vec.len() {
            Err(SerdeError::Type("Invalid index".into()))
        } else {
            let value = seed.deserialize(&mut Deserializer::from_z_data(&self.vec[self.index]))?;
            self.index += 1;
            Ok(value)
        }
    }
}

struct Enum<'a, 'de> {
    de: &'a mut Deserializer<'de>,
    variant: String,
    index: usize,
}

impl<'a, 'de> Enum<'a, 'de> {
    fn new(de: &'a mut Deserializer<'de>, variant: String, index: usize) -> Self {
        Enum { de, variant, index }
    }
}

// `EnumAccess` is provided to the `Visitor` to give it the ability to determine
// which variant of the enum is supposed to be deserialized.
impl<'de, 'a> de::EnumAccess<'de> for Enum<'a, 'de> {
    type Error = SerdeError;
    type Variant = Self;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant), Self::Error>
    where
        V: de::DeserializeSeed<'de>,
    {
        let variant = self.variant.clone().into_deserializer();
        let val = seed.deserialize(variant)?;
        Ok((val, self))
    }
}

// `VariantAccess` is provided to the `Visitor` to give it the ability to see
// the content of the single variant that it decided to deserialize.
impl<'de, 'a> de::VariantAccess<'de> for Enum<'a, 'de> {
    type Error = SerdeError;

    fn unit_variant(self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value, Self::Error>
    where
        T: de::DeserializeSeed<'de>,
    {
        let mut newtype = match self.de.input {
            ZData::Cell(xs) if xs.len() > 1 => Deserializer::from_z_data(&xs[1]),
            err => {
                return Err(SerdeError::Type(format!(
                    "expected newtype variant, got: {}",
                    err
                )))
            }
        };
        seed.deserialize(&mut newtype)
    }

    fn tuple_variant<V>(self, _len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.de.input {
            ZData::Cell(xs) => visitor.visit_seq(SeqAccess::new(xs, self.index)),
            err => Err(SerdeError::Type(format!("expected sequence, got: {}", err))),
        }
    }

    fn struct_variant<V>(
        self,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.tuple_variant(fields.len(), visitor)
    }
}
