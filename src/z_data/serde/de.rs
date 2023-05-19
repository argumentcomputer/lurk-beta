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
        Err(SerdeError::Function("Function not supported".into()))
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
                _ => Err(SerdeError::Type("expected bool".into())),
            },
            _ => Err(SerdeError::Type("expected bool".into())),
        }
    }

    #[inline]
    fn deserialize_i8<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type("Unsigned integers not supported".into()))
    }

    #[inline]
    fn deserialize_i16<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type("Unsigned integers not supported".into()))
    }
    #[inline]
    fn deserialize_i32<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type("Unsigned integers not supported".into()))
    }
    #[inline]
    fn deserialize_i64<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type("Unsigned integers not supported".into()))
    }

    #[inline]
    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.input {
            ZData::Atom(x) if x.len() == 1 => visitor.visit_u8(x[0]),
            _ => Err(SerdeError::Type("expected bool".into())),
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
            _ => Err(SerdeError::Type("expected u16".into())),
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
            _ => Err(SerdeError::Type("expected u32".into())),
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
            _ => Err(SerdeError::Type("expected u64".into())),
        }
    }

    #[inline]
    fn deserialize_f32<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type("Floats not supported".into()))
    }

    #[inline]
    fn deserialize_f64<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type("Floats not supported".into()))
    }

    #[inline]
    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match char::from_u32(
            u32::deserialize(self).map_err(|_| SerdeError::Type("expected char".into()))?,
        ) {
            Some(a) => visitor.visit_char(a),
            None => Err(SerdeError::Type("expected char".into())),
        }
    }

    #[inline]
    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_string(visitor)
    }

    #[inline]
    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match Vec::<u8>::deserialize(self) {
            Ok(a) => match String::from_utf8(a) {
                Ok(v) => visitor.visit_str(&v),
                Err(_) => Err(SerdeError::Type("expected string".into())),
            },
            Err(_) => Err(SerdeError::Type("expected string".into())),
        }
    }

    #[inline]
    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.input {
            ZData::Atom(x) => visitor.visit_bytes(x),
            _ => Err(SerdeError::Type("expected bytes".into())),
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
                _ => Err(SerdeError::Type("expected Option".into())),
            },
            ZData::Cell(xs) => match xs.as_slice() {
                [a] => visitor.visit_some(&mut Deserializer::from_z_data(a)),
                _ => Err(SerdeError::Type("expected Option".into())),
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
                _ => Err(SerdeError::Type("expected Unit ()".into())),
            },
            _ => Err(SerdeError::Type("expected Unit ()".into())),
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
            ZData::Cell(xs) => visitor.visit_seq(SeqAccess::new(xs)),
            _ => Err(SerdeError::Type("expected sequence".into())),
        }
    }

    #[inline]
    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }

    #[inline]
    fn deserialize_tuple_struct<V>(
        self,
        name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }

    // TODO: Should I just deserialize_seq into Vec<(A, B)> and collect into a map?
    // Example Map: ZData::Cell(vec![ZData::Cell(vec![ZData::Atom[0], ZData::Atom[1]])])
    #[inline]
    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.input {
            ZData::Cell(xs) => visitor.visit_map(MapAccess::new(xs)),
            _ => Err(SerdeError::Type("expected map".into())),
        }
    }

    #[inline]
    fn deserialize_struct<V>(
        self,
        name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_map(visitor)
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
            ZData::Cell(xs) => visitor.visit_enum(VariantAccess::new(xs)),
            _ => Err(SerdeError::Type("expected enum".into())),
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
        Err(SerdeError::Function("Function not supported".into()))
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
    fn new(vec: &'a [ZData]) -> Self {
        Self { vec, index: 0 }
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

struct VariantAccess<'a> {
    vec: &'a [ZData],
    index: usize,
}

impl<'a> VariantAccess<'a> {
    fn new(vec: &'a [ZData]) -> Self {
        Self { vec, index: 0 }
    }
}

impl<'de> de::EnumAccess<'de> for VariantAccess<'de> {
    type Error = SerdeError;
    type Variant = Self;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self), Self::Error>
    where
        V: de::DeserializeSeed<'de>,
    {
        let val = seed.deserialize(&mut Deserializer::from_z_data(&self.vec[self.index]))?;
        Ok((val, self))
    }
}

impl<'de> de::VariantAccess<'de> for VariantAccess<'de> {
    type Error = SerdeError;

    fn unit_variant(self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value, Self::Error>
    where
        T: de::DeserializeSeed<'de>,
    {
        seed.deserialize(&mut Deserializer::from_z_data(&self.vec[self.index]))
    }

    fn tuple_variant<V>(self, _len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        de::Deserializer::deserialize_seq(
            &mut Deserializer::from_z_data(&self.vec[self.index]),
            visitor,
        )
    }

    fn struct_variant<V>(
        self,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: de::Visitor<'de>,
    {
        de::Deserializer::deserialize_struct(
            &mut Deserializer::from_z_data(&self.vec[self.index]),
            "",
            fields,
            visitor,
        )
    }
}
// See https://github.com/pyfisch/cbor/blob/master/src/de.rs#L1133 for alternative

#[cfg(test)]
mod tests {
    use super::*;
    use crate::z_data::ZData::{Atom, Cell};
    use crate::z_expr::ZExpr;
    use pasta_curves::pallas::Scalar;

    // TODO: Write up some test vectors for a Vec, tuple, BTreeMap, enum, and struct
    #[test]
    fn de_simple() {
        let atom = Cell(vec![Atom(vec![1])]);
        let num: u8 = from_z_data(&atom).unwrap();
        assert_eq!(num, 1u8);
    }

    //#[test]
    //fn de_z_expr() {
    //let test_zexpr = |zd: ZData| {
    //  let ze: ZExpr<Scalar> = from_z_data(&zd).unwrap();
    //  println!("ZExpr: {:?}", ze);
    //  //assert_eq!(ZExpr::de(zd), ze);
    //};
    //test_zexpr(ZData::Cell(vec![Atom(vec![0])]));
    //test_zexpr(ZData::Cell(vec![Atom(vec![1]), Cell(vec![Atom(vec![2]), Atom(vec![1])]), Cell(vec![Atom(vec![2]), Atom(vec![1])])]));
    //test_zexpr(ZData::Cell(vec![Atom(vec![2]), Atom(vec![1]), Cell(vec![Atom(vec![2]), Atom(vec![1])])]));
    //test_zexpr(ZData::Cell(vec![Atom(vec![3])]));
    //test_zexpr(ZData::Cell(vec![Atom(vec![4]), Cell(vec![Atom(vec![2]), Atom(vec![1])]), Cell(vec![Atom(vec![2]), Atom(vec![1])])]));
    //test_zexpr(ZData::Cell(vec![Atom(vec![5]), Cell(vec![Atom(vec![2]), Atom(vec![1])])]));
    //test_zexpr(ZData::Cell(vec![Atom(vec![6]), Cell(vec![Atom(vec![2]), Atom(vec![1])]), Cell(vec![Atom(vec![2]), Atom(vec![1])]), Cell(vec![Atom(vec![2]), Atom(vec![1])])]));
    //test_zexpr(ZData::Cell(vec![Atom(vec![7]), Atom(vec![1])]));
    //test_zexpr(ZData::Cell(vec![Atom(vec![8])]));
    //test_zexpr(ZData::Cell(vec![Atom(vec![9]), Cell(vec![Atom(vec![2]), Atom(vec![1])]), Cell(vec![Atom(vec![2]), Atom(vec![1])])]));
    //test_zexpr(ZData::Cell(vec![Atom(vec![10]), Cell(vec![Atom(vec![2]), Atom(vec![1])]), Cell(vec![Atom(vec![6, 16]), Atom(vec![1])])]));
    //test_zexpr(ZData::Cell(vec![Atom(vec![11]), Atom(vec![97, 0, 0, 0])]));
    //test_zexpr(ZData::Cell(vec![Atom(vec![12]), Atom(vec![0, 0, 0, 0, 0, 0, 0, 0])]));
    //}
}
