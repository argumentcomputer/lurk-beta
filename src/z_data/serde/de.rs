use serde::{Deserialize, de, de::{IntoDeserializer, Visitor}};

use crate::z_data::serde::SerdeError;
use crate::z_data::ZData;

pub fn from_z_data<'a, T>(z: &'a ZData) -> Result<T, SerdeError>
  where T: Deserialize<'a>,
{
  let mut deserializer = Deserializer::from_z_data(z);
  T::deserialize(&mut deserializer)
}

pub struct Deserializer<'de> {
  input: &'de ZData,
  //_pd: PhantomData<&'de ZData>,
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
	}
      _ => Err(SerdeError::Type("expected bool".into())),
      }
  }

  #[inline]
 fn deserialize_i8<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type(
            "Unsigned integers not supported".into(),
        ))
    }

  #[inline]
 fn deserialize_i16<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type(
            "Unsigned integers not supported".into(),
        ))
    }
  #[inline]
 fn deserialize_i32<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type(
            "Unsigned integers not supported".into(),
        ))
    }
  #[inline]
 fn deserialize_i64<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(SerdeError::Type(
            "Unsigned integers not supported".into(),
        ))
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
   where V: Visitor<'de> {
   match char::from_u32(u32::deserialize(self).map_err(|_| SerdeError::Type("expected char".into()))?) {
     Some(a) => visitor.visit_char(a),
     None => Err(SerdeError::Type("expected char".into())),
   }
 }

  #[inline]
  fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    //match self.deserialize_bytes(visitor) {
    //  Ok(a) => visitor.visit_borrowed_str(&str::from_bytes(a)),
    //  Err(_) => Err(SerdeError::Type("expected str".into())),
    //}
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
     }
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
   todo!()
   //match self.input {
   //  ZData::Atom(x) => match x.as_slice() {
   //    [] => visitor.visit_none(),
   //    _ => Err(SerdeError::Type("expected Option".into())),
   //  }
   //  ZData::Cell(xs) => match xs.as_slice() {
   //    [a] => visitor.visit_some(a::deserialize()),
   //    _ => Err(SerdeError::Type("expected Option".into())),
   //  }
   //}
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
     }
     _ => Err(SerdeError::Type("expected Unit ()".into())),
   }
 }

  #[inline]
 fn deserialize_unit_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_unit(visitor)
    }

  #[inline]
 fn deserialize_newtype_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value, Self::Error>
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
    ZData::Cell(xs) => visit_seq(*xs, visitor),
      //xs.iter().map(|x| x.deserialize(self)).collect(),
    _ => Err(SerdeError::Type("expected sequence".into()))
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
 fn deserialize_tuple_struct<V>(self, name: &'static str, len: usize, visitor: V) -> Result<V::Value, Self::Error>
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
   todo!()
   // Look at BTreeMap Encodable::de, Ipld-rs visit_map fn, and the serde docs as
     // many of these visit fn's are unimplemented by default
    }

  #[inline]
 fn deserialize_struct<V>(self, name: &'static str, fields: &'static [&'static str], visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
   todo!()
    }

  #[inline]
 fn deserialize_enum<V>(self, _name: &'static str, variants: &'static [&'static str], visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
   todo!()
     // See Ipld-rs fn
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

fn visit_seq<'de, V>(
  list: Vec<ZData>,
  visitor: V,
) -> Result<V::Value, SerdeError>
where
  V: de::Visitor<'de>,
{
  let mut deserializer = SeqDeserializer::new(list);
  visitor.visit_seq(&mut deserializer)
}

// Probably should include length
struct SeqDeserializer {
  iter: <Vec<ZData> as IntoIterator>::IntoIter,
}

impl SeqDeserializer {
  fn new(vec: Vec<ZData>) -> Self { Self { iter: vec.into_iter() } }
}

impl<'de> de::SeqAccess<'de> for SeqDeserializer {
  type Error = SerdeError;

  fn next_element_seed<T>(
    &mut self,
    seed: T,
  ) -> Result<Option<T::Value>, Self::Error>
  where
    T: de::DeserializeSeed<'de>,
  {
    match self.iter.next() {
      Some(value) => seed.deserialize(value).map(Some),
      None => Ok(None),
    }
  }

  fn size_hint(&self) -> Option<usize> {
    match self.iter.size_hint() {
      (lower, Some(upper)) if lower == upper => Some(upper),
      _ => None,
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::z_data::ZData::{Atom, Cell};
  use crate::z_expr::ZExpr;
  use pasta_curves::pallas::Scalar;

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
