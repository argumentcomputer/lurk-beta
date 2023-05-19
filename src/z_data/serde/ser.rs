use serde::{ser, Serialize};

use crate::z_data::serde::SerdeError;
use crate::z_data::ZData;

pub fn to_z_data<T>(value: T) -> Result<ZData, SerdeError>
where
    T: ser::Serialize,
{
    value.serialize(&Serializer)
}

pub struct Serializer;

pub struct SerializeCell {
    cell: Vec<ZData>,
}

pub struct SerializeMap {
    cell: Vec<ZData>,
    next_key: Option<ZData>,
}

pub struct SerializeTupleVariant {
    variant_index: u32,
    cell: Vec<ZData>,
}

pub struct StructSerializer<'a> {
    ser: &'a Serializer,
    cell: Vec<ZData>,
    variant_index: u32,
}

impl<'a> StructSerializer<'a> {
    fn serialize_field_inner<T>(&mut self, _key: &'static str, value: &T) -> Result<(), SerdeError>
    where
        T: ?Sized + ser::Serialize,
    {
        //self.ser.serialize_u32(self.variant_index)?;
        let val = value.serialize(self.ser)?;
        self.cell.push(val);
        //self.variant_index += 1;
        Ok(())
    }

    fn skip_field_inner(&mut self, _: &'static str) -> Result<(), SerdeError> {
        self.variant_index += 1;
        Ok(())
    }

    fn end_inner(self) -> Result<Vec<ZData>, SerdeError> {
        Ok(self.cell)
    }
}

impl<'a> ser::Serializer for &'a Serializer {
    type Ok = ZData;

    type Error = SerdeError;

    type SerializeSeq = SerializeCell;
    type SerializeTuple = SerializeCell;
    type SerializeTupleStruct = SerializeCell;
    type SerializeTupleVariant = SerializeTupleVariant;
    type SerializeMap = SerializeMap;
    type SerializeStruct = StructSerializer<'a>;
    type SerializeStructVariant = StructSerializer<'a>;

    #[inline]
    fn serialize_bool(self, value: bool) -> Result<Self::Ok, Self::Error> {
        self.serialize_u8(value.into())
    }

    #[inline]
    fn serialize_i8(self, _value: i8) -> Result<Self::Ok, Self::Error> {
        Err(SerdeError::Function(
            "Unsigned integers not supported".into(),
        ))
    }

    #[inline]
    fn serialize_i16(self, _value: i16) -> Result<Self::Ok, Self::Error> {
        Err(SerdeError::Function(
            "Unsigned integers not supported".into(),
        ))
    }

    #[inline]
    fn serialize_i32(self, _value: i32) -> Result<Self::Ok, Self::Error> {
        Err(SerdeError::Function(
            "Unsigned integers not supported".into(),
        ))
    }

    #[inline]
    fn serialize_i64(self, _value: i64) -> Result<Self::Ok, Self::Error> {
        Err(SerdeError::Function(
            "Unsigned integers not supported".into(),
        ))
    }

    #[inline]
    fn serialize_u8(self, value: u8) -> Result<Self::Ok, Self::Error> {
        Ok(ZData::Atom(vec![value]))
    }

    #[inline]
    fn serialize_u16(self, value: u16) -> Result<Self::Ok, Self::Error> {
        Ok(ZData::Atom(u16::to_le_bytes(value).to_vec()))
    }

    #[inline]
    fn serialize_u32(self, value: u32) -> Result<Self::Ok, Self::Error> {
        Ok(ZData::Atom(u32::to_le_bytes(value).to_vec()))
    }

    #[inline]
    fn serialize_u64(self, value: u64) -> Result<Self::Ok, Self::Error> {
        Ok(ZData::Atom(u64::to_le_bytes(value).to_vec()))
    }

    #[inline]
    fn serialize_f32(self, _value: f32) -> Result<Self::Ok, Self::Error> {
        Err(SerdeError::Function("Floats not supported".into()))
    }

    #[inline]
    fn serialize_f64(self, _value: f64) -> Result<Self::Ok, Self::Error> {
        Err(SerdeError::Function("Floats not supported".into()))
    }

    #[inline]
    fn serialize_char(self, value: char) -> Result<Self::Ok, Self::Error> {
        self.serialize_u32(value as u32)
    }

    #[inline]
    fn serialize_str(self, value: &str) -> Result<Self::Ok, Self::Error> {
        self.serialize_bytes(value.as_bytes())
    }

    fn serialize_bytes(self, value: &[u8]) -> Result<Self::Ok, Self::Error> {
        Ok(ZData::Atom(value.to_vec()))
    }

    #[inline]
    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        self.serialize_none()
    }

    #[inline]
    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        self.serialize_none()
    }

    #[inline]
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        // Assuming # of variants < 128 for now
        Ok(ZData::Cell(vec![
            self.serialize_u8(u8::try_from(variant_index).unwrap())?
        ]))
    }

    #[inline]
    fn serialize_newtype_struct<T: ?Sized>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ser::Serialize,
    {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T: ?Sized>(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ser::Serialize,
    {
        // Assuming # of variants < 128 for now
        Ok(ZData::Cell(vec![
            u8::try_from(variant_index).unwrap().serialize(self)?,
            value.serialize(self)?,
        ]))
    }

    #[inline]
    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        Ok(ZData::Atom(vec![]))
    }

    #[inline]
    fn serialize_some<T: ?Sized>(self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: ser::Serialize,
    {
        Ok(ZData::Cell(vec![value.serialize(self)?]))
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Ok(SerializeCell {
            cell: Vec::with_capacity(len.unwrap_or(0)),
        })
    }

    #[inline]
    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        self.serialize_seq(Some(len))
    }

    #[inline]
    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        self.serialize_seq(Some(len))
    }

    #[inline]
    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Ok(SerializeTupleVariant {
            variant_index,
            cell: Vec::with_capacity(len),
        })
    }

    #[inline]
    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Ok(SerializeMap {
            cell: Vec::with_capacity(len.unwrap_or(0)),
            next_key: None,
        })
    }

    #[inline]
    fn serialize_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        Ok(StructSerializer {
            ser: self,
            cell: Vec::new(),
            variant_index: 0,
        })
    }

    #[inline]
    fn serialize_struct_variant(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        Ok(StructSerializer {
            ser: self,
            cell: Vec::new(),
            variant_index,
        })
    }

    #[inline]
    fn is_human_readable(&self) -> bool {
        false
    }
}

impl ser::SerializeSeq for SerializeCell {
    type Ok = ZData;
    type Error = SerdeError;

    fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ser::Serialize,
    {
        self.cell.push(value.serialize(&Serializer)?);
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(ZData::Cell(self.cell))
    }
}

impl ser::SerializeTuple for SerializeCell {
    type Ok = ZData;
    type Error = SerdeError;

    fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ser::Serialize,
    {
        ser::SerializeSeq::serialize_element(self, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        ser::SerializeSeq::end(self)
    }
}

impl ser::SerializeTupleStruct for SerializeCell {
    type Ok = ZData;
    type Error = SerdeError;

    fn serialize_field<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ser::Serialize,
    {
        ser::SerializeSeq::serialize_element(self, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        ser::SerializeSeq::end(self)
    }
}

impl ser::SerializeTupleVariant for SerializeTupleVariant {
    type Ok = ZData;
    type Error = SerdeError;

    fn serialize_field<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ser::Serialize,
    {
        self.cell.push(value.serialize(&Serializer)?);
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        let mut res = vec![u8::try_from(self.variant_index)
            .unwrap()
            .serialize(&Serializer)?];
        res.extend(self.cell);
        Ok(ZData::Cell(res))
    }
}

impl ser::SerializeMap for SerializeMap {
    type Ok = ZData;
    type Error = SerdeError;

    fn serialize_key<T: ?Sized>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: ser::Serialize,
    {
        self.next_key = Some(key.serialize(&Serializer)?);
        Ok(())
    }

    fn serialize_value<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ser::Serialize,
    {
        let key = self
            .next_key
            .take()
            .expect("serialize_value called before serialize_key");
        //self.cell.push(ta::Cell(vec![key, value.serialize(&Serializer)?]));
        self.cell.extend(vec![key, value.serialize(&Serializer)?]);
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(ZData::Cell(self.cell))
    }
}

impl<'a> ser::SerializeStruct for StructSerializer<'a> {
    type Ok = ZData;
    type Error = SerdeError;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ser::Serialize + ?Sized,
    {
        self.serialize_field_inner(key, value)
    }

    fn skip_field(&mut self, key: &'static str) -> Result<(), Self::Error> {
        self.skip_field_inner(key)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(ZData::Cell(self.end_inner()?))
    }
}

impl<'a> ser::SerializeStructVariant for StructSerializer<'a> {
    type Ok = ZData;
    type Error = SerdeError;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ser::Serialize + ?Sized,
    {
        self.serialize_field_inner(key, value)
    }

    fn skip_field(&mut self, key: &'static str) -> Result<(), Self::Error> {
        self.skip_field_inner(key)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        let mut cell = vec![u8::try_from(self.variant_index)
            .unwrap()
            .serialize(self.ser)?];
        cell.extend(self.end_inner()?);
        Ok(ZData::Cell(cell))
    }
}

#[cfg(test)]
mod tests {
    //use super::*;

    use crate::tag::{ContTag, ExprTag};
    use crate::tag::{Op1, Op2};
    use crate::uint::UInt;
    use crate::z_cont::ZCont;
    use crate::z_data::to_z_data;
    use crate::z_data::Encodable;
    use crate::z_expr::ZExpr;
    use crate::z_ptr::{ZContPtr, ZExprPtr};
    use crate::z_store::ZStore;
    use pasta_curves::pallas::Scalar;

    #[test]
    fn ser_z_expr() {
        let test_zexpr = |ze: ZExpr<Scalar>| {
            let zd = to_z_data(ze).unwrap();
            println!("ZData: {:?}", zd);
            //assert_eq!(ze.ser(), zd);
        };
        let f = Scalar::one();
        let zp = ZExprPtr::from_parts(ExprTag::Sym, f);
        assert_eq!(zp.ser(), to_z_data(zp).unwrap());
        let zc = ZContPtr::from_parts(ContTag::Lookup, f);
        assert_eq!(zc.ser(), to_z_data(zc).unwrap());

        test_zexpr(ZExpr::Nil);
        test_zexpr(ZExpr::Cons(zp, zp));
        test_zexpr(ZExpr::Comm(f, zp));
        test_zexpr(ZExpr::SymNil);
        test_zexpr(ZExpr::SymCons(zp, zp));
        test_zexpr(ZExpr::Key(zp));
        test_zexpr(ZExpr::Fun {
            arg: zp,
            body: zp,
            closed_env: zp,
        });
        test_zexpr(ZExpr::Num(f));
        test_zexpr(ZExpr::StrNil);
        test_zexpr(ZExpr::StrCons(zp, zp));
        test_zexpr(ZExpr::Thunk(zp, zc));
        test_zexpr(ZExpr::Char('a'));
        test_zexpr(ZExpr::Uint(UInt::U64(0)));

        let zs: ZStore<Scalar> = ZStore::new();
        assert_eq!(zs.ser(), to_z_data(zs).unwrap());
    }

    #[test]
    fn ser_z_cont() {
        let test_zcont = |zc: ZCont<Scalar>| {
            assert_eq!(zc.ser(), to_z_data(zc).unwrap());
        };
        let f = Scalar::one();
        let ze = ZExprPtr::from_parts(ExprTag::Nil, f);
        let zp = ZContPtr::from_parts(ContTag::Outermost, f);
        assert_eq!(zp.ser(), to_z_data(zp).unwrap());

        test_zcont(ZCont::Outermost);
        test_zcont(ZCont::Call0 {
            saved_env: ze,
            continuation: zp,
        });
        test_zcont(ZCont::Call {
            unevaled_arg: ze,
            saved_env: ze,
            continuation: zp,
        });
        test_zcont(ZCont::Call2 {
            function: ze,
            saved_env: ze,
            continuation: zp,
        });
        test_zcont(ZCont::Tail {
            saved_env: ze,
            continuation: zp,
        });
        test_zcont(ZCont::Error);
        test_zcont(ZCont::Lookup {
            saved_env: ze,
            continuation: zp,
        });
        test_zcont(ZCont::Unop {
            operator: Op1::Car,
            continuation: zp,
        });
        test_zcont(ZCont::Binop {
            operator: Op2::Sum,
            saved_env: ze,
            unevaled_args: ze,
            continuation: zp,
        });
        test_zcont(ZCont::Binop2 {
            operator: Op2::Sum,
            evaled_arg: ze,
            continuation: zp,
        });
        test_zcont(ZCont::If {
            unevaled_args: ze,
            continuation: zp,
        });
        test_zcont(ZCont::Let {
            var: ze,
            body: ze,
            saved_env: ze,
            continuation: zp,
        });
        test_zcont(ZCont::LetRec {
            var: ze,
            body: ze,
            saved_env: ze,
            continuation: zp,
        });
        test_zcont(ZCont::Emit { continuation: zp });
        test_zcont(ZCont::Dummy);
        test_zcont(ZCont::Terminal);
    }
}
