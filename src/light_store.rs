// This is a temporary shim which should be merged with scalar_store
// Currently it only exists for reading store-dumps

use std::collections::BTreeMap;

use crate::light_data::Encodable;
use crate::light_data::LightData;
use crate::scalar_store::ScalarStore;
use crate::store::ScalarPtr;

use crate::field::LurkField;

pub struct LightStore<F: LurkField> {
    pub scalar_map: BTreeMap<ScalarPtr<F>, Option<LightExpr<F>>>,
}

impl<F: LurkField> Encodable for LightStore<F> {
    fn ser(&self) -> LightData {
        todo!()
    }
    fn de(ld: &LightData) -> Result<Self, String> {
        todo!()
    }
}

impl<F: LurkField> LightStore<F> {
    pub fn to_scalar_store(self) -> ScalarStore<F> {
        todo!()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LightExpr<F: LurkField> {
    Cons(ScalarPtr<F>, ScalarPtr<F>),
    StrCons(ScalarPtr<F>, ScalarPtr<F>),
    Comm(F, ScalarPtr<F>),
    Sym(ScalarPtr<F>),
    Num(F),
    Char(F),
}

impl<F: LurkField> Encodable for LightExpr<F> {
    fn ser(&self) -> LightData {
        todo!()
    }
    fn de(ld: &LightData) -> Result<Self, String> {
        todo!()
    }
}
