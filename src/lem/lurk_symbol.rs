use crate::field::LurkField;

pub enum LurkSymbol {
    Nil,
}

impl LurkSymbol {
    pub fn field<F: LurkField>(&self) -> F {
        match self {
            LurkSymbol::Nil => F::from_u64(0),
        }
    }
}
