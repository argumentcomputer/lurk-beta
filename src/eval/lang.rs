use std::collections::HashMap;
use std::marker::PhantomData;

use bellperson::Circuit;

use crate::coprocessor::Coprocessor;
use crate::field::LurkField;
use crate::sym::Sym;

// TODO: Define a trait for the Hash and parameterize on that also.
pub struct Lang<F: LurkField> {
    coprocessors: HashMap<Sym, Box<dyn Coprocessor<F>>>,
    _p: PhantomData<F>,
}
