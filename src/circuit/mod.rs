use crate::field::LurkField;

use crate::store::Store;

#[macro_use]
pub mod gadgets;

pub mod circuit_frame;

pub trait ToInputs<F: LurkField> {
    fn to_inputs(&self, store: &Store<F>) -> Vec<F>;
    fn input_size() -> usize;
}

impl<F: LurkField, T: ToInputs<F>> ToInputs<F> for Option<T> {
    fn to_inputs(&self, store: &Store<F>) -> Vec<F> {
        if let Some(t) = self {
            t.to_inputs(store)
        } else {
            panic!("no inputs for None");
        }
    }
    fn input_size() -> usize {
        unimplemented!();
    }
}
