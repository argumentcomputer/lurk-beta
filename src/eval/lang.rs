use std::collections::HashMap;
use std::fmt::Debug;

use crate::coprocessor::Coprocessor;
use crate::field::LurkField;
use crate::store::{Ptr, Store};
use crate::sym::Sym;

// TODO: Define a trait for the Hash and parameterize on that also.
#[derive(Debug, Default, Clone)]
pub struct Lang<'a, F: LurkField> {
    coprocessors: HashMap<Sym, &'a dyn Coprocessor<F>>,
}

impl<'a, F: LurkField> Lang<'a, F> {
    pub fn new() -> Self {
        Self {
            coprocessors: Default::default(),
        }
    }

    pub fn add_coprocessor(&mut self, name: Sym, cproc: &'a dyn Coprocessor<F>) {
        self.coprocessors.insert(name, cproc);
    }

    pub fn lookup(&self, s: &Store<F>, name: Ptr<F>) -> Option<&dyn Coprocessor<F>> {
        let name_ptr = s.fetch_maybe_sym(&name);

        name_ptr
            .and_then(|sym| self.coprocessors.get(&sym))
            .copied()
    }

    pub fn has_coprocessors(&self) -> bool {
        !self.coprocessors.is_empty()
    }

    pub fn is_default(&self) -> bool {
        !self.has_coprocessors()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::coprocessor::test::DumbCoprocessor;

    use pasta_curves::pallas::Scalar as Fr;

    #[test]
    fn lang() {
        Lang::<Fr>::new();
    }

    #[test]
    fn dumb_lang() {
        let mut lang = Lang::<Fr>::new();
        let name = Sym::new(".cproc.dumb".to_string());
        let dumb = DumbCoprocessor::new();

        lang.add_coprocessor(name, &dumb);
    }
}
