use std::collections::HashMap;
use std::fmt::Debug;
use std::marker::PhantomData;

use lurk_macros::Coproc;
use serde::{Deserialize, Serialize};

use crate::coprocessor::{CoCircuit, Coprocessor};
use crate::field::LurkField;
use crate::ptr::{Ptr, ScalarPtr};
use crate::store::Store;
use crate::sym::Sym;

use crate as lurk;

/// `DummyCoprocessor` is a concrete implementation of the [`crate::coprocessor::Coprocessor`] trait.
///
/// It provides specific behavior for a dummy coprocessor.
///
/// # Pattern
/// This struct is an example of a coprocessor implementation that would extend the [`crate::coprocessor::Coprocessor`] trait.
/// More implementations can be added without modifying the existing code, adhering to the open-closed principle.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct DummyCoprocessor<F: LurkField> {
    pub(crate) _p: PhantomData<F>,
}

impl<F: LurkField> Coprocessor<F> for DummyCoprocessor<F> {
    /// Dummy Coprocessor takes no arguments.
    fn eval_arity(&self) -> usize {
        0
    }

    /// And does nothing but return nil. It should probably never be used and can perhaps be eliminated,
    /// but for now it exists as an exemplar demonstrating the intended shape of enums like the default, `Coproc`.
    fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
        assert!(args.is_empty());
        s.get_nil()
    }
}

impl<F: LurkField> CoCircuit<F> for DummyCoprocessor<F> {}

impl<F: LurkField> DummyCoprocessor<F> {
    #[allow(dead_code)]
    pub(crate) fn new() -> Self {
        Self {
            _p: Default::default(),
        }
    }
}

/// `CoProc` is an enum that wraps over different implementations of the [`crate::coprocessor::Coprocessor`] trait.
/// It is used at runtime to encode a finite choice of acceptable coprocessors.
///
/// This enum is the key to constraining a trait hierarchy by allowing us to have a common type
/// for all implementations of the [`crate::coprocessor::Coprocessor`] trait (which e.g. allows putting them in a collection).
///
/// # Pattern
/// The enum `CoProc` serves as the "closing" element of a trait hierarchy, providing
/// a common type for all coprocessor implementations.
#[derive(Clone, Debug, Deserialize, Serialize, Coproc)]
pub enum Coproc<F: LurkField> {
    Dummy(DummyCoprocessor<F>),
}

/// `Lang` is a struct that represents a language with coprocessors.
///
/// It allows late-binding of the exact set of coprocessors by using a type parameter `C` that
/// is expected to have the [`crate::coprocessor::Coprocessor`] trait bound in concrete instantiations.
///
/// # Type Parameters
/// - `F`: A field type that implements the [`crate::field::LurkField`] trait.
/// - `C`: A type that implements the [`crate::coprocessor::Coprocessor`] trait. This allows late-binding of the
///   exact set of coprocessors to be allowed in the `Lang` struct.
///
// TODO: Define a trait for the Hash and parameterize on that also.
#[derive(Debug, Default, Clone)]
pub struct Lang<F: LurkField, C: Coprocessor<F>> {
    //  A HashMap that stores coprocessors with their associated `Sym` keys.
    coprocessors: HashMap<Sym, (C, ScalarPtr<F>)>,
}

impl<F: LurkField, C: Coprocessor<F>> Lang<F, C> {
    pub fn new() -> Self {
        Self {
            coprocessors: Default::default(),
        }
    }

    pub fn key(&self) -> String {
        let mut key = String::new();

        for coprocessor in &self.coprocessors {
            let name = match coprocessor.0 {
                Sym::Sym(sym) => &sym.path,
                Sym::Key(sym) => &sym.path,
            }
            .join("-");

            key += name.as_str()
        }
        key
    }

    pub fn add_coprocessor(&mut self, name: Sym, cproc: C, store: &mut Store<F>) {
        let ptr = store.intern_sym_and_ancestors(&name).unwrap();
        let scalar_ptr = store.get_expr_hash(&ptr).unwrap();

        self.coprocessors.insert(name, (cproc, scalar_ptr));
    }

    pub fn coprocessors(&self) -> &HashMap<Sym, (C, ScalarPtr<F>)> {
        &self.coprocessors
    }

    pub fn max_coprocessor_arity(&self) -> usize {
        self.coprocessors
            .values()
            .map(|(c, _)| c.arity())
            .max()
            .unwrap_or(0)
    }

    pub fn lookup(&self, s: &Store<F>, name: Ptr<F>) -> Option<&(C, ScalarPtr<F>)> {
        let maybe_sym = s.fetch_maybe_sym(&name);

        maybe_sym.and_then(|sym| self.coprocessors.get(&sym))
    }

    pub fn has_coprocessors(&self) -> bool {
        !self.coprocessors.is_empty()
    }

    pub fn is_default(&self) -> bool {
        !self.has_coprocessors()
    }
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use pasta_curves::pallas::Scalar as Fr;

    #[test]
    fn lang() {
        Lang::<Fr, Coproc<Fr>>::new();
    }

    #[test]
    fn dummy_lang() {
        let store = &mut Store::<Fr>::default();
        let mut lang = Lang::<Fr, Coproc<Fr>>::new();
        let name = Sym::new(".cproc.dummy".to_string());
        let dummy = DummyCoprocessor::new();

        lang.add_coprocessor(name, Coproc::Dummy(dummy), store);
    }
}
