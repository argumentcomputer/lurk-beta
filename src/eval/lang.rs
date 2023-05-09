use std::collections::HashMap;
use std::fmt::Debug;
use std::marker::PhantomData;

use lurk_macros::Coproc;
use serde::{Deserialize, Serialize};

use crate::coprocessor::{CoCircuit, Coprocessor};
use crate::field::LurkField;
use crate::ptr::Ptr;
use crate::store::Store;
use crate::symbol::Symbol;
use crate::z_ptr::ZExprPtr;

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
    coprocessors: HashMap<Symbol, (C, ZExprPtr<F>)>,
}

impl<F: LurkField, C: Coprocessor<F>> Lang<F, C> {
    pub fn new() -> Self {
        Self {
            coprocessors: Default::default(),
        }
    }

    pub fn new_with_bindings<B: Into<Binding<F, C>>>(s: &mut Store<F>, bindings: Vec<B>) -> Self {
        let mut new = Self {
            coprocessors: Default::default(),
        };
        for b in bindings {
            new.add_binding(b.into(), s);
        }

        new
    }

    pub fn key(&self) -> String {
        let mut key = String::new();

        for coprocessor in &self.coprocessors {
            let name = match coprocessor.0 {
                Symbol::Sym(sym) => sym,
                Symbol::Key(sym) => sym,
            }
            .join("-");

            key += name.as_str()
        }
        key
    }

    pub fn add_coprocessor<T: Into<C>, S: Into<Symbol>>(
        &mut self,
        name: S,
        cproc: T,
        store: &mut Store<F>,
    ) {
        let name = name.into();
      // TODO: Check if intern_symbol should take a reference
        let ptr = store.intern_symbol(name.clone());
        let scalar_ptr = store.hash_expr(&ptr).unwrap();

        self.coprocessors.insert(name, (cproc.into(), scalar_ptr));
    }

    pub fn add_binding<B: Into<Binding<F, C>>>(&mut self, binding: B, store: &mut Store<F>) {
        let Binding { name, coproc, _p } = binding.into();
        let ptr = store.intern_symbol(name.clone());
        let scalar_ptr = store.hash_expr(&ptr).unwrap();

        self.coprocessors.insert(name, (coproc, scalar_ptr));
    }

    pub fn coprocessors(&self) -> &HashMap<Symbol, (C, ZExprPtr<F>)> {
        &self.coprocessors
    }

    pub fn max_coprocessor_arity(&self) -> usize {
        self.coprocessors
            .values()
            .map(|(c, _)| c.arity())
            .max()
            .unwrap_or(0)
    }

    pub fn lookup(&self, s: &Store<F>, name: Ptr<F>) -> Option<&(C, ZExprPtr<F>)> {
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

pub struct Binding<F: LurkField, C: Coprocessor<F>> {
    name: Symbol,
    coproc: C,
    _p: PhantomData<F>,
}

impl<F: LurkField, C: Coprocessor<F>, S: Into<Symbol>> From<(S, C)> for Binding<F, C> {
    fn from(pair: (S, C)) -> Self {
        Self::new(pair.0, pair.1)
    }
}

impl<F: LurkField, C: Coprocessor<F>> Binding<F, C> {
    pub fn new<T: Into<C>, S: Into<Symbol>>(name: S, coproc: T) -> Self {
        Self {
            name: name.into(),
            coproc: coproc.into(),
            _p: Default::default(),
        }
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
        let name = Symbol::sym(vec!["".into(), "cproc".into(), "dumb".into()]);
        let dummy = DummyCoprocessor::new();

        lang.add_coprocessor(name, dummy, store);
    }
}
