use indexmap::IndexMap;
use lurk_macros::Coproc;
use serde::{Deserialize, Serialize};
use std::{fmt::Debug, marker::PhantomData};

use crate::{
    self as lurk,
    coprocessor::{CoCircuit, Coprocessor},
    field::LurkField,
    lem::{pointers::Ptr, store::Store},
    symbol::Symbol,
};

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
    fn evaluate_simple(&self, s: &Store<F>, _args: &[Ptr]) -> Ptr {
        s.intern_nil()
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
#[derive(Debug, Default, Clone, Deserialize, Serialize)]
pub struct Lang<F: LurkField, C: Coprocessor<F>> {
    /// An IndexMap that stores coprocessors with their associated `Sym` keys.
    coprocessors: IndexMap<Symbol, C>,
    _p: PhantomData<F>,
}

impl<F: LurkField, C: Coprocessor<F>> Lang<F, C> {
    #[inline]
    pub fn new() -> Self {
        Self {
            coprocessors: IndexMap::default(),
            _p: PhantomData,
        }
    }

    pub fn new_with_bindings<B: Into<Binding<F, C>>>(bindings: Vec<B>) -> Self {
        let mut new = Self::new();
        for b in bindings {
            new.add_binding(b.into());
        }

        new
    }

    pub fn key(&self) -> String {
        let mut key = String::new();
        if self.has_coprocessors() {
            for coprocessor in &self.coprocessors {
                let name = coprocessor.0.path().join("-");
                key += name.as_str()
            }
        } else {
            key += "none"
        }
        key
    }

    pub fn add_coprocessor<T: Into<C>, S: Into<Symbol>>(&mut self, name: S, cproc: T) {
        let name = name.into();
        self.coprocessors.insert(name, cproc.into());
    }

    pub fn add_binding<B: Into<Binding<F, C>>>(&mut self, binding: B) {
        let Binding { name, coproc, _p } = binding.into();
        self.add_coprocessor(name, coproc);
    }

    #[inline]
    pub fn coprocessors(&self) -> &IndexMap<Symbol, C> {
        &self.coprocessors
    }

    #[inline]
    pub fn lookup_by_sym(&self, sym: &Symbol) -> Option<&C> {
        self.coprocessors.get(sym)
    }

    #[inline]
    pub fn has_coprocessors(&self) -> bool {
        !self.coprocessors.is_empty()
    }

    #[inline]
    pub fn is_default(&self) -> bool {
        !self.has_coprocessors()
    }

    #[inline]
    pub fn coprocessor_count(&self) -> usize {
        self.coprocessors.len()
    }

    #[inline]
    pub fn get_index_by_symbol(&self, sym: &Symbol) -> Option<usize> {
        self.coprocessors.get_index_of(sym)
    }
}

/// A `Binding` associates a name (`Sym`) and `Coprocessor`. It facilitates modular construction of `Lang`s using
/// `Coprocessor`s.
#[derive(Debug)]
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
    use crate::sym;

    use super::*;
    use pasta_curves::pallas::Scalar as Fr;

    #[test]
    fn lang() {
        Lang::<Fr, Coproc<Fr>>::new();
    }

    #[test]
    fn dummy_lang() {
        let _lang = Lang::<Fr, Coproc<Fr>>::new_with_bindings(vec![(
            sym!("coproc", "dummy"),
            DummyCoprocessor::new().into(),
        )]);
    }
}
