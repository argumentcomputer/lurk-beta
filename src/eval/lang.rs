use std::collections::HashMap;
use std::fmt::Debug;
use std::marker::PhantomData;

use bellperson::{ConstraintSystem, SynthesisError};
use serde::{Deserialize, Serialize};

use crate::circuit::gadgets::pointer::{AllocatedContPtr, AllocatedPtr};
use crate::coprocessor::{CoCircuit, Coprocessor};
use crate::field::LurkField;
use crate::store::{Ptr, ScalarPtr, Store};
use crate::sym::Sym;

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

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Coproc<F: LurkField> {
    Dummy(DummyCoprocessor<F>),
}

impl<F: LurkField> Coprocessor<F> for Coproc<F> {
    fn eval_arity(&self) -> usize {
        match self {
            Self::Dummy(c) => c.eval_arity(),
        }
    }

    fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
        match self {
            Self::Dummy(c) => c.simple_evaluate(s, args),
        }
    }
}

impl<F: LurkField> CoCircuit<F> for Coproc<F> {
    fn arity(&self) -> usize {
        match self {
            Self::Dummy(c) => c.arity(),
        }
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &Store<F>,
        input_exprs: &[AllocatedPtr<F>],
        input_env: &AllocatedPtr<F>,
        input_cont: &AllocatedContPtr<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        match self {
            Self::Dummy(c) => c.synthesize(cs, store, input_exprs, input_env, input_cont),
        }
    }
}

// TODO: Define a trait for the Hash and parameterize on that also.
#[derive(Debug, Default, Clone)]
pub struct Lang<F: LurkField, C: Coprocessor<F>> {
    coprocessors: HashMap<Sym, (C, ScalarPtr<F>)>,
    _p: PhantomData<F>,
}

impl<F: LurkField, C: Coprocessor<F>> Lang<F, C> {
    pub fn new() -> Self {
        Self {
            coprocessors: Default::default(),
            _p: Default::default(),
        }
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
        let c: Option<&(C, _)> = self.coprocessors.values().max_by_key(|(c, _)| c.arity());

        c.map(|(c, _)| c.arity()).unwrap_or(0)
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
