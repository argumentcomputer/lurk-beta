use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};

use super::{
    query::{CircuitQuery, Query, RecursiveQuery},
    CircuitScope, LogMemo, LogMemoCircuit, Scope,
};
use crate::circuit::gadgets::constraints::alloc_is_zero;
use crate::circuit::gadgets::pointer::AllocatedPtr;
use crate::field::LurkField;
use crate::lem::circuit::GlobalAllocator;
use crate::lem::{pointers::Ptr, store::Store};
use crate::symbol::Symbol;
use crate::tag::{ExprTag, Tag};

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub(crate) enum DemoQuery<F> {
    Factorial(Ptr),
    Phantom(F),
}

#[derive(Debug, Clone)]
pub(crate) enum DemoCircuitQuery<F: LurkField> {
    Factorial(AllocatedPtr<F>),
}

impl<F: LurkField> Query<F> for DemoQuery<F> {
    type CQ = DemoCircuitQuery<F>;

    fn eval(&self, scope: &mut Scope<Self, LogMemo<F>, F>) -> Ptr {
        match self {
            Self::Factorial(n) => {
                let n_zptr = scope.store.hash_ptr(n);
                let n = n_zptr.value();

                if *n == F::ZERO {
                    scope.store.num(F::ONE)
                } else {
                    let sub_query = Self::Factorial(scope.store.num(*n - F::ONE));
                    let m_ptr = self.recursive_eval(scope, sub_query);
                    let m_zptr = scope.store.hash_ptr(&m_ptr);
                    let m = m_zptr.value();

                    scope.store.num(*n * m)
                }
            }
            _ => unreachable!(),
        }
    }

    fn symbol(&self) -> Symbol {
        match self {
            Self::Factorial(_) => Symbol::sym(&["lurk", "user", "factorial"]),
            _ => unreachable!(),
        }
    }

    fn from_ptr(s: &Store<F>, ptr: &Ptr) -> Option<Self> {
        let (head, body) = s.car_cdr(ptr).expect("query should be cons");
        let sym = s.fetch_sym(&head).expect("head should be sym");

        if sym == Symbol::sym(&["lurk", "user", "factorial"]) {
            let num = body;
            Some(Self::Factorial(num))
        } else {
            None
        }
    }

    fn to_ptr(&self, s: &Store<F>) -> Ptr {
        match self {
            Self::Factorial(n) => {
                let factorial = s.intern_symbol(&self.symbol());

                s.cons(factorial, *n)
            }
            _ => unreachable!(),
        }
    }

    fn to_circuit<CS: ConstraintSystem<F>>(&self, cs: &mut CS, s: &Store<F>) -> Self::CQ {
        match self {
            DemoQuery::Factorial(n) => {
                Self::CQ::Factorial(AllocatedPtr::alloc_infallible(cs, || s.hash_ptr(n)))
            }
            _ => unreachable!(),
        }
    }

    fn dummy_from_index(s: &Store<F>, index: usize) -> Self {
        match index {
            0 => Self::Factorial(s.num(0.into())),
            _ => unreachable!(),
        }
    }

    fn index(&self) -> usize {
        match self {
            Self::Factorial(_) => 0,
            _ => unreachable!(),
        }
    }

    fn count() -> usize {
        1
    }
}

impl<F: LurkField> RecursiveQuery<F> for DemoCircuitQuery<F> {
    // It would be nice if this could be passed to `CircuitQuery::recurse` as an optional closure, rather than be a
    // trait method. That would allow more generality. The types get complicated, though. For generality, we should
    // support a context object that can be initialized once in `synthesize_eval` and be passed through for use here.
    fn post_recursion<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        subquery_results: &[AllocatedPtr<F>],
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        assert_eq!(subquery_results.len(), 1);
        let subquery_result = &subquery_results[0];
        match self {
            Self::Factorial(n) => {
                let result_f = n.hash().mul(
                    ns!(cs, "incremental multiplication"),
                    subquery_result.hash(),
                )?;

                AllocatedPtr::alloc_tag(ns!(cs, "result"), ExprTag::Num.to_field(), result_f)
            }
        }
    }
}

impl<F: LurkField> CircuitQuery<F> for DemoCircuitQuery<F> {
    fn synthesize_args<CS: ConstraintSystem<F>>(
        &self,
        _cs: &mut CS,
        _g: &GlobalAllocator<F>,
        _store: &Store<F>,
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        match self {
            Self::Factorial(n) => Ok(n.clone()),
        }
    }

    fn synthesize_eval<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        scope: &mut CircuitScope<F, LogMemoCircuit<F>>,
        acc: &AllocatedPtr<F>,
        allocated_key: &AllocatedPtr<F>,
    ) -> Result<((AllocatedPtr<F>, AllocatedPtr<F>), AllocatedPtr<F>), SynthesisError> {
        match self {
            Self::Factorial(n) => {
                // FIXME: Check n tag or decide not to.
                let base_case_f = g.alloc_const(cs, F::ONE);
                let base_case = AllocatedPtr::alloc_tag(
                    ns!(cs, "base_case"),
                    ExprTag::Num.to_field(),
                    base_case_f.clone(),
                )?;

                let n_is_zero = alloc_is_zero(ns!(cs, "n_is_zero"), n.hash())?;

                let new_n = AllocatedNum::alloc(ns!(cs, "new_n"), || {
                    n.hash()
                        .get_value()
                        .map(|n| n - F::ONE)
                        .ok_or(SynthesisError::AssignmentMissing)
                })?;

                // new_n * 1 = n - 1
                cs.enforce(
                    || "enforce_new_n",
                    |lc| lc + new_n.get_variable(),
                    |lc| lc + CS::one(),
                    |lc| lc + n.hash().get_variable() - CS::one(),
                );

                let new_num =
                    AllocatedPtr::alloc_tag(ns!(cs, "new_num"), ExprTag::Num.to_field(), new_n)?;

                let subquery = Self::Factorial(new_num);

                self.recurse(
                    cs,
                    g,
                    store,
                    scope,
                    &[subquery],
                    &n_is_zero.not(),
                    (&base_case, acc),
                    allocated_key,
                )
            }
        }
    }

    fn from_ptr<CS: ConstraintSystem<F>>(cs: &mut CS, s: &Store<F>, ptr: &Ptr) -> Option<Self> {
        DemoQuery::from_ptr(s, ptr).map(|q| q.to_circuit(cs, s))
    }

    fn dummy_from_index<CS: ConstraintSystem<F>>(cs: &mut CS, s: &Store<F>, index: usize) -> Self {
        DemoQuery::dummy_from_index(s, index).to_circuit(cs, s)
    }

    fn symbol(&self) -> Symbol {
        match self {
            Self::Factorial(_) => Symbol::sym(&["lurk", "user", "factorial"]),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use ff::Field;
    use halo2curves::bn256::Fr as F;
    use std::sync::Arc;

    #[test]
    fn test_factorial() {
        let s = Arc::new(Store::default());
        let zero = s.num(F::ZERO);
        let one = s.num(F::ONE);
        let two = s.num(F::from_u64(2));
        let three = s.num(F::from_u64(3));
        let four = s.num(F::from_u64(4));
        let six = s.num(F::from_u64(6));
        let twenty_four = s.num(F::from_u64(24));
        let mut scope: Scope<DemoQuery<F>, LogMemo<F>, F> = Scope::new(1, s);
        assert_eq!(one, DemoQuery::Factorial(zero).eval(&mut scope));
        assert_eq!(one, DemoQuery::Factorial(one).eval(&mut scope));
        assert_eq!(two, DemoQuery::Factorial(two).eval(&mut scope));
        assert_eq!(six, DemoQuery::Factorial(three).eval(&mut scope));
        assert_eq!(twenty_four, DemoQuery::Factorial(four).eval(&mut scope));
    }
}
