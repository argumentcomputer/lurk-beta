use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};

use super::{CircuitScope, CircuitTranscript, LogMemo, Scope};
use crate::circuit::gadgets::constraints::alloc_is_zero;
use crate::coprocessor::gadgets::construct_list;
use crate::coprocessor::AllocatedPtr;
use crate::field::LurkField;
use crate::lem::circuit::GlobalAllocator;
use crate::lem::{pointers::Ptr, store::Store};
use crate::symbol::Symbol;
use crate::tag::{ExprTag, Tag};

pub trait Query<F: LurkField>
where
    Self: Sized,
{
    fn eval(&self, s: &Store<F>, scope: &mut Scope<F, Self, LogMemo<F>>) -> Ptr;
    fn recursive_eval(
        &self,
        scope: &mut Scope<F, Self, LogMemo<F>>,
        s: &Store<F>,
        subquery: Self,
    ) -> Ptr;
    fn from_ptr(s: &Store<F>, ptr: &Ptr) -> Option<Self>;
    fn to_ptr(&self, s: &Store<F>) -> Ptr;
    fn symbol(&self) -> Symbol;
    fn symbol_ptr(&self, s: &Store<F>) -> Ptr {
        s.intern_symbol(&self.symbol())
    }

    fn index(&self) -> usize;
}

#[allow(unreachable_pub)]
pub trait CircuitQuery<F: LurkField>
where
    Self: Sized,
{
    type Q: Query<F>;

    fn synthesize_eval<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        scope: &mut CircuitScope<F, Self::Q, LogMemo<F>>,
        acc: &AllocatedPtr<F>,
        transcript: &CircuitTranscript<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, CircuitTranscript<F>), SynthesisError>;

    fn symbol(&self, s: &Store<F>) -> Symbol {
        self.dummy_query_variant(s).symbol()
    }

    fn symbol_ptr(&self, s: &Store<F>) -> Ptr {
        self.dummy_query_variant(s).symbol_ptr(s)
    }

    fn from_ptr<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        s: &Store<F>,
        ptr: &Ptr,
    ) -> Result<Option<Self>, SynthesisError>;

    fn dummy_query_variant(&self, s: &Store<F>) -> Self::Q;
}

#[derive(Debug, Clone)]
pub enum DemoQuery<F> {
    Factorial(Ptr),
    Phantom(F),
}

pub enum DemoCircuitQuery<F: LurkField> {
    Factorial(AllocatedPtr<F>),
}

impl<F: LurkField> Query<F> for DemoQuery<F> {
    // DemoQuery and Scope depend on each other.
    fn eval(&self, s: &Store<F>, scope: &mut Scope<F, Self, LogMemo<F>>) -> Ptr {
        match self {
            Self::Factorial(n) => {
                let n_zptr = s.hash_ptr(n);
                let n = n_zptr.value();

                if *n == F::ZERO {
                    s.num(F::ONE)
                } else {
                    let m_ptr = self.recursive_eval(scope, s, Self::Factorial(s.num(*n - F::ONE)));
                    let m_zptr = s.hash_ptr(&m_ptr);
                    let m = m_zptr.value();

                    s.num(*n * m)
                }
            }
            _ => unreachable!(),
        }
    }

    fn recursive_eval(
        &self,
        scope: &mut Scope<F, Self, LogMemo<F>>,
        s: &Store<F>,
        subquery: Self,
    ) -> Ptr {
        scope.query_recursively(s, self, subquery)
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
            let (num, _) = s.car_cdr(&body).expect("query body should be cons");
            Some(Self::Factorial(num))
        } else {
            None
        }
    }

    fn to_ptr(&self, s: &Store<F>) -> Ptr {
        match self {
            Self::Factorial(n) => {
                let factorial = s.intern_symbol(&self.symbol());

                s.list(vec![factorial, *n])
            }
            _ => unreachable!(),
        }
    }

    fn index(&self) -> usize {
        match self {
            Self::Factorial(_) => 0,
            _ => unreachable!(),
        }
    }
}

impl<F: LurkField> CircuitQuery<F> for DemoCircuitQuery<F> {
    type Q = DemoQuery<F>;

    fn dummy_query_variant(&self, s: &Store<F>) -> Self::Q {
        match self {
            Self::Factorial(_) => Self::Q::Factorial(s.num(F::ZERO)),
        }
    }

    fn synthesize_eval<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        store: &Store<F>,
        scope: &mut CircuitScope<F, Self::Q, LogMemo<F>>,
        acc: &AllocatedPtr<F>,
        transcript: &CircuitTranscript<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, CircuitTranscript<F>), SynthesisError> {
        match self {
            // TODO: Factor out the recursive boilerplate so individual queries can just implement their distinct logic
            // using a sane framework.
            Self::Factorial(n) => {
                // FIXME: Check n tag or decide not to.
                let base_case_f = g.alloc_const(cs, F::ONE);
                let base_case = AllocatedPtr::alloc_tag(
                    &mut cs.namespace(|| "base_case"),
                    ExprTag::Num.to_field(),
                    base_case_f.clone(),
                )?;

                let n_is_zero = alloc_is_zero(&mut cs.namespace(|| "n_is_zero"), n.hash())?;

                let (recursive_result, recursive_acc, recursive_transcript) = {
                    let new_n = AllocatedNum::alloc(&mut cs.namespace(|| "new_n"), || {
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

                    let subquery = {
                        let symbol =
                            g.alloc_ptr(cs, &store.intern_symbol(&self.symbol(store)), store);

                        let new_num = AllocatedPtr::alloc_tag(
                            &mut cs.namespace(|| "new_num"),
                            ExprTag::Num.to_field(),
                            new_n,
                        )?;
                        construct_list(
                            &mut cs.namespace(|| "subquery"),
                            g,
                            store,
                            &[&symbol, &new_num],
                            None,
                        )?
                    };

                    let (sub_result, new_acc, new_transcript) = scope.synthesize_query(
                        &mut cs.namespace(|| "recursive query"),
                        g,
                        store,
                        &subquery,
                        acc,
                        transcript,
                        &n_is_zero.not(),
                    )?;

                    let result_f = n.hash().mul(
                        &mut cs.namespace(|| "incremental multiplication"),
                        sub_result.hash(),
                    )?;

                    let result = AllocatedPtr::alloc_tag(
                        &mut cs.namespace(|| "result"),
                        ExprTag::Num.to_field(),
                        result_f,
                    )?;

                    (result, new_acc, new_transcript)
                };

                let value = AllocatedPtr::pick(
                    &mut cs.namespace(|| "pick value"),
                    &n_is_zero,
                    &base_case,
                    &recursive_result,
                )?;

                let acc = AllocatedPtr::pick(
                    &mut cs.namespace(|| "pick acc"),
                    &n_is_zero,
                    acc,
                    &recursive_acc,
                )?;

                let transcript = CircuitTranscript::pick(
                    &mut cs.namespace(|| "pick recursive_transcript"),
                    &n_is_zero,
                    transcript,
                    &recursive_transcript,
                )?;

                Ok((value, acc, transcript))
            }
        }
    }

    fn from_ptr<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        s: &Store<F>,
        ptr: &Ptr,
    ) -> Result<Option<Self>, SynthesisError> {
        let query = Self::Q::from_ptr(s, ptr);
        Ok(if let Some(q) = query {
            match q {
                Self::Q::Factorial(n) => Some(Self::Factorial(AllocatedPtr::alloc(cs, || {
                    Ok(s.hash_ptr(&n))
                })?)),
                _ => unreachable!(),
            }
        } else {
            None
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use ff::Field;
    use pasta_curves::pallas::Scalar as F;

    #[test]
    fn test_factorial() {
        let s = Store::default();
        let mut scope: Scope<F, DemoQuery<F>, LogMemo<F>> = Scope::default();
        let zero = s.num(F::ZERO);
        let one = s.num(F::ONE);
        let two = s.num(F::from_u64(2));
        let three = s.num(F::from_u64(3));
        let four = s.num(F::from_u64(4));
        let six = s.num(F::from_u64(6));
        let twenty_four = s.num(F::from_u64(24));
        assert_eq!(one, DemoQuery::Factorial(zero).eval(&s, &mut scope));
        assert_eq!(one, DemoQuery::Factorial(one).eval(&s, &mut scope));
        assert_eq!(two, DemoQuery::Factorial(two).eval(&s, &mut scope));
        assert_eq!(six, DemoQuery::Factorial(three).eval(&s, &mut scope));
        assert_eq!(twenty_four, DemoQuery::Factorial(four).eval(&s, &mut scope));
    }
}
