use bellpepper::gadgets::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use std::fmt::Debug;

use crate::{
    circuit::gadgets::pointer::AllocatedPtr,
    field::LurkField,
    lem::{circuit::GlobalAllocator, pointers::Ptr, store::Store},
};

pub mod circom;
pub mod gadgets;
pub mod sha256;
pub mod trie;

/// `Coprocessor` is a trait that represents a generalized interface for coprocessors.
/// Coprocessors augment the Lurk circuit and evaluation with additional built-in functionality.
/// This trait generalizes over functionality needed in the evaluator, the sibling `CoCircuit` trait,
/// generalizes over functionality needed in the circuit.
///
/// The trait is implemented by concrete coprocessor types, such as `DummyCoprocessor`.
///
/// # Pattern
/// We use a type class (trait) pattern to provide extensibility for the coprocessor implementations.
/// The pattern involves:
/// - A trait [`crate::coprocessor::Coprocessor`], which defines the methods and behavior for all coprocessors.
/// - An enum such as [`crate::eval::lang::Coproc`], which "closes" the hierarchy of possible coprocessor
///   implementations we want to instantiate at a particular point in the code.
pub trait Coprocessor<F: LurkField>: Clone + Debug + Sync + Send + CoCircuit<F> {
    fn eval_arity(&self) -> usize;

    /// Returns true if this Coprocessor actually implements a circuit.
    fn has_circuit(&self) -> bool {
        false
    }

    /// Function for internal plumbing. Reimplementing is not recommended
    fn evaluate_internal(&self, s: &Store<F>, ptrs: &[Ptr<F>]) -> Vec<Ptr<F>> {
        let arity = self.arity();
        let args = &ptrs[0..arity];
        let env = &ptrs[arity];
        let cont = &ptrs[arity + 1];
        self.evaluate(s, args, env, cont)
    }

    fn evaluate(&self, s: &Store<F>, args: &[Ptr<F>], env: &Ptr<F>, cont: &Ptr<F>) -> Vec<Ptr<F>> {
        vec![self.evaluate_simple(s, args), *env, *cont]
    }

    fn evaluate_simple(&self, _s: &Store<F>, _args: &[Ptr<F>]) -> Ptr<F>;
}

/// `CoCircuit` is a trait that represents a generalized interface for coprocessors.
/// Coprocessors augment the Lurk circuit and evaluation with additional built-in functionality.
/// This trait generalizes over functionality needed in the circuit, the sibling `Coprocessor` trait,
/// generalizes over functionality needed in the evaluator.
///
/// The trait is implemented by concrete coprocessor types, such as `DumbCoprocessor`.
pub trait CoCircuit<F: LurkField>: Send + Sync + Clone {
    fn arity(&self) -> usize {
        todo!()
    }

    /// Function for internal plumbing. Reimplementing is not recommended
    fn synthesize_internal<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        s: &Store<F>,
        not_dummy: &Boolean,
        ptrs: &[AllocatedPtr<F>],
    ) -> Result<Vec<AllocatedPtr<F>>, SynthesisError> {
        let arity = self.arity();
        let args = &ptrs[0..arity];
        let env = &ptrs[arity];
        let cont = &ptrs[arity + 1];
        self.synthesize(cs, g, s, not_dummy, args, env, cont)
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        s: &Store<F>,
        not_dummy: &Boolean,
        args: &[AllocatedPtr<F>],
        env: &AllocatedPtr<F>,
        cont: &AllocatedPtr<F>,
    ) -> Result<Vec<AllocatedPtr<F>>, SynthesisError> {
        Ok(vec![
            self.synthesize_simple(cs, g, s, not_dummy, args)?,
            env.clone(),
            cont.clone(),
        ])
    }

    fn synthesize_simple<CS: ConstraintSystem<F>>(
        &self,
        _cs: &mut CS,
        _g: &GlobalAllocator<F>,
        _s: &Store<F>,
        _not_dummy: &Boolean,
        _args: &[AllocatedPtr<F>],
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        unimplemented!()
    }
}

#[cfg(test)]
pub(crate) mod test {
    use bellpepper_core::num::AllocatedNum;
    use serde::{Deserialize, Serialize};

    use super::*;
    use crate::circuit::gadgets::constraints::{alloc_equal, mul};
    use crate::lem::Tag as LEMTag;
    use crate::tag::{ExprTag, Tag};
    use std::marker::PhantomData;

    /// A dumb Coprocessor for testing.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub(crate) struct DumbCoprocessor<F: LurkField> {
        pub(crate) _p: PhantomData<F>,
    }

    impl<F: LurkField> DumbCoprocessor<F> {
        fn synthesize_aux<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            input_exprs: &[AllocatedPtr<F>],
            input_env: &AllocatedPtr<F>,
            input_cont: &AllocatedPtr<F>,
            num_tag: &AllocatedNum<F>,
            cont_error: &AllocatedPtr<F>,
        ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedPtr<F>), SynthesisError> {
            let a = &input_exprs[0];
            let b = &input_exprs[1];

            let a_is_num = alloc_equal(&mut cs.namespace(|| "fst is num"), a.tag(), num_tag)?;
            let b_is_num = alloc_equal(&mut cs.namespace(|| "snd is num"), b.tag(), num_tag)?;
            let types_are_correct = Boolean::and(
                &mut cs.namespace(|| "types are correct"),
                &a_is_num,
                &b_is_num,
            )?;

            // a^2 + b = c
            let a2 = mul(&mut cs.namespace(|| "square"), a.hash(), a.hash())?;
            let c = a2.add(&mut cs.namespace(|| "add"), b.hash())?;
            let c_ptr = AllocatedPtr::alloc_tag(cs, ExprTag::Num.to_field(), c)?;

            let result_expr0 =
                AllocatedPtr::pick(&mut cs.namespace(|| "result_expr0"), &b_is_num, &c_ptr, b)?;

            // If `a` is not a `Num`, then that error takes precedence, and we return `a`. Otherwise, return either the
            // correct result or `b`, depending on whether `b` is a `Num` or not.
            let result_expr = AllocatedPtr::pick(
                &mut cs.namespace(|| "result_expr"),
                &a_is_num,
                &result_expr0,
                a,
            )?;

            let result_cont = AllocatedPtr::pick(
                &mut cs.namespace(|| "result_cont"),
                &types_are_correct,
                input_cont,
                cont_error,
            )?;

            Ok((result_expr, input_env.clone(), result_cont))
        }
    }

    impl<F: LurkField> CoCircuit<F> for DumbCoprocessor<F> {
        fn arity(&self) -> usize {
            2
        }

        fn synthesize<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            g: &GlobalAllocator<F>,
            s: &Store<F>,
            _not_dummy: &Boolean,
            input_exprs: &[AllocatedPtr<F>],
            input_env: &AllocatedPtr<F>,
            input_cont: &AllocatedPtr<F>,
        ) -> Result<Vec<AllocatedPtr<F>>, SynthesisError> {
            let num_tag = g
                .get_tag(&ExprTag::Num)
                .expect("Num tag should have been allocated");

            let cont_err = g
                .get_allocated_ptr_from_ptr(&s.cont_error(), s)
                .expect("Error pointer should have been allocated");

            let (expr, env, cont) =
                self.synthesize_aux(cs, input_exprs, input_env, input_cont, num_tag, &cont_err)?;

            Ok(vec![expr, env, cont])
        }
    }

    impl<F: LurkField> Coprocessor<F> for DumbCoprocessor<F> {
        /// Dumb Coprocessor takes two arguments.
        fn eval_arity(&self) -> usize {
            2
        }

        fn has_circuit(&self) -> bool {
            true
        }

        fn evaluate(
            &self,
            s: &Store<F>,
            args: &[Ptr<F>],
            env: &Ptr<F>,
            cont: &Ptr<F>,
        ) -> Vec<Ptr<F>> {
            let Ptr::Atom(LEMTag::Expr(ExprTag::Num), a) = &args[0] else {
                return vec![args[0], *env, s.cont_error()];
            };
            let Ptr::Atom(LEMTag::Expr(ExprTag::Num), b) = &args[1] else {
                return vec![args[1], *env, s.cont_error()];
            };
            vec![Ptr::num((*a * *a) + *b), *env, *cont]
        }

        fn evaluate_simple(&self, _s: &Store<F>, _args: &[Ptr<F>]) -> Ptr<F> {
            unreachable!()
        }
    }

    impl<F: LurkField> DumbCoprocessor<F> {
        pub(crate) fn new() -> Self {
            Self {
                _p: Default::default(),
            }
        }
    }

    /// A coprocessor that simply halts the CEK machine, for testing purposes
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub(crate) struct Terminator<F: LurkField> {
        _p: PhantomData<F>,
    }

    impl<F: LurkField> CoCircuit<F> for Terminator<F> {
        fn arity(&self) -> usize {
            0
        }

        fn synthesize<CS: ConstraintSystem<F>>(
            &self,
            _cs: &mut CS,
            g: &GlobalAllocator<F>,
            s: &Store<F>,
            _not_dummy: &Boolean,
            _args: &[AllocatedPtr<F>],
            env: &AllocatedPtr<F>,
            _cont: &AllocatedPtr<F>,
        ) -> Result<Vec<AllocatedPtr<F>>, SynthesisError> {
            let nil = g
                .get_allocated_ptr_from_ptr(&s.intern_nil(), s)
                .expect("nil pointer not allocated");
            let term = g
                .get_allocated_ptr_from_ptr(&s.cont_terminal(), s)
                .expect("terminal pointer not allocated");
            Ok(vec![nil, env.clone(), term])
        }
    }

    impl<F: LurkField> Coprocessor<F> for Terminator<F> {
        fn eval_arity(&self) -> usize {
            0
        }

        fn evaluate(
            &self,
            s: &Store<F>,
            _args: &[Ptr<F>],
            env: &Ptr<F>,
            _cont: &Ptr<F>,
        ) -> Vec<Ptr<F>> {
            vec![s.intern_nil(), *env, s.cont_terminal()]
        }

        fn evaluate_simple(&self, _s: &Store<F>, _args: &[Ptr<F>]) -> Ptr<F> {
            unreachable!()
        }

        fn has_circuit(&self) -> bool {
            true
        }
    }

    impl<F: LurkField> Terminator<F> {
        pub(crate) fn new() -> Self {
            Self {
                _p: Default::default(),
            }
        }
    }
}
