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
/// - An enum such as [`crate::lang::Coproc`], which "closes" the hierarchy of possible coprocessor
///   implementations we want to instantiate at a particular point in the code.
pub trait Coprocessor<F: LurkField>: Clone + Debug + Sync + Send + CoCircuit<F> {
    /// Returns true if this Coprocessor actually implements a circuit.
    fn has_circuit(&self) -> bool {
        false
    }

    /// Function for internal plumbing. Reimplementing is not recommended
    fn evaluate_internal(&self, s: &Store<F>, ptrs: &[Ptr]) -> Vec<Ptr> {
        let arity = self.arity();
        let args = &ptrs[0..arity];
        let env = &ptrs[arity];
        let cont = &ptrs[arity + 1];
        self.evaluate(s, args, env, cont)
    }

    fn evaluate(&self, s: &Store<F>, args: &[Ptr], env: &Ptr, cont: &Ptr) -> Vec<Ptr> {
        vec![self.evaluate_simple(s, args), *env, *cont]
    }

    fn evaluate_simple(&self, _s: &Store<F>, _args: &[Ptr]) -> Ptr;
}

/// `CoCircuit` is a trait that represents a generalized interface for coprocessors.
/// Coprocessors augment the Lurk circuit and evaluation with additional built-in functionality.
/// This trait generalizes over functionality needed in the circuit, the sibling `Coprocessor` trait,
/// generalizes over functionality needed in the evaluator.
///
/// The trait is implemented by concrete coprocessor types, such as `DumbCoprocessor`.
pub trait CoCircuit<F: LurkField>: Send + Sync + Clone {
    fn arity(&self) -> usize;

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

    /// Perform global allocations needed for synthesis
    fn alloc_globals<CS: ConstraintSystem<F>>(
        &self,
        _cs: &mut CS,
        _g: &GlobalAllocator<F>,
        _s: &Store<F>,
    ) {
    }
}

#[cfg(test)]
pub(crate) mod test {
    use bellpepper_core::num::AllocatedNum;
    use serde::{Deserialize, Serialize};

    use self::gadgets::construct_cons;

    use super::*;
    use crate::circuit::gadgets::constraints::{alloc_equal, mul};
    use crate::lem::{pointers::RawPtr, tag::Tag as LEMTag};
    use crate::tag::{ExprTag, Tag};
    use std::marker::PhantomData;

    /// A dumb Coprocessor for testing.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub(crate) struct DumbCoprocessor<F> {
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

            let a_is_num = alloc_equal(ns!(cs, "fst is num"), a.tag(), num_tag)?;
            let b_is_num = alloc_equal(ns!(cs, "snd is num"), b.tag(), num_tag)?;
            let types_are_correct =
                Boolean::and(ns!(cs, "types are correct"), &a_is_num, &b_is_num)?;

            // a^2 + b = c
            let a2 = mul(ns!(cs, "square"), a.hash(), a.hash())?;
            let c = a2.add(ns!(cs, "add"), b.hash())?;
            let c_ptr = AllocatedPtr::alloc_tag(cs, ExprTag::Num.to_field(), c)?;

            let result_expr0 = AllocatedPtr::pick(ns!(cs, "result_expr0"), &b_is_num, &c_ptr, b)?;

            // If `a` is not a `Num`, then that error takes precedence, and we return `a`. Otherwise, return either the
            // correct result or `b`, depending on whether `b` is a `Num` or not.
            let result_expr =
                AllocatedPtr::pick(ns!(cs, "result_expr"), &a_is_num, &result_expr0, a)?;

            let result_cont = AllocatedPtr::pick(
                ns!(cs, "result_cont"),
                &types_are_correct,
                input_cont,
                cont_error,
            )?;

            Ok((result_expr, input_env.clone(), result_cont))
        }
    }

    impl<F: LurkField> CoCircuit<F> for DumbCoprocessor<F> {
        /// Dumb Coprocessor takes two arguments.
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
            let num_tag = g.alloc_tag(cs, &ExprTag::Num);

            let cont_err = g.alloc_ptr(cs, &s.cont_error(), s);

            let (expr, env, cont) =
                self.synthesize_aux(cs, input_exprs, input_env, input_cont, num_tag, &cont_err)?;

            Ok(vec![expr, env, cont])
        }

        fn alloc_globals<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            g: &GlobalAllocator<F>,
            s: &Store<F>,
        ) {
            g.alloc_tag(cs, &ExprTag::Num);
            g.alloc_ptr(cs, &s.cont_error(), s);
        }
    }

    impl<F: LurkField> Coprocessor<F> for DumbCoprocessor<F> {
        fn has_circuit(&self) -> bool {
            true
        }

        fn evaluate(&self, s: &Store<F>, args: &[Ptr], env: &Ptr, cont: &Ptr) -> Vec<Ptr> {
            let (LEMTag::Expr(ExprTag::Num), RawPtr::Atom(a)) = args[0].parts() else {
                return vec![args[0], *env, s.cont_error()];
            };
            let a = s.expect_f(*a);
            let (LEMTag::Expr(ExprTag::Num), RawPtr::Atom(b)) = args[1].parts() else {
                return vec![args[1], *env, s.cont_error()];
            };
            let b = s.expect_f(*b);
            vec![s.num((*a * *a) + *b), *env, *cont]
        }

        fn evaluate_simple(&self, _s: &Store<F>, _args: &[Ptr]) -> Ptr {
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
    pub(crate) struct Terminator<F> {
        _p: PhantomData<F>,
    }

    impl<F: LurkField> CoCircuit<F> for Terminator<F> {
        fn arity(&self) -> usize {
            0
        }

        fn synthesize<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            g: &GlobalAllocator<F>,
            s: &Store<F>,
            _not_dummy: &Boolean,
            _args: &[AllocatedPtr<F>],
            env: &AllocatedPtr<F>,
            _cont: &AllocatedPtr<F>,
        ) -> Result<Vec<AllocatedPtr<F>>, SynthesisError> {
            let nil = g.alloc_ptr(cs, &s.intern_nil(), s);
            let term = g.alloc_ptr(cs, &s.cont_terminal(), s);
            Ok(vec![nil, env.clone(), term])
        }

        fn alloc_globals<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            g: &GlobalAllocator<F>,
            s: &Store<F>,
        ) {
            g.alloc_ptr(cs, &s.intern_nil(), s);
            g.alloc_ptr(cs, &s.cont_terminal(), s);
        }
    }

    impl<F: LurkField> Coprocessor<F> for Terminator<F> {
        fn evaluate(&self, s: &Store<F>, _args: &[Ptr], env: &Ptr, _cont: &Ptr) -> Vec<Ptr> {
            vec![s.intern_nil(), *env, s.cont_terminal()]
        }

        fn evaluate_simple(&self, _s: &Store<F>, _args: &[Ptr]) -> Ptr {
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

    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub(crate) struct HelloWorld<F> {
        _p: PhantomData<F>,
    }

    impl<F: LurkField> HelloWorld<F> {
        pub(crate) fn new() -> Self {
            Self {
                _p: Default::default(),
            }
        }

        #[inline]
        pub(crate) fn intern_hello_world(s: &Store<F>) -> Ptr {
            s.intern_string("Hello, world!")
        }
    }

    impl<F: LurkField> CoCircuit<F> for HelloWorld<F> {
        fn arity(&self) -> usize {
            0
        }

        fn synthesize_simple<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            g: &GlobalAllocator<F>,
            s: &Store<F>,
            _not_dummy: &Boolean,
            _args: &[AllocatedPtr<F>],
        ) -> Result<AllocatedPtr<F>, SynthesisError> {
            Ok(g.alloc_ptr(cs, &Self::intern_hello_world(s), s))
        }

        fn alloc_globals<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            g: &GlobalAllocator<F>,
            s: &Store<F>,
        ) {
            g.alloc_ptr(cs, &Self::intern_hello_world(s), s);
        }
    }

    impl<F: LurkField> Coprocessor<F> for HelloWorld<F> {
        fn has_circuit(&self) -> bool {
            true
        }

        fn evaluate_simple(&self, s: &Store<F>, _args: &[Ptr]) -> Ptr {
            Self::intern_hello_world(s)
        }
    }

    /// A coprocessor that simply returns the pair (nil . nil)
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub(crate) struct NilNil<F> {
        _p: PhantomData<F>,
    }

    impl<F: LurkField> NilNil<F> {
        pub(crate) fn new() -> Self {
            Self {
                _p: Default::default(),
            }
        }
    }

    impl<F: LurkField> CoCircuit<F> for NilNil<F> {
        fn arity(&self) -> usize {
            0
        }

        fn synthesize_simple<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            g: &GlobalAllocator<F>,
            s: &Store<F>,
            _not_dummy: &Boolean,
            _args: &[AllocatedPtr<F>],
        ) -> Result<AllocatedPtr<F>, SynthesisError> {
            let nil = g.alloc_ptr(cs, &s.intern_nil(), s);
            construct_cons(cs, g, s, &nil, &nil)
        }

        fn alloc_globals<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            g: &GlobalAllocator<F>,
            s: &Store<F>,
        ) {
            g.alloc_ptr(cs, &s.intern_nil(), s);
            g.alloc_tag(cs, &ExprTag::Cons);
        }
    }

    impl<F: LurkField> Coprocessor<F> for NilNil<F> {
        fn has_circuit(&self) -> bool {
            true
        }

        fn evaluate_simple(&self, s: &Store<F>, _args: &[Ptr]) -> Ptr {
            let nil = s.intern_nil();
            s.cons(nil, nil)
        }
    }
}
