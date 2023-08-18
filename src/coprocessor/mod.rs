use std::fmt::Debug;

use bellpepper_core::{ConstraintSystem, SynthesisError};

use crate::circuit::gadgets::data::GlobalAllocations;
use crate::circuit::gadgets::pointer::{AllocatedContPtr, AllocatedPtr};
use crate::eval::IO;
use crate::field::LurkField;
use crate::ptr::{ContPtr, Ptr};
use crate::store::Store;

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

    fn evaluate(&self, s: &mut Store<F>, args: Ptr<F>, env: Ptr<F>, cont: ContPtr<F>) -> IO<F> {
        let Some(argv) = s.fetch_list(&args) else {
            return IO {
                expr: args,
                env,
                cont: s.intern_cont_error(),
            };
        };

        if argv.len() != self.eval_arity() {
            return IO {
                expr: args,
                env,
                cont: s.intern_cont_error(),
            };
        };

        let result = self.simple_evaluate(s, &argv);

        IO {
            expr: result,
            env,
            cont,
        }
    }

    /// As with all evaluation, the value returned from `simple_evaluate` must be fully evaluated.
    fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F>;

    /// Returns true if this Coprocessor actually implements a circuit.
    fn has_circuit(&self) -> bool {
        false
    }
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

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        _cs: &mut CS,
        _g: &GlobalAllocations<F>,
        _store: &Store<F>,
        _input_exprs: &[AllocatedPtr<F>],
        _input_env: &AllocatedPtr<F>,
        _input_cont: &AllocatedContPtr<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        // A `synthesize` implementation needs to be provided by implementers of `CoCircuit`.
        unimplemented!()
    }
}

#[cfg(test)]
pub(crate) mod test {
    use serde::{Deserialize, Serialize};

    use super::*;
    use crate::circuit::gadgets::constraints::{add, mul};
    use crate::tag::{ExprTag, Tag};
    use std::marker::PhantomData;

    /// A dumb Coprocessor for testing.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub(crate) struct DumbCoprocessor<F: LurkField> {
        pub(crate) _p: PhantomData<F>,
    }

    impl<F: LurkField> CoCircuit<F> for DumbCoprocessor<F> {
        fn arity(&self) -> usize {
            2
        }

        fn synthesize<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            _g: &GlobalAllocations<F>,
            _store: &Store<F>,
            input_exprs: &[AllocatedPtr<F>],
            input_env: &AllocatedPtr<F>,
            input_cont: &AllocatedContPtr<F>,
        ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError>
        {
            let a = input_exprs[0].clone();
            let b = &input_exprs[1];

            // FIXME: Check tags.

            // a^2 + b = c
            let a2 = mul(&mut cs.namespace(|| "square"), a.hash(), a.hash())?;
            let c = add(&mut cs.namespace(|| "add"), &a2, b.hash())?;
            let c_ptr = AllocatedPtr::alloc_tag(cs, ExprTag::Num.to_field(), c)?;

            Ok((c_ptr, input_env.clone(), input_cont.clone()))
        }
    }

    impl<F: LurkField> Coprocessor<F> for DumbCoprocessor<F> {
        /// Dumb Coprocessor takes two arguments.
        fn eval_arity(&self) -> usize {
            2
        }

        /// It squares the first arg and adds it to the second.
        fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
            let a = args[0];
            let b = args[1];

            let a_num = s.fetch_num(&a).unwrap();
            let b_num = s.fetch_num(&b).unwrap();
            let mut result = *a_num;
            result *= *a_num;
            result += *b_num;

            s.intern_num(result)
        }

        fn has_circuit(&self) -> bool {
            true
        }
    }

    impl<F: LurkField> DumbCoprocessor<F> {
        pub(crate) fn new() -> Self {
            Self {
                _p: Default::default(),
            }
        }
    }
}
