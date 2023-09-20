use std::fmt::Debug;

use bellpepper::gadgets::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};

use crate::circuit::circuit_frame::{car_cdr, destructure_list};
use crate::circuit::gadgets::constraints::{alloc_equal_const, enforce_equal_const};
use crate::circuit::gadgets::data::GlobalAllocations;
use crate::circuit::gadgets::pointer::{AllocatedContPtr, AllocatedPtr, AsAllocatedHashComponents};
use crate::eval::IO;
use crate::field::LurkField;
use crate::ptr::{ContPtr, Ptr};
use crate::store::Store;
use crate::tag::Tag;
use crate::z_data::z_ptr::ZExprPtr;

pub mod circom;
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

    fn synthesize_step_circuit<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &Store<F>,
        g: &GlobalAllocations<F>,
        coprocessor_zptr: &ZExprPtr<F>,
        input_expr: &AllocatedPtr<F>,
        input_env: &AllocatedPtr<F>,
        input_cont: &AllocatedContPtr<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        // TODO: This code is almost identical to that in circuit_frame.rs (the arg destructuring is factored out and shared there).
        // Refactor to share.
        let arity = self.arity();

        // If `input_expr` is not a cons, the circuit will not be satisified, per `car_cdr`'s contract.
        // That is also the desired behavior for the coprocessor circuit's validation, so this is fine.
        let (head, rest) = car_cdr(
            &mut cs.namespace(|| "coprocessor_input car_cdr"),
            g,
            input_expr,
            store,
            &Boolean::Constant(true),
        )?;

        {
            // The NIVC coprocessor contract requires that a proof (of any kind, including error) will be generated only if
            // the control expression can be correctly handled by the coprocessor. This means each circuit must validate its
            // input to ensure it matches the coprocessor.
            enforce_equal_const(
                cs,
                || "coprocessor head tag matches",
                coprocessor_zptr.tag().to_field(),
                head.tag(),
            );
            enforce_equal_const(
                cs,
                || "coprocessor head val matches",
                *coprocessor_zptr.value(),
                head.hash(),
            );
        }

        let (inputs, actual_length) = destructure_list(
            &mut cs.namespace(|| "coprocessor form"),
            store,
            g,
            arity,
            &rest,
        )?;

        let arity_is_correct = alloc_equal_const(
            &mut cs.namespace(|| "arity_is_correct"),
            &actual_length,
            F::from(arity as u64),
        )?;

        let (result_expr, result_env, result_cont) =
            self.synthesize(cs, g, store, &inputs, input_env, input_cont)?;

        let quoted_expr = AllocatedPtr::construct_list(
            &mut cs.namespace(|| "quote coprocessor result"),
            g,
            store,
            &[&g.quote_ptr, &result_expr],
        )?;

        let default_num_pair = &[&g.default_num, &g.default_num];

        // TODO: This should be better abstracted, perhaps by resurrecting historical code.
        let tail_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
            &result_env,
            &result_cont,
            default_num_pair,
            default_num_pair,
        ];

        let tail_cont = AllocatedContPtr::construct(
            &mut cs.namespace(|| "coprocessor tail cont"),
            store,
            &g.tail_cont_tag,
            tail_components,
        )?;

        let new_expr = pick_ptr!(cs, &arity_is_correct, &quoted_expr, &rest)?;
        let new_env = pick_ptr!(cs, &arity_is_correct, &result_env, &input_env)?;
        let new_cont = pick_cont_ptr!(cs, &arity_is_correct, &tail_cont, &g.error_ptr_cont)?;

        Ok((new_expr, new_env, new_cont))
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
