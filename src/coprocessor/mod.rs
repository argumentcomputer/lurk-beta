use std::fmt::Debug;

use bellpepper::gadgets::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};

use crate::circuit::circuit_frame::{car_cdr, destructure_list};
use crate::circuit::gadgets::constraints::{alloc_equal_const, enforce_equal_const};
use crate::circuit::gadgets::data::GlobalAllocations;
use crate::circuit::gadgets::pointer::{AllocatedContPtr, AllocatedPtr};
use crate::eval::IO;
use crate::field::LurkField;
use crate::lem::{circuit::GlobalAllocator, pointers::Ptr as LEMPtr, store::Store as LEMStore};
use crate::ptr::{ContPtr, Ptr};
use crate::store::Store;
use crate::tag::Tag;
use crate::z_data::z_ptr::ZExprPtr;

pub mod circom;
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

    fn evaluate(&self, s: &Store<F>, args: Ptr<F>, env: Ptr<F>, cont: ContPtr<F>) -> IO<F> {
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
    fn simple_evaluate(&self, s: &Store<F>, args: &[Ptr<F>]) -> Ptr<F>;

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
        dummy_or_blank: bool,
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
            self.synthesize(cs, g, store, &inputs, input_env, input_cont, dummy_or_blank)?;

        let quoted_expr = AllocatedPtr::construct_list(
            &mut cs.namespace(|| "quote coprocessor result"),
            g,
            store,
            &[&g.quote_ptr, &result_expr],
        )?;

        // FIXME: technically, the error is defined to be rest -- which is the cdr of input_expr.tes
        //let new_expr = pick_ptr!(cs, &arity_is_correct, &quoted_expr, &rest)?;
        let new_expr = pick_ptr!(cs, &arity_is_correct, &quoted_expr, &input_expr)?;

        let new_env = pick_ptr!(cs, &arity_is_correct, &result_env, &input_env)?;
        let new_cont = pick_cont_ptr!(cs, &arity_is_correct, &result_cont, &g.error_ptr_cont)?;

        Ok((new_expr, new_env, new_cont))
    }

    fn evaluate_lem_internal(&self, s: &LEMStore<F>, ptrs: &[LEMPtr<F>]) -> Vec<LEMPtr<F>> {
        let arity = self.arity();
        let args = &ptrs[0..arity];
        let env = &ptrs[arity];
        let cont = &ptrs[arity + 1];
        self.evaluate_lem(s, args, env, cont)
    }

    fn evaluate_lem(
        &self,
        s: &LEMStore<F>,
        args: &[LEMPtr<F>],
        env: &LEMPtr<F>,
        cont: &LEMPtr<F>,
    ) -> Vec<LEMPtr<F>> {
        vec![self.evaluate_lem_simple(s, args), *env, *cont]
    }

    // TODO: this default implementation should disappear once we make the switch to LEM
    fn evaluate_lem_simple(&self, _s: &LEMStore<F>, _args: &[LEMPtr<F>]) -> LEMPtr<F> {
        unimplemented!()
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
        _dummy_or_blank: bool,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        // A `synthesize` implementation needs to be provided by implementers of `CoCircuit`.
        unimplemented!()
    }

    fn synthesize_lem_internal<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        s: &LEMStore<F>,
        not_dummy: &Boolean,
        ptrs: &[AllocatedPtr<F>],
    ) -> Result<Vec<AllocatedPtr<F>>, SynthesisError> {
        let arity = self.arity();
        let args = &ptrs[0..arity];
        let env = &ptrs[arity];
        let cont = &ptrs[arity + 1];
        self.synthesize_lem(cs, g, s, not_dummy, args, env, cont)
    }

    fn synthesize_lem<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocator<F>,
        s: &LEMStore<F>,
        not_dummy: &Boolean,
        args: &[AllocatedPtr<F>],
        env: &AllocatedPtr<F>,
        cont: &AllocatedPtr<F>,
    ) -> Result<Vec<AllocatedPtr<F>>, SynthesisError> {
        Ok(vec![
            self.synthesize_lem_simple(cs, g, s, not_dummy, args)?,
            env.clone(),
            cont.clone(),
        ])
    }

    fn synthesize_lem_simple<CS: ConstraintSystem<F>>(
        &self,
        _cs: &mut CS,
        _g: &GlobalAllocator<F>,
        _s: &LEMStore<F>,
        _not_dummy: &Boolean,
        _args: &[AllocatedPtr<F>],
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        unimplemented!()
    }
}

#[cfg(test)]
pub(crate) mod test {
    use serde::{Deserialize, Serialize};

    use super::*;
    use crate::circuit::gadgets::constraints::{add, implies_equal, mul};
    use crate::lem::Tag as LEMTag;
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
            _dummy_or_blank: bool,
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

        fn synthesize_lem_simple<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            g: &GlobalAllocator<F>,
            _s: &LEMStore<F>,
            not_dummy: &Boolean,
            args: &[AllocatedPtr<F>],
        ) -> Result<AllocatedPtr<F>, SynthesisError> {
            use crate::lem::Tag::Expr;
            let a = &args[0];
            let b = &args[1];

            let allocated_num_tag = g
                .get_allocated_const(Expr(ExprTag::Num).to_field())
                .expect("Num tag should have been allocated");
            implies_equal(
                &mut cs.namespace(|| "first arg tag"),
                not_dummy,
                a.tag(),
                allocated_num_tag,
            );
            implies_equal(
                &mut cs.namespace(|| "second arg tag"),
                not_dummy,
                b.tag(),
                allocated_num_tag,
            );

            // a^2 + b = c
            let a2 = mul(&mut cs.namespace(|| "square"), a.hash(), a.hash())?;
            let c = add(&mut cs.namespace(|| "add"), &a2, b.hash())?;
            AllocatedPtr::alloc_tag(cs, ExprTag::Num.to_field(), c)
        }
    }

    impl<F: LurkField> Coprocessor<F> for DumbCoprocessor<F> {
        /// Dumb Coprocessor takes two arguments.
        fn eval_arity(&self) -> usize {
            2
        }

        /// It squares the first arg and adds it to the second.
        fn simple_evaluate(&self, s: &Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
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

        fn evaluate_lem_simple(&self, _s: &LEMStore<F>, args: &[LEMPtr<F>]) -> LEMPtr<F> {
            match (&args[0], &args[1]) {
                (
                    LEMPtr::Atom(LEMTag::Expr(ExprTag::Num), a),
                    LEMPtr::Atom(LEMTag::Expr(ExprTag::Num), b),
                ) => LEMPtr::Atom(LEMTag::Expr(ExprTag::Num), (*a * *a) + *b),
                _ => panic!("Invalid input"),
            }
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
