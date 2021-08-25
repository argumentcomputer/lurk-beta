use bellperson::{
    bls::{Bls12, Engine, Fr},
    gadgets::{
        boolean::{AllocatedBit, Boolean},
        num::AllocatedNum,
    },
    groth16::{self, verify_proof},
    Circuit, ConstraintSystem, SynthesisError,
};
use ff::{Field, ScalarEngine};
use neptune::circuit::poseidon_hash;

use crate::constraints::{self, equal};
use crate::data::{fr_from_u64, BaseContinuationTag, Continuation, Expression, Store, Tag, Tagged};
use crate::eval::{empty_sym_env, Frame, Witness, IO};

pub trait Provable {
    fn public_inputs(&self) -> Vec<Fr>;
}

pub struct Proof<F: Provable> {
    _frame: F,
    groth16_proof: groth16::Proof<Bls12>,
}

impl<W> Provable for Frame<IO, W> {
    fn public_inputs(&self) -> Vec<Fr> {
        let mut inputs = Vec::with_capacity(10);

        inputs.extend(self.input.public_inputs());
        inputs.extend(self.output.public_inputs());
        inputs.extend(self.initial.public_inputs());
        inputs.push(fr_from_u64(self.i as u64));

        inputs
    }
}

impl IO {
    fn public_inputs(&self) -> Vec<Fr> {
        vec![
            self.expr.tag_fr(),
            self.expr.get_hash(),
            self.env.tag_fr(),
            self.env.get_hash(),
            self.cont.get_continuation_tag().cont_tag_fr(),
            self.cont.get_hash(),
        ]
    }
}

pub fn verify<F: Provable>(p: Proof<F>, f: F) -> Result<bool, SynthesisError> {
    let inputs = f.public_inputs();
    let vk = todo!();

    verify_proof(vk, &p.groth16_proof, &inputs)
}

fn bind_input<CS: ConstraintSystem<Bls12>>(
    cs: &mut CS,
    expr: &Expression,
) -> Result<(AllocatedNum<Bls12>, AllocatedNum<Bls12>), SynthesisError> {
    let tagged_hash = expr.tagged_hash();
    let tag = AllocatedNum::alloc(cs.namespace(|| "tag"), || Ok(tagged_hash.tag))?;
    tag.inputize(cs.namespace(|| "tag input"));

    let hash = AllocatedNum::alloc(cs.namespace(|| "hash"), || Ok(tagged_hash.hash))?;
    hash.inputize(cs.namespace(|| "hash input"));

    Ok((tag, hash))
}

fn bind_input_cont<CS: ConstraintSystem<Bls12>>(
    cs: &mut CS,
    cont: &Continuation,
) -> Result<(AllocatedNum<Bls12>, AllocatedNum<Bls12>), SynthesisError> {
    let tag = AllocatedNum::alloc(cs.namespace(|| "continuation tag"), || {
        Ok(cont.get_continuation_tag().cont_tag_fr())
    })?;
    tag.inputize(cs.namespace(|| "continuation tag input"));

    let hash = AllocatedNum::alloc(cs.namespace(|| "continuation hash"), || Ok(cont.get_hash()))?;
    hash.inputize(cs.namespace(|| "continuation hash input"));

    Ok((tag, hash))
}

macro_rules! if_then {
    ($cs:ident, $a:expr, $b:expr) => {
        enforce_implication(
            $cs.namespace(|| format!("if {} then {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        );
    };
}

macro_rules! equal {
    ($cs:ident, $a:expr, $b:expr) => {
        alloc_equal(
            $cs.namespace(|| format!("{} equals {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        );
    };
}

macro_rules! and {
    ($cs:ident, $a:expr, $b:expr) => {
        Boolean::and(
            $cs.namespace(|| format!("{} and {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        );
    };
}

macro_rules! or {
    ($cs:ident, $a:expr, $b:expr) => {
        or(
            $cs.namespace(|| format!("{} or {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        );
    };
}

macro_rules! allocate_tag {
    ($cs:ident, $tag:expr) => {
        AllocatedNum::alloc(
            $cs.namespace(|| format!("{} tag", stringify!($tag))),
            || Ok($tag.fr()),
        )
    };
}

macro_rules! allocate_continuation_tag {
    ($cs:ident, $continuation_tag:expr) => {
        AllocatedNum::alloc(
            $cs.namespace(|| format!("{} continuation tag", stringify!($continuation_tag))),
            || Ok($continuation_tag.cont_tag_fr()),
        )
    };
}

impl Circuit<Bls12> for Frame<IO, Witness> {
    fn synthesize<CS: ConstraintSystem<Bls12>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let witness = self.witness.clone();

        ////////////////////////////////////////////////////////////////////////////////
        // Bind public inputs.
        //
        // THe frame's input:
        let (input_tag, input_hash) =
            bind_input(&mut cs.namespace(|| "input expression"), &self.input.expr)?;

        let (input_env_tag, input_env_hash) =
            bind_input(&mut cs.namespace(|| "input env"), &self.input.env)?;

        let (input_cont_tag, input_cont_hash) =
            bind_input_cont(&mut cs.namespace(|| "input cont"), &self.input.cont)?;

        // The frame's output:
        let (output_tag, output_hash) =
            bind_input(&mut cs.namespace(|| "output expression"), &self.output.expr)?;

        let (output_env_tag, output_env_hash) =
            bind_input(&mut cs.namespace(|| "output env"), &self.output.env)?;

        let (output_cont_tag, output_cont_hash) =
            bind_input_cont(&mut cs.namespace(|| "output cont"), &self.output.cont)?;

        // The initial input to the IVC computation.
        let (initial_tag, initial_hash) = bind_input(
            &mut cs.namespace(|| "initial expression"),
            &self.initial.expr,
        )?;

        let (initial_env_tag, initial_env_hash) =
            bind_input(&mut cs.namespace(|| "initial env"), &self.initial.env)?;

        let (initial_cont_tag, initial_cont_hash) =
            bind_input_cont(&mut cs.namespace(|| "initial cont"), &self.initial.cont)?;

        // We don't currently need this, but we could expose access to it for logging, etc.
        // The frame counter:
        let frame_counter = cs.alloc_input(|| "frame counter", || Ok(fr_from_u64(self.i as u64)));
        //
        // End public inputs.
        ////////////////////////////////////////////////////////////////////////////////

        ////////////////////////////////////////////////////////////////////////////////
        // Tag allocations
        //
        // Optimization: We don't need to allocate the tags, but avoiding it requires a version
        // of `alloc_equal` that takes a constant. TODO

        let nil_tag = allocate_tag!(cs, Tag::Nil)?;
        let cons_tag = allocate_tag!(cs, Tag::Cons)?;
        let sym_tag = allocate_tag!(cs, Tag::Sym)?;
        let fun_tag = allocate_tag!(cs, Tag::Fun)?;
        let num_tag = allocate_tag!(cs, Tag::Num)?;
        let thunk_tag = allocate_tag!(cs, Tag::Thunk)?;

        ////////////////////////////////////////////////////////////////////////////////
        // Input type
        let input_is_nil = equal!(cs, &input_tag, &nil_tag)?;
        let input_is_cons = equal!(cs, &input_tag, &cons_tag)?;
        let input_is_sym = equal!(cs, &input_tag, &sym_tag)?;
        let input_is_fun = equal!(cs, &input_tag, &fun_tag)?;
        let input_is_num = equal!(cs, &input_tag, &num_tag)?;
        let input_is_thunk = equal!(cs, &input_tag, &thunk_tag)?;

        ////////////////////////////////////////////////////////////////////////////////
        // Output type
        let output_is_nil = equal!(cs, &output_tag, &nil_tag)?;
        let output_is_cons = equal!(cs, &output_tag, &cons_tag)?;
        let output_is_sym = equal!(cs, &output_tag, &sym_tag)?;
        let output_is_fun = equal!(cs, &output_tag, &fun_tag)?;
        let output_is_num = equal!(cs, &output_tag, &num_tag)?;
        let output_is_thunk = equal!(cs, &output_tag, &thunk_tag)?;

        ////////////////////////////////////////////////////////////////////////////////
        // Tag allocations (TODO: make these unnecesssary.)
        let outermost_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::Outermost)?;
        let simple_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::Simple)?;
        let call_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::Call)?;
        let call2_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::Call2)?;
        let tail_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::Tail)?;
        let error_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::Error)?;
        let lookup_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::Lookup)?;
        let binop_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::Binop)?;
        let binop2_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::Binop2)?;
        let relop_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::Relop)?;
        let relop2_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::Relop2)?;
        let if_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::If)?;
        let let_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::LetStar)?;
        let let_rec_star_cont_tag =
            allocate_continuation_tag!(cs, BaseContinuationTag::LetRecStar)?;
        let dummy_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::Dummy)?;
        let terminal_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::Terminal)?;

        ////////////////////////////////////////////////////////////////////////////////
        // Input Continuation type
        let input_cont_is_outermost = equal!(cs, &input_cont_tag, &outermost_cont_tag)?;
        let input_cont_is_simple = equal!(cs, &input_cont_tag, &simple_cont_tag)?;
        let input_cont_is_call = equal!(cs, &input_cont_tag, &call_cont_tag)?;
        let input_cont_is_call2 = equal!(cs, &input_cont_tag, &call2_cont_tag)?;
        let input_cont_is_tail = equal!(cs, &input_cont_tag, &tail_cont_tag)?;
        let input_cont_is_error = equal!(cs, &input_cont_tag, &error_cont_tag)?;
        let input_cont_is_lookup = equal!(cs, &input_cont_tag, &lookup_cont_tag)?;
        let input_cont_is_binop = equal!(cs, &input_cont_tag, &binop_cont_tag)?;
        let input_cont_is_binop2 = equal!(cs, &input_cont_tag, &binop2_cont_tag)?;
        let input_cont_is_relop = equal!(cs, &input_cont_tag, &relop_cont_tag)?;
        let input_cont_is_relop2 = equal!(cs, &input_cont_tag, &relop2_cont_tag)?;
        let input_cont_is_if = equal!(cs, &input_cont_tag, &if_cont_tag)?;
        let input_cont_is_let = equal!(cs, &input_cont_tag, &let_cont_tag)?;
        let input_cont_is_let_rec_star = equal!(cs, &input_cont_tag, &let_rec_star_cont_tag)?;
        let input_cont_is_dummy = equal!(cs, &input_cont_tag, &dummy_cont_tag)?;
        let input_cont_is_terminal = equal!(cs, &input_cont_tag, &terminal_cont_tag)?;

        ////////////////////////////////////////////////////////////////////////////////
        // Output Continuation type
        let output_cont_is_outermost = equal!(cs, &output_cont_tag, &outermost_cont_tag)?;
        let output_cont_is_simple = equal!(cs, &output_cont_tag, &simple_cont_tag)?;
        let output_cont_is_call = equal!(cs, &output_cont_tag, &call_cont_tag)?;
        let output_cont_is_call2 = equal!(cs, &output_cont_tag, &call2_cont_tag)?;
        let output_cont_is_tail = equal!(cs, &output_cont_tag, &tail_cont_tag)?;
        let output_cont_is_error = equal!(cs, &output_cont_tag, &error_cont_tag)?;
        let output_cont_is_lookup = equal!(cs, &output_cont_tag, &lookup_cont_tag)?;
        let output_cont_is_binop = equal!(cs, &output_cont_tag, &binop_cont_tag)?;
        let output_cont_is_binop2 = equal!(cs, &output_cont_tag, &binop2_cont_tag)?;
        let output_cont_is_relop = equal!(cs, &output_cont_tag, &relop_cont_tag)?;
        let output_cont_is_relop2 = equal!(cs, &output_cont_tag, &relop2_cont_tag)?;
        let output_cont_is_if = equal!(cs, &output_cont_tag, &if_cont_tag)?;
        let output_cont_is_let = equal!(cs, &output_cont_tag, &let_cont_tag)?;
        let output_cont_is_let_rec_star = equal!(cs, &output_cont_tag, &let_rec_star_cont_tag)?;
        let output_cont_is_dummy = equal!(cs, &output_cont_tag, &dummy_cont_tag)?;
        let output_cont_is_terminal = equal!(cs, &output_cont_tag, &terminal_cont_tag)?;

        ////////////////////////////////////////////////////////////////////////////////
        // Self-evaluating inputs
        //
        let input_is_self_evaluating = {
            // Set boolean flags based on input type tags.

            // TODO: This allocation is also unneeded when we have `alloc_const_equal` (or whatever we call it).
            let t_hash = AllocatedNum::alloc(cs.namespace(|| "sym hash"), || {
                Ok(Expression::Sym("T".to_string()).get_hash())
            })?;

            let input_hash_matches_sym_t = equal!(cs, &input_hash, &t_hash)?;
            let input_is_t = and!(cs, &input_is_sym, &input_hash_matches_sym_t)?;
            let input_is_self_evaluating_sym = or!(cs, &input_is_nil, &input_is_t)?;
            let input_is_num_or_fun = or!(cs, &input_is_num, &input_is_fun)?;

            or!(cs, &input_is_num_or_fun, &input_is_self_evaluating_sym)?
        };

        let input_output_equal = {
            // Allocates a bit which is true if input and output expressions are identical.

            let tags_equal = equal!(cs, &input_tag, &output_tag)?;
            let hashes_equal = equal!(cs, &input_hash, &output_hash)?;

            Boolean::and(
                cs.namespace(|| "input and output are equal"),
                &tags_equal,
                &hashes_equal,
            )?
        };

        {
            // If make_thunk was called.

            let cont_is_terminal_and_input_output_equal = Boolean::and(
                cs.namespace(|| "cont_is_terminal and input_output_equal"),
                &output_cont_is_terminal, // FIXME: Only if input cont is Outermost
                &input_output_equal,
            )?;

            if_then!(
                cs,
                &input_is_self_evaluating,
                &cont_is_terminal_and_input_output_equal
            )?;
        }

        //
        // End Self-evaluating inputs
        ////////////////////////////////////////////////////////////////////////////////

        ////////////////////////////////////////////////////////////////////////////////
        // make_thunk
        //

        // True if make_thunk was called when evaluating (according to the prover's witness).
        let make_thunk_was_called = Boolean::Is(AllocatedBit::alloc(
            cs.namespace(|| "make_thunk_called"),
            Some(witness.make_thunk_was_called),
        )?);

        if_then!(cs, &output_is_thunk, &make_thunk_was_called)?;
        if_then!(cs, &make_thunk_was_called, &output_is_thunk)?;

        let (cont_hash, cont_tag) = if let Some(cont) = witness.make_thunk_cont {
            let cont_hash = cont.get_hash();
            let cont_tag = AllocatedNum::alloc(cs.namespace(|| "make_thunk_cont tag"), || {
                Ok(cont.get_continuation_tag().cont_tag_fr())
            });

            // let h = poseidon_hash(cs.namespace(|| "contxxxx"), vec![cont_tag, ]);
            todo!();
            //(hash, tag)
        } else {
            (Fr::zero(), Fr::zero())
        };

        //
        ////////////////////////////////////////////////////////////////////////////////

        Ok(())
    }
}

fn enforce_implication<CS: ConstraintSystem<E>, E: Engine>(
    mut cs: CS,
    a: &Boolean,
    b: &Boolean,
) -> Result<(), SynthesisError> {
    let implication = implies(cs.namespace(|| "construct implication"), a, b)?;
    enforce_true(cs.namespace(|| "enforce implication"), &implication);
    Ok(())
}

fn enforce_true<CS: ConstraintSystem<E>, E: Engine>(mut cs: CS, prop: &Boolean) {
    Boolean::enforce_equal(cs, &Boolean::Constant(true), &prop).unwrap(); // FIXME: unwrap
}

// a => b
// not (a and (not b))
fn implies<CS: ConstraintSystem<E>, E: Engine>(
    cs: CS,
    a: &Boolean,
    b: &Boolean,
) -> Result<Boolean, SynthesisError> {
    Ok(Boolean::and(cs, a, &b.not())?.not())
}

fn or<CS: ConstraintSystem<E>, E: Engine>(
    mut cs: CS,
    a: &Boolean,
    b: &Boolean,
) -> Result<Boolean, SynthesisError> {
    Ok(Boolean::not(&Boolean::and(
        cs.namespace(|| "not and (not a) (not b)"),
        &Boolean::not(a),
        &Boolean::not(b),
    )?))
}

fn must_be_simple_bit(x: &Boolean) -> AllocatedBit {
    match x {
        Boolean::Constant(_) => panic!("Expected a non-constant Boolean."),
        Boolean::Is(b) => b.clone(),
        Boolean::Not(b) => panic!("Expected a non-negated Boolean."),
    }
}

fn alloc_equal<CS: ConstraintSystem<E>, E: Engine>(
    mut cs: CS,
    a: &AllocatedNum<E>,
    b: &AllocatedNum<E>,
) -> Result<Boolean, SynthesisError> {
    let equal = a.get_value() == b.get_value();

    // Difference between `a` and `b`. This will be zero if `a` and `b` are equal.
    let diff = constraints::sub(cs.namespace(|| "a - b"), &a, &b)?;

    // result = (a == b)
    let result = AllocatedBit::alloc(cs.namespace(|| "a = b"), Some(equal))?;

    // result * diff = 0
    // This means that at least one of result or diff is zero.
    cs.enforce(
        || "result or diff is 0",
        |lc| lc + result.get_variable(),
        |lc| lc + diff.get_variable(),
        |lc| lc,
    );

    // Inverse of `diff`, if it exists, otherwise one.
    let q = if let Some(inv) = diff.get_value().unwrap().inverse() {
        inv
    } else {
        E::Fr::one()
    };

    // (diff + result) * q = 1.
    // This enforces that diff and result are not both 0.
    cs.enforce(
        || "(diff + result) * q = 1",
        |lc| lc + diff.get_variable() + result.get_variable(),
        |lc| Boolean::Constant(true).lc(CS::one(), q),
        |lc| lc + CS::one(),
    );

    // Taken together, these constraints enforce that exactly one of `diff` and `result` is 0.
    // Since result is constrained to be boolean, that means `result` is true iff `diff` is 0.
    // `Diff` is 0 iff `a == b`.
    // Therefore, `result = (a == b)`.

    Ok(Boolean::Is(result))
}

#[cfg(test)]

mod tests {
    use super::*;

    use bellperson::util_cs::test_cs::TestConstraintSystem;

    #[test]
    fn num_self_evaluating() {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let num = Expression::num(123);

        let input = IO {
            expr: num.clone(),
            env: env.clone(),
            cont: Continuation::Outermost,
        };

        let initial = input.clone();

        let test_with_output = |output, expect_success| {
            let mut cs = TestConstraintSystem::new();

            let frame = Frame {
                input: input.clone(),
                output,
                initial: initial.clone(),
                i: 0,
                witness: Witness::default(),
            };

            frame.synthesize(&mut cs).expect("failed to synthesize");

            if expect_success {
                assert!(cs.is_satisfied());
            } else {
                assert!(!cs.is_satisfied());
            }
        };

        // Success
        {
            let output = IO {
                expr: num.clone(),
                env: env.clone(),
                cont: Continuation::Terminal,
            };

            test_with_output(output, true);
        }

        // Failure
        {
            {
                // Wrong type, so tag should differ.
                let bad_output_tag = IO {
                    expr: store.intern("SYMBOL"),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                };

                test_with_output(bad_output_tag, false);
            }
            {
                // Wrong value, so hash should differ.
                let bad_output_value = IO {
                    expr: Expression::num(999),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                };

                test_with_output(bad_output_value, false);
            }
        }
    }

    #[test]
    fn nil_self_evaluating() {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let nil = Expression::Nil;

        let input = IO {
            expr: nil.clone(),
            env: env.clone(),
            cont: Continuation::Outermost,
        };

        let initial = input.clone();

        let test_with_output = |output, expect_success| {
            let mut cs = TestConstraintSystem::new();

            let frame = Frame {
                input: input.clone(),
                output,
                initial: initial.clone(),
                i: 0,
                witness: Witness::default(),
            };

            frame.synthesize(&mut cs).expect("failed to synthesize");

            if expect_success {
                assert!(cs.is_satisfied());
            } else {
                assert!(!cs.is_satisfied());
            }
        };

        // Success
        {
            let output = IO {
                expr: nil.clone(),
                env: env.clone(),
                cont: Continuation::Terminal,
            };

            test_with_output(output, true);
        }

        // Failure
        {
            {
                // Wrong type, so tag should differ.
                let bad_output_tag = IO {
                    expr: store.intern("SYMBOL"),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                };

                test_with_output(bad_output_tag, false);
            }
            {
                // Wrong value, so hash should differ.
                let bad_output_value = IO {
                    expr: Expression::num(999),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                };

                test_with_output(bad_output_value, false);
            }
        }
    }

    #[test]
    fn t_self_evaluating() {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let t = store.intern("T");

        let input = IO {
            expr: t.clone(),
            env: env.clone(),
            cont: Continuation::Outermost,
        };

        let initial = input.clone();

        let test_with_output = |output, expect_success| {
            let mut cs = TestConstraintSystem::new();

            let frame = Frame {
                input: input.clone(),
                output,
                initial: initial.clone(),
                i: 0,
                witness: Witness::default(),
            };

            frame.synthesize(&mut cs).expect("failed to synthesize");

            if expect_success {
                assert!(cs.is_satisfied());
            } else {
                assert!(!cs.is_satisfied());
            }
        };

        // Success
        {
            let output = IO {
                expr: t.clone(),
                env: env.clone(),
                cont: Continuation::Terminal,
            };

            test_with_output(output, true);
        }

        // Failure
        {
            {
                // Wrong type, so tag should differ.
                let bad_output_tag = IO {
                    expr: Expression::num(999),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                };

                test_with_output(bad_output_tag, false);
            }
            {
                // Wrong symbol, so hash should differ.
                let bad_output_value = IO {
                    expr: store.intern("S"),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                };

                test_with_output(bad_output_value, false);
            }
        }
    }

    #[test]
    fn fun_self_evaluating() {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let var = store.intern("a");
        let body = store.list(vec![var.clone()]);
        let fun = Expression::Fun(var.tagged_hash(), body.tagged_hash(), env.tagged_hash());

        let input = IO {
            expr: fun.clone(),
            env: env.clone(),
            cont: Continuation::Outermost,
        };

        let initial = input.clone();

        let test_with_output = |output, expect_success| {
            let mut cs = TestConstraintSystem::new();

            let frame = Frame {
                input: input.clone(),
                output,
                initial: initial.clone(),
                i: 0,
                witness: Witness::default(),
            };

            frame.synthesize(&mut cs).expect("failed to synthesize");

            if expect_success {
                assert!(cs.is_satisfied());
            } else {
                assert!(!cs.is_satisfied());
            }
        };

        // Success
        {
            let output = IO {
                expr: fun.clone(),
                env: env.clone(),
                cont: Continuation::Terminal,
            };

            test_with_output(output, true);
        }

        // Failure
        {
            {
                // Wrong type, so tag should differ.
                let bad_output_tag = IO {
                    expr: store.intern("SYMBOL"),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                };

                test_with_output(bad_output_tag, false);
            }
            {
                // Wrong value, so hash should differ.
                let bad_output_value = IO {
                    expr: Expression::num(999),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                };

                test_with_output(bad_output_value, false);
            }
        }
    }

    #[test]
    fn non_self_evaluating() {
        let mut store = Store::default();
        let env = empty_sym_env(&store);

        // Input is not self-evaluating.
        let expr = store.read("(+ 1 2)").unwrap();
        let input = IO {
            expr: expr.clone(),
            env: env.clone(),
            cont: Continuation::Outermost,
        };

        let initial = input.clone();

        let test_with_output = |output, expect_success| {
            let mut cs = TestConstraintSystem::new();

            let frame = Frame {
                input: input.clone(),
                output,
                initial: initial.clone(),
                i: 0,
                witness: Witness::default(),
            };

            frame.synthesize(&mut cs).expect("failed to synthesize");

            if expect_success {
                assert!(cs.is_satisfied());
            } else {
                assert!(!cs.is_satisfied());
            }
        };

        // Success
        {
            {
                // Output is not required to equal input.
                let output = IO {
                    //                expr: expr.clone(),
                    expr: Expression::num(987),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                };

                test_with_output(output, true);
            }
            {
                // However, output is permitted to equal input.
                // Input could theoretically be a single-step quine.
                // This is impossible in the current language for other reasons.
                let output = IO {
                    expr: expr.clone(),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                };

                test_with_output(output, true);
            }
        }
    }
}
