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

use crate::constraints::{self, equal};
use crate::data::{fr_from_u64, BaseContinuationTag, Continuation, Expression, Store, Tag, Tagged};
use crate::eval::{empty_sym_env, Frame, IO};

pub trait Provable {
    fn public_inputs(&self) -> Vec<Fr>;
}

pub struct Proof<F: Provable> {
    _frame: F,
    groth16_proof: groth16::Proof<Bls12>,
}

impl Provable for Frame<IO> {
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

impl Circuit<Bls12> for Frame<IO> {
    fn synthesize<CS: ConstraintSystem<Bls12>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
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
        // Input type

        // Optimization: We don't need to allocate the tags, but avoiding it requires a version
        // of `alloc_equal` that takes a constant. TODO
        let nil_tag = AllocatedNum::alloc(cs.namespace(|| "nil tag"), || Ok(Tag::Nil.fr()))?;
        let input_is_nil = alloc_equal(cs.namespace(|| "input is nil"), &input_tag, &nil_tag)?;

        let cons_tag = AllocatedNum::alloc(cs.namespace(|| "cons tag"), || Ok(Tag::Cons.fr()))?;
        let input_is_cons = alloc_equal(cs.namespace(|| "input is Cons"), &input_tag, &cons_tag)?;

        let sym_tag = AllocatedNum::alloc(cs.namespace(|| "sym tag"), || Ok(Tag::Sym.fr()))?;
        let input_is_sym = alloc_equal(cs.namespace(|| "input is sym"), &input_tag, &sym_tag)?;

        let fun_tag = AllocatedNum::alloc(cs.namespace(|| "fun tag"), || Ok(Tag::Fun.fr()))?;
        let input_is_fun = alloc_equal(cs.namespace(|| "input is fun"), &input_tag, &fun_tag)?;

        let num_tag = AllocatedNum::alloc(cs.namespace(|| "num tag"), || Ok(Tag::Num.fr()))?;
        let input_is_num = alloc_equal(cs.namespace(|| "input is num"), &input_tag, &num_tag)?;

        let thunk_tag = AllocatedNum::alloc(cs.namespace(|| "cont tag"), || Ok(Tag::Thunk.fr()))?;
        let input_is_cont = alloc_equal(cs.namespace(|| "input is Cont"), &input_tag, &thunk_tag)?;

        //
        ////////////////////////////////////////////////////////////////////////////////

        ////////////////////////////////////////////////////////////////////////////////
        // Input Continuation type

        let outermost_cont_tag =
            AllocatedNum::alloc(cs.namespace(|| "Outermost continuation tag"), || {
                Ok(BaseContinuationTag::Outermost.cont_tag_fr())
            })?;
        let input_cont_is_outermost = alloc_equal(
            cs.namespace(|| "input cont is Outermost"),
            &input_cont_tag,
            &outermost_cont_tag,
        )?;

        let simple_cont_tag =
            AllocatedNum::alloc(cs.namespace(|| "Simple continuation tag"), || {
                Ok(BaseContinuationTag::Simple.cont_tag_fr())
            })?;
        let input_cont_is_simple = alloc_equal(
            cs.namespace(|| "input cont is Simple"),
            &input_cont_tag,
            &simple_cont_tag,
        )?;

        let call_cont_tag = AllocatedNum::alloc(cs.namespace(|| "Call continuation tag"), || {
            Ok(BaseContinuationTag::Call.cont_tag_fr())
        })?;
        let input_cont_is_call = alloc_equal(
            cs.namespace(|| "input cont is Call"),
            &input_cont_tag,
            &call_cont_tag,
        )?;

        let call2_cont_tag =
            AllocatedNum::alloc(cs.namespace(|| "Call2 continuation tag"), || {
                Ok(BaseContinuationTag::Call2.cont_tag_fr())
            })?;
        let input_cont_is_call2 = alloc_equal(
            cs.namespace(|| "input cont is Call2"),
            &input_cont_tag,
            &call2_cont_tag,
        )?;

        let tail_cont_tag = AllocatedNum::alloc(cs.namespace(|| "Tail continuation tag"), || {
            Ok(BaseContinuationTag::Tail.cont_tag_fr())
        })?;
        let input_cont_is_tail = alloc_equal(
            cs.namespace(|| "input cont is Tail"),
            &input_cont_tag,
            &tail_cont_tag,
        )?;

        let error_cont_tag =
            AllocatedNum::alloc(cs.namespace(|| "Error continuation tag"), || {
                Ok(BaseContinuationTag::Error.cont_tag_fr())
            })?;
        let input_cont_is_error = alloc_equal(
            cs.namespace(|| "input cont is Error"),
            &input_cont_tag,
            &error_cont_tag,
        )?;

        let lookup_cont_tag =
            AllocatedNum::alloc(cs.namespace(|| "Lookup continuation tag"), || {
                Ok(BaseContinuationTag::Lookup.cont_tag_fr())
            })?;
        let input_cont_is_lookup = alloc_equal(
            cs.namespace(|| "input cont is Lookup"),
            &input_cont_tag,
            &lookup_cont_tag,
        )?;

        let binop_cont_tag =
            AllocatedNum::alloc(cs.namespace(|| "Binop continuation tag"), || {
                Ok(BaseContinuationTag::Binop.cont_tag_fr())
            })?;
        let input_cont_is_binop = alloc_equal(
            cs.namespace(|| "input cont is Binop"),
            &input_cont_tag,
            &binop_cont_tag,
        )?;

        let binop2_cont_tag =
            AllocatedNum::alloc(cs.namespace(|| "Binop2 continuation tag"), || {
                Ok(BaseContinuationTag::Binop2.cont_tag_fr())
            })?;
        let input_cont_is_binop2 = alloc_equal(
            cs.namespace(|| "input cont is Binop2"),
            &input_cont_tag,
            &binop2_cont_tag,
        )?;

        let relop_cont_tag =
            AllocatedNum::alloc(cs.namespace(|| "Relop continuation tag"), || {
                Ok(BaseContinuationTag::Relop.cont_tag_fr())
            })?;
        let input_cont_is_relop = alloc_equal(
            cs.namespace(|| "input cont is Relop"),
            &input_cont_tag,
            &relop_cont_tag,
        )?;

        let relop2_cont_tag =
            AllocatedNum::alloc(cs.namespace(|| "Relop2 continuation tag"), || {
                Ok(BaseContinuationTag::Relop2.cont_tag_fr())
            })?;
        let input_cont_is_relop2 = alloc_equal(
            cs.namespace(|| "input cont is Relop2"),
            &input_cont_tag,
            &relop2_cont_tag,
        )?;

        let if_cont_tag = AllocatedNum::alloc(cs.namespace(|| "If continuation tag"), || {
            Ok(BaseContinuationTag::If.cont_tag_fr())
        })?;
        let input_cont_is_if = alloc_equal(
            cs.namespace(|| "input cont is If"),
            &input_cont_tag,
            &if_cont_tag,
        )?;

        let let_cont_tag = AllocatedNum::alloc(cs.namespace(|| "Let continuation tag"), || {
            Ok(BaseContinuationTag::LetStar.cont_tag_fr())
        })?;
        let input_cont_is_let = alloc_equal(
            cs.namespace(|| "input cont is Let"),
            &input_cont_tag,
            &let_cont_tag,
        )?;

        let let_rec_star_cont_tag =
            AllocatedNum::alloc(cs.namespace(|| "LetRecStar continuation tag"), || {
                Ok(BaseContinuationTag::Tail.cont_tag_fr())
            })?;
        let input_cont_is_let_rec_star = alloc_equal(
            cs.namespace(|| "input cont is LetRecStar"),
            &input_cont_tag,
            &let_rec_star_cont_tag,
        )?;

        let dummy_cont_tag =
            AllocatedNum::alloc(cs.namespace(|| "Dummy continuation tag"), || {
                Ok(BaseContinuationTag::Dummy.cont_tag_fr())
            })?;
        let input_cont_is_dummy = alloc_equal(
            cs.namespace(|| "input cont is Dummy"),
            &input_cont_tag,
            &dummy_cont_tag,
        )?;

        let terminal_cont_tag =
            AllocatedNum::alloc(cs.namespace(|| "Terminal continuation tag"), || {
                Ok(BaseContinuationTag::Terminal.cont_tag_fr())
            })?;
        let input_cont_is_terminal = alloc_equal(
            cs.namespace(|| "input cont is Terminal"),
            &input_cont_tag,
            &terminal_cont_tag,
        )?;

        //
        ////////////////////////////////////////////////////////////////////////////////

        ////////////////////////////////////////////////////////////////////////////////
        // Output Continuation type

        let output_cont_is_outermost = alloc_equal(
            cs.namespace(|| "output cont is Outermost"),
            &output_cont_tag,
            &outermost_cont_tag,
        )?;

        let output_cont_is_simple = alloc_equal(
            cs.namespace(|| "output cont is Simple"),
            &output_cont_tag,
            &simple_cont_tag,
        )?;

        let output_cont_is_call = alloc_equal(
            cs.namespace(|| "output cont is Call"),
            &output_cont_tag,
            &call_cont_tag,
        )?;

        let output_cont_is_call2 = alloc_equal(
            cs.namespace(|| "output cont is Call2"),
            &output_cont_tag,
            &call2_cont_tag,
        )?;

        let output_cont_is_tail = alloc_equal(
            cs.namespace(|| "output cont is Tail"),
            &output_cont_tag,
            &tail_cont_tag,
        )?;

        let output_cont_is_error = alloc_equal(
            cs.namespace(|| "output cont is Error"),
            &output_cont_tag,
            &error_cont_tag,
        )?;

        let output_cont_is_lookup = alloc_equal(
            cs.namespace(|| "output cont is Lookup"),
            &output_cont_tag,
            &lookup_cont_tag,
        )?;

        let output_cont_is_binop = alloc_equal(
            cs.namespace(|| "output cont is Binop"),
            &output_cont_tag,
            &binop_cont_tag,
        )?;

        let output_cont_is_binop2 = alloc_equal(
            cs.namespace(|| "output cont is Binop2"),
            &output_cont_tag,
            &binop2_cont_tag,
        )?;

        let output_cont_is_relop = alloc_equal(
            cs.namespace(|| "output cont is Relop"),
            &output_cont_tag,
            &relop_cont_tag,
        )?;

        let output_cont_is_relop2 = alloc_equal(
            cs.namespace(|| "output cont is Relop2"),
            &output_cont_tag,
            &relop2_cont_tag,
        )?;

        let output_cont_is_if = alloc_equal(
            cs.namespace(|| "output cont is If"),
            &output_cont_tag,
            &if_cont_tag,
        )?;

        let output_cont_is_let = alloc_equal(
            cs.namespace(|| "output cont is Let"),
            &output_cont_tag,
            &let_cont_tag,
        )?;

        let output_cont_is_let_rec_star = alloc_equal(
            cs.namespace(|| "output cont is LetRecStar"),
            &output_cont_tag,
            &let_rec_star_cont_tag,
        )?;

        let output_cont_is_dummy = alloc_equal(
            cs.namespace(|| "output cont is Dummy"),
            &output_cont_tag,
            &dummy_cont_tag,
        )?;

        let output_cont_is_terminal = alloc_equal(
            cs.namespace(|| "output cont is Terminal"),
            &output_cont_tag,
            &terminal_cont_tag,
        )?;

        //
        ////////////////////////////////////////////////////////////////////////////////

        ////////////////////////////////////////////////////////////////////////////////
        // Self-evaluating inputs
        //

        let input_is_self_evaluating = {
            // Set boolean flags based on input type tags.

            // TODO: This allocation is also unneeded when we have `alloc_const_equal` (or whatever we call it).
            let t_hash = AllocatedNum::alloc(cs.namespace(|| "sym hash"), || {
                Ok(Expression::Sym("T".to_string()).get_hash())
            })?;

            let input_hash_matches_sym_t = alloc_equal(
                cs.namespace(|| "input hash matches sym T"),
                &input_hash,
                &t_hash,
            )?;

            let input_is_t = Boolean::and(
                cs.namespace(|| "input is sym t"),
                &Boolean::Is(input_is_sym),
                &Boolean::Is(input_hash_matches_sym_t),
            )?;

            let input_is_self_evaluating_sym = or(
                cs.namespace(|| "input is self-evaluating sym"),
                &Boolean::Is(input_is_nil),
                &input_is_t,
            )?;

            let input_is_num_or_fun = or(
                cs.namespace(|| "input is num or fun"),
                &Boolean::Is(input_is_num),
                &Boolean::Is(input_is_fun),
            )?;

            or(
                cs.namespace(|| "input is self-evaluating"),
                &input_is_num_or_fun,
                &input_is_self_evaluating_sym,
            )?
        };

        let input_output_equal = {
            // Allocates a bit which is true if input and output expressions are identical.

            let tags_equal = alloc_equal(cs.namespace(|| "tags equal"), &input_tag, &output_tag)?;
            let hashes_equal =
                alloc_equal(cs.namespace(|| "hashes equal"), &input_hash, &output_hash)?;

            Boolean::and(
                cs.namespace(|| "input and output are equal"),
                &Boolean::Is(tags_equal),
                &Boolean::Is(hashes_equal),
            )?
        };

        dbg!(
            &input_is_self_evaluating.get_value(),
            &input_output_equal.get_value()
        );

        enforce_implication(
            cs.namespace(|| "if input_is_self_evaluating then input_output_equal"),
            &input_is_self_evaluating,
            &input_output_equal,
        );

        //
        // End Self-evaluating inputs
        ////////////////////////////////////////////////////////////////////////////////

        dbg!(&input_tag.get_value(), &output_tag.get_value());
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
) -> Result<AllocatedBit, SynthesisError> {
    let equal = a.get_value() == b.get_value();

    // Difference between `a` and `b`. This will be zero if `a` and `b` are equal.
    let diff = constraints::sub(cs.namespace(|| "a - b"), &a, &b)?;

    // result = (a == b)
    let result = AllocatedBit::alloc(cs.namespace(|| "a = b"), Some(equal))?;

    dbg!(equal, diff.get_value(), result.get_value());
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

    dbg!(&q);

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

    Ok(result)
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
