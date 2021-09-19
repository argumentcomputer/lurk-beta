use bellperson::{
    bls::{Bls12, Engine, Fr},
    gadgets::{
        boolean::{AllocatedBit, Boolean},
        num::AllocatedNum,
    },
    groth16::{self, verify_proof},
    Circuit, ConstraintSystem, SynthesisError,
};
use ff::Field;
use neptune::circuit::poseidon_hash;

use crate::constraints::{self};
use crate::data::{
    fr_from_u64, BaseContinuationTag, Continuation, Expression, Tag, Tagged, Thunk,
    POSEIDON_CONSTANTS_4, POSEIDON_CONSTANTS_9,
};
use crate::eval::{Frame, Witness, IO};

pub trait Provable {
    fn public_inputs(&self) -> Vec<Fr>;
}

pub struct Proof<F: Provable> {
    _frame: F,
    groth16_proof: groth16::Proof<Bls12>,
}

impl<W> Provable for Frame<IO<W>> {
    fn public_inputs(&self) -> Vec<Fr> {
        let mut inputs = Vec::with_capacity(10);

        inputs.extend(self.input.public_inputs());
        inputs.extend(self.output.public_inputs());
        inputs.extend(self.initial.public_inputs());
        inputs.push(fr_from_u64(self.i as u64));

        inputs
    }
}

impl<W> IO<W> {
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
    tag.inputize(cs.namespace(|| "tag input"))?;

    let hash = AllocatedNum::alloc(cs.namespace(|| "hash"), || Ok(tagged_hash.hash))?;
    hash.inputize(cs.namespace(|| "hash input"))?;

    Ok((tag, hash))
}

fn bind_input_cont<CS: ConstraintSystem<Bls12>>(
    cs: &mut CS,
    cont: &Continuation,
) -> Result<(AllocatedNum<Bls12>, AllocatedNum<Bls12>), SynthesisError> {
    let tag = AllocatedNum::alloc(cs.namespace(|| "continuation tag"), || {
        Ok(cont.get_continuation_tag().cont_tag_fr())
    })?;
    tag.inputize(cs.namespace(|| "continuation tag input"))?;

    let hash = AllocatedNum::alloc(cs.namespace(|| "continuation hash"), || Ok(cont.get_hash()))?;
    hash.inputize(cs.namespace(|| "continuation hash input"))?;

    Ok((tag, hash))
}

fn bind_tag_hash<CS: ConstraintSystem<Bls12>>(
    cs: &mut CS,
    expr: Option<Expression>,
) -> Result<(AllocatedNum<Bls12>, AllocatedNum<Bls12>), SynthesisError> {
    let (tag, hash) = if let Some(e) = expr {
        let tag = AllocatedNum::alloc(cs.namespace(|| "tag"), || Ok(e.tag_fr()))?;
        let hash = AllocatedNum::alloc(cs.namespace(|| "hash"), || Ok(e.get_hash()))?;
        (tag, hash)
    } else {
        let tag = AllocatedNum::alloc(cs.namespace(|| "tag"), || Ok(Fr::zero()))?;
        let hash = AllocatedNum::alloc(cs.namespace(|| "hash"), || Ok(Fr::zero()))?;

        (tag, hash)
    };

    Ok((tag, hash))
}

fn bind_continuation_tag_hash<CS: ConstraintSystem<Bls12>>(
    cs: &mut CS,
    cont: Option<Continuation>,
) -> Result<(AllocatedNum<Bls12>, AllocatedNum<Bls12>), SynthesisError> {
    let (tag, hash) = if let Some(e) = cont {
        let tag = AllocatedNum::alloc(cs.namespace(|| "tag"), || {
            Ok(e.get_continuation_tag().cont_tag_fr())
        })?;
        let hash = AllocatedNum::alloc(cs.namespace(|| "hash"), || Ok(e.get_hash()))?;
        (tag, hash)
    } else {
        let tag = AllocatedNum::alloc(cs.namespace(|| "tag"), || Ok(Fr::zero()))?;
        let hash = AllocatedNum::alloc(cs.namespace(|| "hash"), || Ok(Fr::zero()))?;

        (tag, hash)
    };

    Ok((tag, hash))
}

// Enforces constraint that a implies b.
macro_rules! if_then {
    ($cs:ident, $a:expr, $b:expr) => {
        enforce_implication(
            $cs.namespace(|| format!("if {} then {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        )
    };
}

// Enforces constraint that a implies b and that (not a) implices c.
macro_rules! if_then_else {
    ($cs:ident, $a:expr, $b:expr, $c:expr) => {
        enforce_implication(
            $cs.namespace(|| format!("if {} then {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        )
        .and_then(|_| {
            enforce_implication(
                $cs.namespace(|| {
                    format!(
                        "if {} then {} else {}",
                        stringify!($a),
                        stringify!($b),
                        stringify!($c)
                    )
                }),
                &Boolean::not($a),
                $c,
            )
        })
    };
}

// Allocates a bit (returned as Boolean) which is true if a and b are equal.
macro_rules! equal {
    ($cs:ident, $a:expr, $b:expr) => {
        alloc_equal(
            $cs.namespace(|| format!("{} equals {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        )
    };
}

// Returns a Boolean which is true if a and b are true.
macro_rules! and {
    ($cs:ident, $a:expr, $b:expr) => {
        Boolean::and(
            $cs.namespace(|| format!("{} and {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        )
    };
}

macro_rules! tag_and_hash_equal {
    ($cs:ident, $a_tag:expr, $b_tag:expr, $a_hash:expr, $b_hash:expr) => {{
        let tags_equal = equal!($cs, &$a_tag, &$b_tag)?;
        let hashes_equal = equal!($cs, &$a_hash, &$b_hash)?;
        let mut cs = $cs.namespace(|| {
            format!(
                "({} equals {}) and ({} equals {})",
                stringify!($a_tag),
                stringify!($b_tag),
                stringify!($a_hash),
                stringify!($b_hash)
            )
        });
        and!(cs, &tags_equal, &hashes_equal)
    }};
}

// Returns a Boolean which is true if a or b are true.
macro_rules! or {
    ($cs:ident, $a:expr, $b:expr) => {
        or(
            $cs.namespace(|| format!("{} or {}", stringify!($a), stringify!($b))),
            $a,
            $b,
        )
    };
}

// Enforce that x is true.
macro_rules! is_true {
    ($cs:ident, $x:expr) => {
        enforce_true($cs.namespace(|| format!("{} is true!", stringify!($x))), $x);
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

impl Circuit<Bls12> for Frame<IO<Witness>> {
    fn synthesize<CS: ConstraintSystem<Bls12>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let witness = self.input.witness.clone().unwrap();

        ////////////////////////////////////////////////////////////////////////////////
        // Bind public inputs.
        //
        // The frame's input:
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
        let (_initial_tag, _initial_hash) = bind_input(
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
        let let_star_cont_tag = allocate_continuation_tag!(cs, BaseContinuationTag::LetStar)?;
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
        let input_cont_is_let_star = equal!(cs, &input_cont_tag, &let_star_cont_tag)?;
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
        let output_cont_is_let_star = equal!(cs, &output_cont_tag, &let_star_cont_tag)?;
        let output_cont_is_let_rec_star = equal!(cs, &output_cont_tag, &let_rec_star_cont_tag)?;
        let output_cont_is_dummy = equal!(cs, &output_cont_tag, &dummy_cont_tag)?;
        let output_cont_is_terminal = equal!(cs, &output_cont_tag, &terminal_cont_tag)?;

        ////////////////////////////////////////////////////////////////////////////////
        // Witness

        let (invoke_continuation_cont_tag, invoke_continuation_cont_hash) = if let Some(cont) =
            &witness.invoke_continuation_cont
        {
            let tag = AllocatedNum::alloc(cs.namespace(|| "continuation tag"), || {
                Ok(cont.get_continuation_tag().cont_tag_fr())
            })?;

            let hash =
                AllocatedNum::alloc(cs.namespace(|| "continuation hash"), || Ok(cont.get_hash()))?;

            (tag, hash)
        } else {
            (
                AllocatedNum::alloc(cs.namespace(|| "continuation tag"), || Ok(Fr::zero()))?,
                AllocatedNum::alloc(cs.namespace(|| "continuation hash"), || Ok(Fr::zero()))?,
            )
        };

        ////////////////////////////////////////////////////////////////////////////////
        // invoke_continuation Continuation type
        let invoke_continuation_cont_is_outermost =
            equal!(cs, &invoke_continuation_cont_tag, &outermost_cont_tag)?;
        let invoke_continuation_cont_is_simple =
            equal!(cs, &invoke_continuation_cont_tag, &simple_cont_tag)?;
        let invoke_continuation_cont_is_call =
            equal!(cs, &invoke_continuation_cont_tag, &call_cont_tag)?;
        let invoke_continuation_cont_is_call2 =
            equal!(cs, &invoke_continuation_cont_tag, &call2_cont_tag)?;
        let invoke_continuation_cont_is_tail =
            equal!(cs, &invoke_continuation_cont_tag, &tail_cont_tag)?;
        let invoke_continuation_cont_is_error =
            equal!(cs, &invoke_continuation_cont_tag, &error_cont_tag)?;
        let invoke_continuation_cont_is_lookup =
            equal!(cs, &invoke_continuation_cont_tag, &lookup_cont_tag)?;
        let invoke_continuation_cont_is_binop =
            equal!(cs, &invoke_continuation_cont_tag, &binop_cont_tag)?;
        let invoke_continuation_cont_is_binop2 =
            equal!(cs, &invoke_continuation_cont_tag, &binop2_cont_tag)?;
        let invoke_continuation_cont_is_relop =
            equal!(cs, &invoke_continuation_cont_tag, &relop_cont_tag)?;
        let invoke_continuation_cont_is_relop2 =
            equal!(cs, &invoke_continuation_cont_tag, &relop2_cont_tag)?;
        let invoke_continuation_cont_is_if =
            equal!(cs, &invoke_continuation_cont_tag, &if_cont_tag)?;
        let invoke_continuation_cont_is_let_star =
            equal!(cs, &invoke_continuation_cont_tag, &let_star_cont_tag)?;
        let invoke_continuation_cont_is_let_rec_star =
            equal!(cs, &invoke_continuation_cont_tag, &let_rec_star_cont_tag)?;
        let invoke_continuation_cont_is_dummy =
            equal!(cs, &invoke_continuation_cont_tag, &dummy_cont_tag)?;
        let invoke_continuation_cont_is_terminal =
            equal!(cs, &invoke_continuation_cont_tag, &terminal_cont_tag)?;

        // True if make_thunk was called when evaluating (according to the prover's witness).
        let make_thunk_was_called = Boolean::Is(AllocatedBit::alloc(
            cs.namespace(|| "make_thunk_was_called"),
            Some(witness.make_thunk_was_called),
        )?);

        let (make_thunk_result_tag, make_thunk_result_hash) = bind_tag_hash(
            &mut cs.namespace(|| "make_thunk result"),
            witness.clone().make_thunk_result,
        )?;

        let (make_thunk_env_tag, make_thunk_env_hash) = bind_tag_hash(
            &mut cs.namespace(|| "make_thunk env"),
            witness.clone().make_thunk_env,
        )?;

        let (make_thunk_effective_env_tag, make_thunk_effective_env_hash) = bind_tag_hash(
            &mut cs.namespace(|| "make_thunk effective_env"),
            witness.clone().make_thunk_effective_env,
        )?;

        let (make_thunk_effective_env2_tag, make_thunk_effective_env2_hash) = bind_tag_hash(
            &mut cs.namespace(|| "make_thunk effective2_env"),
            witness.clone().make_thunk_effective_env2,
        )?;

        let (make_thunk_output_result_tag, make_thunk_output_result_hash) = bind_tag_hash(
            &mut cs.namespace(|| "make_thunk output_result"),
            witness.clone().make_thunk_output_result,
        )?;

        let (make_thunk_output_env_tag, make_thunk_output_env_hash) = bind_tag_hash(
            &mut cs.namespace(|| "make_thunk output_env"),
            witness.clone().make_thunk_output_env,
        )?;

        let (make_thunk_tail_continuation_cont_hash, make_thunk_tail_continuation_cont_components) =
            if let Some(c) = &witness.make_thunk_tail_continuation_cont {
                c.allocate_components(
                    cs.namespace(|| "make_thunk tail continuation cont components"),
                )?
            } else {
                Continuation::allocate_dummy_components(
                    cs.namespace(|| "make_thunk tail continuation cont components"),
                )?
            };

        let make_thunk_actual_thunk = witness
            .clone()
            .make_thunk_tail_continuation_thunk
            .or_else(|| witness.make_thunk_thunk.clone());

        let the_thunk = make_thunk_actual_thunk.or(witness.clone().invoke_continuation_thunk);

        let (the_thunk_hash, the_thunk_components) = if let Some(thunk) = &the_thunk {
            thunk.allocate_components(cs.namespace(|| "make_thunk_tail_continuation_thunk"))?
        } else {
            Thunk::allocate_dummy_components(cs.namespace(|| "make_thunk_tail_continuation_thunk"))?
        };
        let (the_thunk_value_tag, the_thunk_value_hash, the_thunk_cont_tag, the_thunk_cont_hash) = (
            the_thunk_components[0].clone(),
            the_thunk_components[1].clone(),
            the_thunk_components[2].clone(),
            the_thunk_components[3].clone(),
        );

        let make_thunk_output_result_is_thunk = tag_and_hash_equal!(
            cs,
            &make_thunk_output_result_tag,
            &thunk_tag,
            &make_thunk_output_result_hash,
            &the_thunk_hash
        )?;

        let thunk_thunk_value_is_make_thunk_result =
            equal!(cs, &make_thunk_result_hash, &the_thunk_hash)?;

        let make_thunk_tail_continuation_cont_saved_env_tag =
            make_thunk_tail_continuation_cont_components[1].clone();
        let make_thunk_tail_continuation_cont_saved_env_hash =
            make_thunk_tail_continuation_cont_components[2].clone();

        let (make_thunk_cont_hash, make_thunk_cont_components) =
            if let Some(c) = &witness.make_thunk_cont {
                c.allocate_components(cs.namespace(|| "make_thunk cont components"))?
            } else {
                Continuation::allocate_dummy_components(
                    cs.namespace(|| "make_thunk output components"),
                )?
            };

        let (make_thunk_output_cont_hash, make_thunk_output_cont_components) =
            if let Some(c) = &witness.make_thunk_output_cont {
                c.allocate_components(cs.namespace(|| "make_thunk output cont components"))?
            } else {
                Continuation::allocate_dummy_components(
                    cs.namespace(|| "make_thunk output cont components"),
                )?
            };

        let make_thunk_cont_tag = make_thunk_cont_components[0].clone();
        let make_thunk_output_cont_tag = make_thunk_output_cont_components[0].clone();

        ////////////////////////////////////////////////////////////////////////////////
        // invoke_continuation
        let invoke_continuation_was_called = Boolean::Is(AllocatedBit::alloc(
            cs.namespace(|| "invoke_continuation_was_called"),
            Some(witness.invoke_continuation_was_called),
        )?);

        let (invoke_continuation_result_tag, invoke_continuation_result_hash) = bind_tag_hash(
            &mut cs.namespace(|| "invoke_continuation result"),
            witness.clone().invoke_continuation_result,
        )?;

        let (invoke_continuation_env_tag, invoke_continuation_env_hash) = bind_tag_hash(
            &mut cs.namespace(|| "invoke_continuation env"),
            witness.clone().invoke_continuation_env,
        )?;

        let (invoke_continuation_output_result_tag, invoke_continuation_output_result_hash) =
            bind_tag_hash(
                &mut cs.namespace(|| "invoke_continuation output result"),
                witness.clone().invoke_continuation_output_result,
            )?;

        let (invoke_continuation_output_env_tag, invoke_continuation_output_env_hash) =
            bind_tag_hash(
                &mut cs.namespace(|| "invoke_continuation output env"),
                witness.clone().invoke_continuation_output_env,
            )?;

        let (invoke_continuation_output_cont_tag, invoke_continuation_output_cont_hash) =
            bind_continuation_tag_hash(
                &mut cs.namespace(|| "invoke_continuation cont env"),
                witness.clone().invoke_continuation_output_cont,
            )?;

        {
            // Begin make_thunk handling.

            ////////////////////////////////////////////////////////////////////////////////
            // Thunk
            // let make_thunk_cont_components = if let Some(c) = witness.make_thunk_cont {
            //     c.allocate_components(cs.namespace(|| "make_thunk cont components"))?
            // } else {
            //     Continuation::allocate_dummy_components(cs.namespace(|| "make_thunk cont components"))?
            // };

            // If there is a saved_env component, they are these.
            let make_thunk_cont_saved_env_tag = make_thunk_cont_components[1].clone();
            let make_thunk_cont_saved_env_hash = make_thunk_cont_components[2].clone();

            // These names only makes sense if this the continuation is indeed a tail continuation.
            // We use them optimistically, since that is the only case in which we require the values.
            // Appropriate constraints are needed.
            let make_thunk_tail_continuation_cont_tag = make_thunk_cont_components[4].clone();
            let make_thunk_tail_continuation_cont_hash = make_thunk_cont_components[5].clone();

            let thunk_cont_is_tail = equal!(cs, &make_thunk_cont_tag, &tail_cont_tag)?;

            let thunk_cont_is_lookup = equal!(cs, &make_thunk_cont_tag, &lookup_cont_tag)?;
            let thunk_cont_is_outermost = equal!(cs, &make_thunk_cont_tag, &outermost_cont_tag)?;

            let make_thunk_tail_continuation_cont_is_lookup =
                equal!(cs, &make_thunk_tail_continuation_cont_tag, &lookup_cont_tag)?;

            let make_thunk_tail_continuation_cont_is_outermost = equal!(
                cs,
                &make_thunk_tail_continuation_cont_tag,
                &outermost_cont_tag
            )?;

            let thunk_cont_has_saved_env = or!(cs, &thunk_cont_is_lookup, &thunk_cont_is_tail)?;

            let make_thunk_effective_env_is_cont_saved_env = tag_and_hash_equal!(
                cs,
                &make_thunk_effective_env_tag,
                &make_thunk_cont_saved_env_tag,
                &make_thunk_effective_env_hash,
                &make_thunk_cont_saved_env_hash
            )?;

            let make_thunk_effective_env_is_env = tag_and_hash_equal!(
                cs,
                &make_thunk_effective_env_tag,
                &make_thunk_env_tag,
                &make_thunk_effective_env_hash,
                &make_thunk_env_hash
            )?;

            if_then_else!(
                cs,
                &thunk_cont_has_saved_env,
                &make_thunk_effective_env_is_cont_saved_env,
                &make_thunk_effective_env_is_env
            )?;

            let make_thunk_output_result_is_make_thunk_result = tag_and_hash_equal!(
                cs,
                &make_thunk_output_result_tag,
                &make_thunk_result_tag,
                &make_thunk_output_result_hash,
                &make_thunk_result_hash
            )?;

            let make_thunk_output_env_is_effective_env = tag_and_hash_equal!(
                cs,
                &make_thunk_output_env_tag,
                &make_thunk_effective_env_tag,
                &make_thunk_output_env_hash,
                &make_thunk_effective_env_hash
            )?;

            let make_thunk_output_env_is_effective_env2 = tag_and_hash_equal!(
                cs,
                &make_thunk_output_env_tag,
                &make_thunk_effective_env2_tag,
                &make_thunk_output_env_hash,
                &make_thunk_effective_env2_hash
            )?;

            let make_thunk_output_cont_is_terminal =
                equal!(cs, &make_thunk_output_cont_tag, &terminal_cont_tag)?;

            // FIXME: We still have to check hashes and values of Terminal/Dummy continuations to ensure
            // they have the expected values. Otherwise, results will not be deterministic, and the proof will
            // be unsound.

            let make_thunk_output_cont_is_dummy =
                equal!(cs, &make_thunk_output_cont_tag, &dummy_cont_tag)?;

            {
                // When make_thunk continuation is Tail:

                let make_thunk_was_called_with_tail_continuation =
                    and!(cs, &make_thunk_was_called, &thunk_cont_is_tail)?;

                let make_thunk_effective_env2_is_tail_continuation_cont_saved_env = tag_and_hash_equal!(
                    cs,
                    &make_thunk_effective_env_tag,
                    &make_thunk_tail_continuation_cont_saved_env_tag,
                    &make_thunk_effective_env_hash,
                    &make_thunk_tail_continuation_cont_saved_env_hash
                )?;

                let make_thunk_effective_env2_is_effective_env = tag_and_hash_equal!(
                    cs,
                    &make_thunk_effective_env2_tag,
                    &make_thunk_effective_env_tag,
                    &make_thunk_effective_env2_hash,
                    &make_thunk_effective_env_hash
                )?;

                // Check effective_env2.
                if_then!(
                    cs,
                    &make_thunk_tail_continuation_cont_is_lookup,
                    &make_thunk_effective_env2_is_effective_env
                )?;
                let cont_is_tail_and_its_cont_is_lookup = and!(
                    cs,
                    &thunk_cont_is_tail,
                    &make_thunk_tail_continuation_cont_is_lookup
                )?;
                if_then!(
                    cs,
                    &cont_is_tail_and_its_cont_is_lookup,
                    &make_thunk_effective_env2_is_tail_continuation_cont_saved_env
                )?;
                let cont_is_tail_and_its_cont_is_not_lookup = and!(
                    cs,
                    &thunk_cont_is_tail,
                    &Boolean::not(&make_thunk_tail_continuation_cont_is_lookup)
                )?;

                is_true!(cs, &Boolean::not(&cont_is_tail_and_its_cont_is_not_lookup));

                let make_thunk_was_called_and_tail_continuation_cont_is_outermost = and!(
                    cs,
                    &make_thunk_was_called,
                    &make_thunk_tail_continuation_cont_is_outermost
                )?;

                // Check make_thunk output result is make_thunk input result.

                if_then!(
                    cs,
                    &make_thunk_was_called_and_tail_continuation_cont_is_outermost,
                    &make_thunk_output_result_is_make_thunk_result
                )?;

                if_then_else!(
                    cs,
                    &make_thunk_was_called_and_tail_continuation_cont_is_outermost,
                    &make_thunk_output_env_is_effective_env,
                    &make_thunk_output_env_is_effective_env2
                )?;

                // This could be optimized, for example, by creating a variable that is true
                // If either make_func_cont or its tail_cont is outermost, then combining
                // this if_then! constraint with one below (next section).
                if_then!(
                    cs,
                    &make_thunk_was_called_and_tail_continuation_cont_is_outermost,
                    &make_thunk_output_cont_is_terminal
                )?;

                let make_thunk_was_called_with_tail_continuation_whose_cont_is_not_outermost = and!(
                    cs,
                    &make_thunk_was_called_with_tail_continuation,
                    &Boolean::not(&make_thunk_tail_continuation_cont_is_outermost)
                )?;

                if_then!(
                    cs,
                    &make_thunk_was_called_with_tail_continuation_whose_cont_is_not_outermost,
                    &make_thunk_output_result_is_thunk
                )?;

                if_then!(
                    cs,
                    &make_thunk_was_called_with_tail_continuation_whose_cont_is_not_outermost,
                    &thunk_thunk_value_is_make_thunk_result
                )?;

                let thunk_thunk_continuation_is_tail_continuation_cont = tag_and_hash_equal!(
                    cs,
                    &the_thunk_cont_tag,
                    &make_thunk_tail_continuation_cont_tag,
                    &the_thunk_cont_hash,
                    &make_thunk_tail_continuation_cont_hash
                )?;

                if_then!(
                    cs,
                    &make_thunk_was_called_with_tail_continuation_whose_cont_is_not_outermost,
                    &thunk_thunk_continuation_is_tail_continuation_cont
                )?;

                if_then!(
                    cs,
                    &make_thunk_was_called_with_tail_continuation_whose_cont_is_not_outermost,
                    &make_thunk_output_env_is_effective_env2
                )?;

                if_then!(
                    cs,
                    &make_thunk_was_called_with_tail_continuation_whose_cont_is_not_outermost,
                    &make_thunk_output_cont_is_dummy
                )?;
            }
            {
                // When make_thunk continuation is Outermost:

                let make_thunk_was_called_and_cont_is_outermost =
                    and!(cs, &make_thunk_was_called, &thunk_cont_is_outermost)?;

                // Check make_thunk output result is make_thunk input result.
                if_then!(
                    cs,
                    &make_thunk_was_called_and_cont_is_outermost,
                    &make_thunk_output_result_is_make_thunk_result
                )?;

                // Check make_thunk output env is effective_env.
                if_then!(
                    cs,
                    &make_thunk_was_called_and_cont_is_outermost,
                    &make_thunk_output_env_is_effective_env
                )?;

                // Check make_thunk output cont
                if_then!(
                    cs,
                    &make_thunk_was_called_and_cont_is_outermost,
                    &make_thunk_output_cont_is_terminal
                )?;

                let thunk_cont_is_neither_outermost_nor_tail = and!(
                    cs,
                    &Boolean::not(&thunk_cont_is_outermost),
                    &Boolean::not(&thunk_cont_is_tail)
                )?;

                let make_thunk_was_called_and_cont_is_neither_outermost_nor_tail = and!(
                    cs,
                    &make_thunk_was_called,
                    &thunk_cont_is_neither_outermost_nor_tail
                )?;

                if_then!(
                    cs,
                    &make_thunk_was_called_and_cont_is_neither_outermost_nor_tail,
                    &make_thunk_output_result_is_thunk
                )?;

                if_then!(
                    cs,
                    &make_thunk_was_called_and_cont_is_neither_outermost_nor_tail,
                    &thunk_thunk_value_is_make_thunk_result
                )?;

                let thunk_thunk_continuation_is_make_thunk_cont = tag_and_hash_equal!(
                    cs,
                    &the_thunk_cont_tag,
                    &make_thunk_cont_tag,
                    &the_thunk_cont_hash,
                    &make_thunk_cont_hash
                )?;

                if_then!(
                    cs,
                    &make_thunk_was_called_and_cont_is_neither_outermost_nor_tail,
                    &thunk_thunk_continuation_is_make_thunk_cont
                )?;

                if_then!(
                    cs,
                    &make_thunk_was_called_and_cont_is_neither_outermost_nor_tail,
                    &make_thunk_output_env_is_effective_env
                )?;

                if_then!(
                    cs,
                    &make_thunk_was_called_and_cont_is_neither_outermost_nor_tail,
                    &make_thunk_output_cont_is_dummy
                );
            }
            // End make_thunk handling
        }
        {
            // invoke_continuation

            let (invoke_continuation_cont_hash, invoke_continuation_cont_components) =
                if let Some(c) = &witness.invoke_continuation_cont {
                    c.allocate_components(cs.namespace(|| "invoke_continuation cont components"))?
                } else {
                    Continuation::allocate_dummy_components(
                        cs.namespace(|| "invoke_continuation output components"),
                    )?
                };
            ////////////////////////////////////////////////////////////

            let invoke_continuation_was_called_and_cont_is_terminal =
                and!(cs, &invoke_continuation_was_called, &input_cont_is_terminal)?;

            // invoke_continuation must never be called on a Terminal continuation.
            is_true!(
                cs,
                &Boolean::not(&invoke_continuation_was_called_and_cont_is_terminal)
            );

            ////////////////////////////////////////////////////////////
            let invoke_continuation_was_called_and_cont_is_dummy =
                and!(cs, &invoke_continuation_was_called, &input_cont_is_dummy)?;

            // invoke_continuation must never be called on a Dummy continuation.
            is_true!(
                cs,
                &Boolean::not(&invoke_continuation_was_called_and_cont_is_dummy)
            );

            ////////////////////////////////////////////////////////////
            let invoke_continuation_was_called_and_cont_is_simple =
                and!(cs, &invoke_continuation_was_called, &input_cont_is_simple)?;

            // invoke_continuation must never be called on a Simple continuation.
            is_true!(
                cs,
                &Boolean::not(&invoke_continuation_was_called_and_cont_is_simple)
            );

            ////////////////////////////////////////////////////////////
            let invoke_continuation_was_called_and_cont_is_outermost = and!(
                cs,
                &invoke_continuation_was_called,
                &input_cont_is_outermost
            )?;

            // TODO: If outermost and result is Thunk.
            let invoke_continuation_result_is_thunk =
                equal!(cs, &invoke_continuation_result_tag, &thunk_tag)?;

            let invoke_continuation_was_called_and_is_outermost_and_result_is_thunk = and!(
                cs,
                &invoke_continuation_was_called_and_cont_is_outermost,
                &invoke_continuation_result_is_thunk
            )?;

            let invoke_continuation_output_result_is_thunk =
                equal!(cs, &invoke_continuation_output_result_tag, &thunk_tag)?;

            if_then!(
                cs,
                &invoke_continuation_was_called_and_is_outermost_and_result_is_thunk,
                &invoke_continuation_output_result_is_thunk
            )?;

            let invoke_continuation_output_result_value_is_thunk_value = equal!(
                cs,
                &invoke_continuation_output_result_hash,
                &the_thunk_value_hash
            )?;

            if_then!(
                cs,
                &invoke_continuation_was_called_and_is_outermost_and_result_is_thunk,
                &invoke_continuation_output_result_value_is_thunk_value
            )?;

            ////////////////////////////////////////////////////////////
            let outermost_otherwise = and!(
                cs,
                &invoke_continuation_was_called_and_cont_is_outermost,
                &Boolean::not(&invoke_continuation_result_is_thunk)
            )?;

            let invoke_continuation_output_env_is_invoke_continuation_env = tag_and_hash_equal!(
                cs,
                &invoke_continuation_output_env_tag,
                &invoke_continuation_env_tag,
                &invoke_continuation_output_env_hash,
                &invoke_continuation_env_hash
            )?;

            if_then!(
                cs,
                &invoke_continuation_was_called_and_cont_is_outermost,
                &invoke_continuation_output_env_is_invoke_continuation_env
            )?;

            let invoke_continuation_output_cont_is_terminal =
                equal!(cs, &invoke_continuation_output_cont_tag, &terminal_cont_tag)?;

            if_then!(
                cs,
                &invoke_continuation_was_called_and_cont_is_outermost,
                &invoke_continuation_output_cont_is_terminal
            )?;

            ////////////////////////////////////////////////////////////
            let invoke_continuation_was_called_and_cont_is_call =
                and!(cs, &invoke_continuation_was_called, &input_cont_is_call)?;

            let invoke_continuation_was_called_and_cont_is_call_and_input_is_thunk = and!(
                cs,
                &invoke_continuation_was_called_and_cont_is_call,
                &input_is_thunk
            )?;

            // if_then!(
            //     cs,
            //     &invoke_continuation_was_called_and_cont_is_call_and_input_is_thunk,
            // )?;

            let invoke_continuation_was_called_and_cont_is_call2 =
                and!(cs, &invoke_continuation_was_called, &input_cont_is_call2)?;

            let invoke_continuation_was_called_and_cont_is_let_star =
                and!(cs, &invoke_continuation_was_called, &input_cont_is_let_star)?;

            let invoke_continuation_was_called_and_cont_is_let_rec_star = and!(
                cs,
                &invoke_continuation_was_called,
                &input_cont_is_let_rec_star
            )?;

            let invoke_continuation_was_called_and_cont_is_binop =
                and!(cs, &invoke_continuation_was_called, &input_cont_is_binop)?;

            let invoke_continuation_was_called_and_cont_is_binop2 =
                and!(cs, &invoke_continuation_was_called, &input_cont_is_binop2)?;

            let invoke_continuation_was_called_and_cont_is_relop =
                and!(cs, &invoke_continuation_was_called, &input_cont_is_relop)?;

            let invoke_continuation_was_called_and_cont_is_relop2 =
                and!(cs, &invoke_continuation_was_called, &input_cont_is_relop2)?;

            let invoke_continuation_was_called_and_cont_is_if =
                and!(cs, &invoke_continuation_was_called, &input_cont_is_if)?;
        }

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
            let input_is_num_or_fun_or_thunk = or!(cs, &input_is_num_or_fun, &input_is_thunk)?;
            or!(
                cs,
                &input_is_num_or_fun_or_thunk,
                &input_is_self_evaluating_sym
            )?
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

            // This and its dependencies are really just a sanity check leftover from earlier.
            // It can eventually be removed. Or, if kept, the make_thunk case can potentially
            // be optimized based on the assumption this is enforced.
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
        // Routing
        //

        // Actually, this is only true in some cases.

        let thunk_result_tag_is_input_tag = equal!(cs, &input_tag, &make_thunk_result_tag)?;
        let thunk_result_hash_is_input_hash = equal!(cs, &input_hash, &make_thunk_result_hash)?;

        let thunk_env_tag_is_input_env_tag = equal!(cs, &input_env_tag, &make_thunk_env_tag)?;
        let thunk_env_hash_is_input_env_hash = equal!(cs, &input_env_hash, &make_thunk_env_hash)?;

        let make_thunk_cont_tag_is_input_cont_tag =
            equal!(cs, &input_cont_tag, &make_thunk_cont_tag)?;
        let make_thunk_cont_hash_is_input_cont_hash =
            equal!(cs, &input_cont_hash, &make_thunk_cont_hash)?;

        // Enforce constraints on whether make_thunk was called and what its inputs were if so.
        if_then!(cs, &input_is_self_evaluating, &make_thunk_was_called)?;

        let make_thunk_was_called_and_input_is_self_evaluating =
            and!(cs, &make_thunk_was_called, &input_is_self_evaluating)?;

        if_then!(
            cs,
            &make_thunk_was_called_and_input_is_self_evaluating,
            &thunk_result_tag_is_input_tag
        )?;
        if_then!(
            cs,
            &make_thunk_was_called_and_input_is_self_evaluating,
            &thunk_result_hash_is_input_hash
        )?;

        if_then!(
            cs,
            &make_thunk_was_called_and_input_is_self_evaluating,
            &thunk_env_tag_is_input_env_tag
        )?;
        if_then!(
            cs,
            &make_thunk_was_called,
            &thunk_env_hash_is_input_env_hash
        )?;

        if_then!(
            cs,
            &make_thunk_was_called_and_input_is_self_evaluating,
            &make_thunk_cont_tag_is_input_cont_tag
        )?;
        if_then!(
            cs,
            &make_thunk_was_called_and_input_is_self_evaluating,
            &make_thunk_cont_hash_is_input_cont_hash
        )?;

        // TODO: Handle non-self-evaluating cases where make_thunk was called.

        // Output
        // make_thunk is always in tail position, so if it was called, its output is final output.

        let thunk_output_result_tag_is_output_tag =
            equal!(cs, &output_tag, &make_thunk_output_result_tag)?;
        let thunk_output_result_hash_is_output_hash =
            equal!(cs, &output_hash, &make_thunk_output_result_hash)?;

        let thunk_output_env_tag_is_output_env_tag =
            equal!(cs, &output_env_tag, &make_thunk_output_env_tag)?;
        let thunk_output_env_hash_is_output_env_hash =
            equal!(cs, &output_env_hash, &make_thunk_output_env_hash)?;

        let make_thunk_output_cont_tag_is_output_cont_tag =
            equal!(cs, &output_cont_tag, &make_thunk_output_cont_tag)?;
        let make_thunk_output_cont_hash_is_output_cont_hash =
            equal!(cs, &output_cont_hash, &make_thunk_output_cont_hash)?;

        if_then!(
            cs,
            &make_thunk_was_called,
            &thunk_output_result_tag_is_output_tag
        )?;
        if_then!(
            cs,
            &make_thunk_was_called,
            &thunk_output_result_hash_is_output_hash
        )?;

        if_then!(
            cs,
            &make_thunk_was_called,
            &thunk_output_env_tag_is_output_env_tag
        )?;
        if_then!(
            cs,
            &make_thunk_was_called,
            &thunk_output_env_hash_is_output_env_hash
        )?;

        if_then!(
            cs,
            &make_thunk_was_called,
            &make_thunk_output_cont_tag_is_output_cont_tag
        )?;
        if_then!(
            cs,
            &make_thunk_was_called,
            &make_thunk_output_cont_hash_is_output_cont_hash
        )?;

        ////////////////////////////////////////////////////////////////////////////////

        ////////////////////////////////////////////////////////////////////////////////
        // Handle input types

        // If Input is Nil.
        {
            if_then!(cs, &input_is_nil, &thunk_result_tag_is_input_tag)?;
            if_then!(cs, &input_is_nil, &thunk_result_hash_is_input_hash)?;

            // TODO: Branch on continuation type/tag to get effective output env.
            if_then!(cs, &input_is_nil, &thunk_env_tag_is_input_env_tag)?;
            if_then!(cs, &input_is_nil, &thunk_env_hash_is_input_env_hash)?;
        }

        // let input_is_cons = equal!(cs, &input_tag, &cons_tag)?;
        // let input_is_sym = equal!(cs, &input_tag, &sym_tag)?;
        // let input_is_fun = equal!(cs, &input_tag, &fun_tag)?;
        // let input_is_num = equal!(cs, &input_tag, &num_tag)?;
        // let input_is_thunk = equal!(cs, &input_tag, &thunk_tag)?;

        ////////////////////////////////////////////////////////////////////////////////
        // make_thunk
        //

        if_then!(cs, &output_is_thunk, &make_thunk_was_called)?;
        let output_is_thunk_or_output_cont_is_terminal =
            or!(cs, &output_is_thunk, &output_cont_is_terminal)?;
        if_then!(
            cs,
            &make_thunk_was_called,
            &output_is_thunk_or_output_cont_is_terminal
        )?;

        // let (cont_hash, cont_tag) = if let Some(cont) = witness.make_thunk_cont {
        //     let cont_hash = cont.get_hash();
        //     let cont_tag = AllocatedNum::alloc(cs.namespace(|| "make_thunk_cont tag"), || {
        //         Ok(cont.get_continuation_tag().cont_tag_fr())
        //     })?;

        //     // let h = poseidon_hash(cs.namespace(|| "contxxxx"), vec![cont_tag, ]);
        //     //todo!();
        //     (cont_hash, cont_tag)
        // } else {
        //     (Fr::zero(), Fr::zero())
        // };

        //
        ////////////////////////////////////////////////////////////////////////////////

        Ok(())
    }
}

impl Continuation {
    // FIXME: This needs to also prove the hash. Do it like Thunk::allocate_components below.
    fn allocate_components<CS: ConstraintSystem<Bls12>>(
        &self,
        mut cs: CS,
    ) -> Result<(AllocatedNum<Bls12>, Vec<AllocatedNum<Bls12>>), SynthesisError> {
        let component_frs = self.get_hash_components();
        let mut components = Vec::with_capacity(9);

        for (i, fr) in component_frs.iter().enumerate() {
            components.push(AllocatedNum::alloc(
                cs.namespace(|| format!("Continuation component {}", i)),
                || Ok(*fr),
            )?);
        }

        let hash = poseidon_hash(
            cs.namespace(|| "Continuation"),
            components.clone(),
            &POSEIDON_CONSTANTS_9,
        )?;

        Ok((hash, components))
    }

    fn allocate_dummy_components<CS: ConstraintSystem<Bls12>>(
        mut cs: CS,
    ) -> Result<(AllocatedNum<Bls12>, Vec<AllocatedNum<Bls12>>), SynthesisError> {
        let length = 9;
        let mut result = Vec::with_capacity(length);
        for i in 0..length {
            result.push(AllocatedNum::alloc(
                cs.namespace(|| format!("Continuation component {}", i)),
                || Ok(Fr::zero()),
            )?);
        }

        // We need to create these constraints, but eventually we can avoid doing any calculation.
        // We just need a precomputed dummy witness.
        let dummy_hash = poseidon_hash(
            cs.namespace(|| "Continuation"),
            result.clone(),
            &POSEIDON_CONSTANTS_9,
        )?;

        // let dummy_hash = AllocatedNum::alloc(cs.namespace(|| "Continuation"), || Ok(Fr::zero()))?;

        Ok((dummy_hash, result))
    }
}

impl Thunk {
    // First component is the hash, which is wrong.
    fn allocate_components<CS: ConstraintSystem<Bls12>>(
        &self,
        mut cs: CS,
    ) -> Result<(AllocatedNum<Bls12>, Vec<AllocatedNum<Bls12>>), SynthesisError> {
        let component_frs = self.get_hash_components();
        let mut components = Vec::with_capacity(4);

        for (i, fr) in component_frs.iter().enumerate() {
            components.push(AllocatedNum::alloc(
                cs.namespace(|| format!("Continuation component {}", i)),
                || Ok(*fr),
            )?);
        }

        let hash = poseidon_hash(
            cs.namespace(|| "make_thunk_tail_continuation_thunk"),
            components.clone(),
            &POSEIDON_CONSTANTS_4,
        )?;

        Ok((hash, components))
    }

    fn allocate_dummy_components<CS: ConstraintSystem<Bls12>>(
        mut cs: CS,
    ) -> Result<(AllocatedNum<Bls12>, Vec<AllocatedNum<Bls12>>), SynthesisError> {
        let length = 4;
        let mut result = Vec::with_capacity(length);
        for i in 0..length {
            result.push(AllocatedNum::alloc(
                cs.namespace(|| format!("Continuation component {}", i)),
                || Ok(Fr::zero()),
            )?);
        }
        let dummy_hash = poseidon_hash(
            cs.namespace(|| "make_thunk_tail_continuation_thunk"),
            result.clone(),
            &POSEIDON_CONSTANTS_4,
        )?;

        Ok((dummy_hash, result))
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

fn enforce_true<CS: ConstraintSystem<E>, E: Engine>(cs: CS, prop: &Boolean) {
    Boolean::enforce_equal(cs, &Boolean::Constant(true), prop).unwrap(); // FIXME: unwrap
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
        Boolean::Not(_) => panic!("Expected a non-negated Boolean."),
    }
}

fn alloc_equal<CS: ConstraintSystem<E>, E: Engine>(
    mut cs: CS,
    a: &AllocatedNum<E>,
    b: &AllocatedNum<E>,
) -> Result<Boolean, SynthesisError> {
    let equal = a.get_value() == b.get_value();

    // Difference between `a` and `b`. This will be zero if `a` and `b` are equal.
    let diff = constraints::sub(cs.namespace(|| "a - b"), a, b)?;

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
        |_| Boolean::Constant(true).lc(CS::one(), q),
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
    use crate::data::Store;
    use crate::eval::empty_sym_env;
    use bellperson::util_cs::test_cs::TestConstraintSystem;

    #[test]
    fn num_self_evaluating() {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let num = Expression::num(123);

        let mut input = IO {
            expr: num.clone(),
            env: env.clone(),
            cont: Continuation::Outermost,
            witness: None,
        };

        let initial = input.clone();
        input.ensure_witness(&mut store.clone());

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

            assert_eq!(3116, cs.num_constraints());
        };

        // Success
        {
            let output = IO {
                expr: num.clone(),
                env: env.clone(),
                cont: Continuation::Terminal,
                witness: None,
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
                    witness: None,
                };

                test_with_output(bad_output_tag, false);
            }
            {
                // Wrong value, so hash should differ.
                let bad_output_value = IO {
                    expr: Expression::num(999),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                    witness: None,
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

        let mut input = IO {
            expr: nil.clone(),
            env: env.clone(),
            cont: Continuation::Outermost,
            witness: None,
        };

        let initial = input.clone();
        input.ensure_witness(&mut store.clone());

        let mut test_with_output = |output, expect_success| {
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
                witness: None,
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
                    witness: None,
                };

                test_with_output(bad_output_tag, false);
            }
            {
                // Wrong value, so hash should differ.
                let bad_output_value = IO {
                    expr: Expression::num(999),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                    witness: None,
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

        let mut input = IO {
            expr: t.clone(),
            env: env.clone(),
            cont: Continuation::Outermost,
            witness: None,
        };

        let initial = input.clone();
        input.ensure_witness(&mut store.clone());

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
                witness: None,
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
                    witness: None,
                };

                test_with_output(bad_output_tag, false);
            }
            {
                // Wrong symbol, so hash should differ.
                let bad_output_value = IO {
                    expr: store.intern("S"),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                    witness: None,
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

        let mut input = IO {
            expr: fun.clone(),
            env: env.clone(),
            cont: Continuation::Outermost,
            witness: None,
        };

        let initial = input.clone();
        input.ensure_witness(&mut store.clone());

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
                witness: None,
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
                    witness: None,
                };

                test_with_output(bad_output_tag, false);
            }
            {
                // Wrong value, so hash should differ.
                let bad_output_value = IO {
                    expr: Expression::num(999),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                    witness: None,
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
        let mut input = IO {
            expr: expr.clone(),
            env: env.clone(),
            cont: Continuation::Outermost,
            witness: None,
        };

        let initial = input.clone();
        input.ensure_witness(&mut store.clone());

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
                    witness: None,
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
                    witness: None,
                };

                test_with_output(output, true);
            }
        }
    }
}
