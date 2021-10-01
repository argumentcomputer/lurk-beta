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

use crate::gadgets::case::{case, multi_case, CaseClause, CaseConstraint};

use crate::data::{
    fr_from_u64, BaseContinuationTag, Continuation, Expression, Tag, Tagged, Thunk,
    POSEIDON_CONSTANTS_4, POSEIDON_CONSTANTS_9,
};
use crate::eval::{Control, Frame, Witness, IO};
use crate::gadgets::constraints::{self, alloc_equal, alloc_is_zero, equal, or, pick};
use crate::gadgets::data::{allocate_constant, pick_tagged_hash, AllocatedTaggedHash};

pub trait Provable {
    fn public_inputs(&self) -> Vec<Fr>;
}

pub struct Proof<F: Provable> {
    _frame: F,
    groth16_proof: groth16::Proof<Bls12>,
}

impl<W: Copy> Provable for Frame<IO<W>> {
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

    todo!();
    // let vk = todo!();

    // verify_proof(vk, &p.groth16_proof, &inputs)
}

fn bind_input<CS: ConstraintSystem<Bls12>>(
    cs: &mut CS,
    expr: &Expression,
) -> Result<AllocatedTaggedHash<Bls12>, SynthesisError> {
    let tagged_hash = expr.tagged_hash();
    let tag = AllocatedNum::alloc(cs.namespace(|| "tag"), || Ok(tagged_hash.tag))?;
    tag.inputize(cs.namespace(|| "tag input"))?;

    let hash = AllocatedNum::alloc(cs.namespace(|| "hash"), || Ok(tagged_hash.hash))?;
    hash.inputize(cs.namespace(|| "hash input"))?;

    Ok(AllocatedTaggedHash::from_tag_and_hash(tag, hash))
}

fn bind_input_cont<CS: ConstraintSystem<Bls12>>(
    cs: &mut CS,
    cont: &Continuation,
) -> Result<AllocatedTaggedHash<Bls12>, SynthesisError> {
    let tag = AllocatedNum::alloc(cs.namespace(|| "continuation tag"), || {
        Ok(cont.get_continuation_tag().cont_tag_fr())
    })?;
    tag.inputize(cs.namespace(|| "continuation tag input"))?;

    let hash = AllocatedNum::alloc(cs.namespace(|| "continuation hash"), || Ok(cont.get_hash()))?;
    hash.inputize(cs.namespace(|| "continuation hash input"))?;

    Ok(AllocatedTaggedHash::from_tag_and_hash(tag, hash))
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

impl Circuit<Bls12> for Frame<IO<Witness>> {
    fn synthesize<CS: ConstraintSystem<Bls12>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let witness = self.output.witness.clone().unwrap();

        ////////////////////////////////////////////////////////////////////////////////
        // Bind public inputs.
        //
        // The frame's input:
        let input_expr = bind_input(&mut cs.namespace(|| "input expression"), &self.input.expr)?;

        let input_env = bind_input(&mut cs.namespace(|| "input env"), &self.input.env)?;

        let input_cont = bind_input_cont(&mut cs.namespace(|| "input cont"), &self.input.cont)?;

        // The frame's output:
        let output_expr = bind_input(&mut cs.namespace(|| "output expression"), &self.output.expr)?;

        let output_env = bind_input(&mut cs.namespace(|| "output env"), &self.output.env)?;

        let output_cont = bind_input_cont(&mut cs.namespace(|| "output cont"), &self.output.cont)?;

        // The initial input to the IVC computation.
        let initial_expr = bind_input(
            &mut cs.namespace(|| "initial expression"),
            &self.initial.expr,
        )?;

        let initial_env = bind_input(&mut cs.namespace(|| "initial env"), &self.initial.env)?;

        let initial_cont =
            bind_input_cont(&mut cs.namespace(|| "initial cont"), &self.initial.cont)?;

        // We don't currently need this, but we could expose access to it for logging, etc.
        // The frame counter:
        let frame_counter = cs.alloc_input(|| "frame counter", || Ok(fr_from_u64(self.i as u64)));
        //
        // End public inputs.
        ////////////////////////////////////////////////////////////////////////////////

        //        let (new_expr, new_env, new_cont) = evaluate_expression(
        let (new_expr, new_env, new_cont) = evaluate_expression(
            &mut cs.namespace(|| "evaluate expression"),
            &input_expr,
            &input_env,
            &input_cont,
            &self.output.witness.expect("witness missing"),
        )?;

        output_expr.enforce_equal(&mut cs.namespace(|| "output expr is correct"), &new_expr);
        output_env.enforce_equal(&mut cs.namespace(|| "output env is correct"), &new_env);
        output_cont.enforce_equal(&mut cs.namespace(|| "output cont is correct"), &new_cont);

        Ok(())
    }
}

fn evaluate_expression<CS: ConstraintSystem<Bls12>>(
    cs: &mut CS,
    expr: &AllocatedTaggedHash<Bls12>,
    env: &AllocatedTaggedHash<Bls12>,
    cont: &AllocatedTaggedHash<Bls12>,
    witness: &Witness,
) -> Result<
    (
        AllocatedTaggedHash<Bls12>,
        AllocatedTaggedHash<Bls12>,
        AllocatedTaggedHash<Bls12>,
    ),
    SynthesisError,
> {
    let mut result_expr_tag_clauses: Vec<CaseClause<Bls12>> = Vec::new();
    let mut result_expr_hash_clauses: Vec<CaseClause<Bls12>> = Vec::new();
    let mut result_env_tag_clauses: Vec<CaseClause<Bls12>> = Vec::new();
    let mut result_env_hash_clauses: Vec<CaseClause<Bls12>> = Vec::new();
    let mut result_cont_tag_clauses: Vec<CaseClause<Bls12>> = Vec::new();
    let mut result_cont_hash_clauses: Vec<CaseClause<Bls12>> = Vec::new();
    let mut result_make_thunk_clauses: Vec<CaseClause<Bls12>> = Vec::new();

    let mut add_clauses = |key,
                           (result_expr, result_env, result_cont, result_make_thunk): (
        AllocatedTaggedHash<Bls12>,
        AllocatedTaggedHash<Bls12>,
        AllocatedTaggedHash<Bls12>,
        AllocatedNum<Bls12>,
    )| {
        let add_clause = |mut clauses: &mut Vec<CaseClause<Bls12>>, value| {
            clauses.push(CaseClause { key, value })
        };

        add_clause(&mut result_expr_tag_clauses, result_expr.tag);
        add_clause(&mut result_expr_hash_clauses, result_expr.hash);

        add_clause(&mut result_env_tag_clauses, result_env.tag);
        add_clause(&mut result_env_hash_clauses, result_env.hash);

        add_clause(&mut result_cont_tag_clauses, result_cont.tag);
        add_clause(&mut result_cont_hash_clauses, result_cont.hash);

        add_clause(&mut result_make_thunk_clauses, result_make_thunk);
    };

    // add_clauses(Tag::Thunk.fr(), todo!());

    let true_num = allocate_constant(&mut cs.namespace(|| "true"), Fr::one())?;

    add_clauses(
        Tag::Nil.fr(),
        // make_thunk = true
        (cont.clone(), expr.clone(), env.clone(), true_num.clone()),
    );

    // add_clauses(Tag::Sym.fr(), todo!());

    add_clauses(
        Tag::Num.fr(),
        // make_thunk = true
        (cont.clone(), expr.clone(), env.clone(), true_num.clone()),
    );

    add_clauses(
        Tag::Fun.fr(),
        // make_thunk = true
        (cont.clone(), expr.clone(), env.clone(), true_num.clone()),
    );

    // add_clauses(Tag::Cons.fr(), todo!());

    let mut all_clauses = vec![
        result_expr_tag_clauses.as_slice(),
        result_expr_hash_clauses.as_slice(),
        result_env_tag_clauses.as_slice(),
        result_env_hash_clauses.as_slice(),
        result_cont_tag_clauses.as_slice(),
        result_cont_hash_clauses.as_slice(),
        result_make_thunk_clauses.as_slice(),
    ];

    // TODO: This might not be the right default for all cases below.
    let default = AllocatedNum::alloc(cs.namespace(|| "default"), || Ok(Fr::zero()))?;

    let case_results = multi_case(
        &mut cs.namespace(|| "input expr tag case"),
        &expr.tag,
        &all_clauses,
        &[
            default.clone(),
            default.clone(),
            default.clone(),
            default.clone(),
            default.clone(),
            default.clone(),
            default.clone(), // This does have to be zero = false.
        ],
    )?;

    let first_result_expr = tagged_hash_by_index(0, &case_results);
    let first_result_env = tagged_hash_by_index(1, &case_results);
    let first_result_cont = tagged_hash_by_index(2, &case_results);
    let first_result_make_thunk = &case_results[6];

    let make_thunk_boolean = Boolean::not(&alloc_is_zero(
        &mut cs.namespace(|| "make_thunk_is_zero"),
        first_result_make_thunk,
    )?);

    let thunk_results = make_thunk(
        &mut cs.namespace(|| "make_thunk"),
        &first_result_expr,
        &first_result_env,
        &first_result_cont,
        witness,
        // make_thunk_boolean.get_value().unwrap(),
    )?;

    let result_expr = pick_tagged_hash(
        &mut cs.namespace(|| "pick maybe make_thunk expr"),
        &make_thunk_boolean,
        &thunk_results.0,
        &first_result_expr,
    )?;

    let result_env = pick_tagged_hash(
        &mut cs.namespace(|| "pick maybe make_thunk env"),
        &make_thunk_boolean,
        &thunk_results.1,
        &first_result_env,
    )?;

    let result_cont = pick_tagged_hash(
        &mut cs.namespace(|| "pick maybe make_thunk cont"),
        &make_thunk_boolean,
        &thunk_results.2,
        &first_result_cont,
    )?;

    Ok((result_expr, result_env, result_cont))
}

fn make_thunk<CS: ConstraintSystem<Bls12>>(
    cs: &mut CS,
    cont: &AllocatedTaggedHash<Bls12>,
    result: &AllocatedTaggedHash<Bls12>,
    env: &AllocatedTaggedHash<Bls12>,
    witness: &Witness,
    // dummy: bool,
) -> Result<
    (
        AllocatedTaggedHash<Bls12>,
        AllocatedTaggedHash<Bls12>,
        AllocatedTaggedHash<Bls12>,
    ),
    SynthesisError,
> {
    let mut result_expr_tag_clauses: Vec<CaseClause<Bls12>> = Vec::new();
    let mut result_expr_hash_clauses: Vec<CaseClause<Bls12>> = Vec::new();
    let mut result_env_tag_clauses: Vec<CaseClause<Bls12>> = Vec::new();
    let mut result_env_hash_clauses: Vec<CaseClause<Bls12>> = Vec::new();
    let mut result_cont_tag_clauses: Vec<CaseClause<Bls12>> = Vec::new();
    let mut result_cont_hash_clauses: Vec<CaseClause<Bls12>> = Vec::new();

    let mut add_clauses = |key,
                           (result_expr, result_env, result_cont): (
        AllocatedTaggedHash<Bls12>,
        AllocatedTaggedHash<Bls12>,
        AllocatedTaggedHash<Bls12>,
    )| {
        let add_clause = |mut clauses: &mut Vec<CaseClause<Bls12>>, value| {
            clauses.push(CaseClause { key, value })
        };

        add_clause(&mut result_expr_tag_clauses, result_expr.tag);
        add_clause(&mut result_expr_hash_clauses, result_expr.hash);

        add_clause(&mut result_env_tag_clauses, result_env.tag);
        add_clause(&mut result_env_hash_clauses, result_env.hash);

        add_clause(&mut result_cont_tag_clauses, result_cont.tag);
        add_clause(&mut result_cont_hash_clauses, result_cont.hash);
    };

    // TODO: This will also be needed in invoke_continuation, so to save allocating there also,
    // we can do at top-level and pass in -- perhaps along with any other such constants.
    let terminal_tagged_hash = Continuation::Terminal
        .allocate_constant_tagged_hash(&mut cs.namespace(|| "terminal continuation"))?;

    let dummy_tagged_hash = Continuation::Dummy
        .allocate_constant_tagged_hash(&mut cs.namespace(|| "dummy continuation"))?;

    let dummy_value = allocate_constant(&mut cs.namespace(|| "arbitrary dummy"), Fr::zero())?;

    let thunk_tag = Tag::Thunk.allocate_constant(&mut cs.namespace(|| "thunk_tag"))?;
    let cons_tag = Tag::Cons.allocate_constant(&mut cs.namespace(|| "cons_tag"))?;

    let lookup_cont_tag =
        BaseContinuationTag::Lookup.allocate_constant(&mut cs.namespace(|| "lookup_cont_tag"))?;

    let tail_cont_tag =
        BaseContinuationTag::Tail.allocate_constant(&mut cs.namespace(|| "tail_cont_tag"))?;

    let (thunk_hash, thunk_components) = if let Some(thunk) = &witness.make_thunk_thunk {
        thunk.allocate_components(&mut cs.namespace(|| "thunk_components"))?
    } else {
        Thunk::allocate_dummy_components(&mut cs.namespace(|| "thunk_components"))?
    };
    let thunk_value_tag = &thunk_components[0];
    let thunk_value_hash = &thunk_components[1];
    let thunk_cont_tag = &thunk_components[2];
    let thunk_cont_hash = &thunk_components[3];

    add_clauses(
        BaseContinuationTag::Outermost.cont_tag_fr(),
        ((*result).clone(), (*env).clone(), terminal_tagged_hash),
    );

    let mut all_clauses = vec![
        result_expr_tag_clauses.as_slice(),
        result_expr_hash_clauses.as_slice(),
        result_env_tag_clauses.as_slice(),
        result_env_hash_clauses.as_slice(),
        result_cont_tag_clauses.as_slice(),
        result_cont_hash_clauses.as_slice(),
    ];

    // BOOKMARK/TODO: Continuation::Tail case.

    let defaults = {
        let thunk_hash = Thunk::hash_components(
            &mut cs.namespace(|| "thunk_hash"),
            &[
                result.tag.clone(),
                result.hash.clone(),
                cont.tag.clone(),
                cont.hash.clone(),
            ],
        )?;

        let result_expr_tag = thunk_tag;
        let result_expr_hash = thunk_hash;

        let effective_env = {
            let (witnessed_cont_hash, witnessed_cont_components) = if let Some(cont) =
                &witness.make_thunk_cont
            {
                cont.allocate_components(&mut cs.namespace(|| "cont components"))?
            } else {
                // If make_thunk was not effectivelycalled when evaluating, we need to have passed the relevant dummy values
                // generated here. So this allocation will need to move outside to the caller.
                Continuation::allocate_dummy_components(&mut cs.namespace(|| "cont components"))?
            };

            let witnessed_cont_tag = &witnessed_cont_components[0];

            equal(
                cs,
                || "witnessed cont tag equals cont tag",
                &witnessed_cont_tag,
                &cont.tag,
            );
            equal(
                cs,
                || "witnessed cont hash equals cont hash",
                &witnessed_cont_hash,
                &cont.hash,
            );

            let saved_env = AllocatedTaggedHash::from_tag_and_hash(
                witnessed_cont_components[1].clone(),
                witnessed_cont_components[2].clone(),
            );

            let cont_tag_is_lookup = alloc_equal(
                &mut cs.namespace(|| "cont_tag_is_lookup"),
                &witnessed_cont_tag,
                &lookup_cont_tag,
            )?;

            let cont_tag_is_tail = alloc_equal(
                &mut cs.namespace(|| "cont_tag_is_tail"),
                &witnessed_cont_tag,
                &tail_cont_tag,
            )?;

            let cont_tag_is_lookup_or_tail = or!(cs, &cont_tag_is_lookup, &cont_tag_is_tail)?;

            let effective_env = pick_tagged_hash(
                &mut cs.namespace(|| "effective_env"),
                &cont_tag_is_lookup_or_tail,
                &saved_env,
                env,
            )?;

            effective_env
        };

        let result_cont_tag = dummy_tagged_hash.tag;
        let result_cont_hash = dummy_tagged_hash.hash;
        let defaults = [
            result_expr_tag,
            result_expr_hash,
            effective_env.tag,
            effective_env.hash,
            result_cont_tag,
            result_cont_hash,
        ];
        defaults
    };

    let case_results = multi_case(
        &mut cs.namespace(|| "make_thunk continuation case"),
        &cont.tag,
        &all_clauses,
        &defaults,
    )?;

    let result_expr = tagged_hash_by_index(0, &case_results);
    let result_env = tagged_hash_by_index(1, &case_results);
    let result_cont = tagged_hash_by_index(2, &case_results);

    Ok((result_expr, result_env, result_cont))
}

fn invoke_continuation<CS>(
    cs: &mut CS,
    cont: &AllocatedTaggedHash<Bls12>,
    result: &AllocatedTaggedHash<Bls12>,
    env: &AllocatedTaggedHash<Bls12>,
    witness: &Witness,
) -> (
    AllocatedTaggedHash<Bls12>,
    AllocatedTaggedHash<Bls12>,
    AllocatedTaggedHash<Bls12>,
) {
    todo!()
}

fn tagged_hash_by_index(
    n: usize,
    case_results: &[AllocatedNum<Bls12>],
) -> AllocatedTaggedHash<Bls12> {
    AllocatedTaggedHash::from_tag_and_hash(
        case_results[n * 2].clone(),
        case_results[1 + n * 2].clone(),
    )
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

        let hash =
            Self::hash_components(cs.namespace(|| "Thunk Continuation"), &components.clone())?;

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
            cs.namespace(|| "Thunk Continuation"),
            result.clone(),
            &POSEIDON_CONSTANTS_4,
        )?;

        Ok((dummy_hash, result))
    }

    fn hash_components<CS: ConstraintSystem<Bls12>>(
        mut cs: CS,
        components: &[AllocatedNum<Bls12>],
    ) -> Result<AllocatedNum<Bls12>, SynthesisError> {
        assert_eq!(4, components.len());

        // This is a 'binary' hash but has arity 4 because of tag and hash components for each item.
        let hash = poseidon_hash(
            cs.namespace(|| "Thunk Continuation"),
            components.to_vec(),
            &POSEIDON_CONSTANTS_4,
        )?;

        Ok(hash)
    }
}

#[cfg(test)]

mod tests {
    use super::*;
    use crate::data::Store;
    use crate::eval::{empty_sym_env, Evaluable, Witness, IO};
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
        let witness = input.compute_witness(&mut store);

        let test_with_output = |output, expect_success| {
            let mut cs = TestConstraintSystem::new();

            let frame = Frame {
                input: input.clone(),
                output,
                initial: initial.clone(),
                i: 0,
            };

            frame.synthesize(&mut cs).expect("failed to synthesize");

            assert_eq!(1518, cs.num_constraints());

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
                witness: witness.clone(),
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
                    witness: witness.clone(),
                };

                test_with_output(bad_output_tag, false);
            }

            {
                // Wrong value, so hash should differ.
                let bad_output_value = IO {
                    expr: Expression::num(999),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                    witness: witness.clone(),
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
        let witness = input.compute_witness(&mut store);

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
                witness: witness.clone(),
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
                    witness: witness.clone(),
                };

                test_with_output(bad_output_tag, false);
            }
            {
                // Wrong value, so hash should differ.
                let bad_output_value = IO {
                    expr: Expression::num(999),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                    witness: witness.clone(),
                };

                test_with_output(bad_output_value, false);
            }
        }
    }

    //#[test]
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
        let witness = input.compute_witness(&mut store);

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
                witness: witness.clone(),
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
                    witness: witness.clone(),
                };

                test_with_output(bad_output_tag, false);
            }
            {
                // Wrong symbol, so hash should differ.
                let bad_output_value = IO {
                    expr: store.intern("S"),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                    witness: witness.clone(),
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
        let witness = input.compute_witness(&mut store);

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
                witness: witness.clone(),
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
                    witness: witness.clone(),
                };

                test_with_output(bad_output_tag, false);
            }
            {
                // Wrong value, so hash should differ.
                let bad_output_value = IO {
                    expr: Expression::num(999),
                    env: env.clone(),
                    cont: Continuation::Terminal,
                    witness: witness.clone(),
                };

                test_with_output(bad_output_value, false);
            }
        }
    }

    //#[test]
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
        let witness = input.compute_witness(&mut store);

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
                    witness: witness.clone(),
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
                    witness: witness.clone(),
                };

                test_with_output(output, true);
            }
        }
    }
}
