use bellperson::{
    gadgets::{
        boolean::{AllocatedBit, Boolean},
        num::AllocatedNum,
    },
    groth16::{self, verify_proof},
    Circuit, ConstraintSystem, SynthesisError,
};
use blstrs::{Bls12, Scalar as Fr};
use ff::{Field, PrimeField};
use generic_array::typenum::private::IsLessOrEqualPrivate;
use neptune::circuit::poseidon_hash;
use pairing_lib::Engine;
use rand::{RngCore, SeedableRng};
use rand_xorshift::XorShiftRng;
use std::marker::PhantomData;

use crate::gadgets::case::{case, multi_case, CaseClause, CaseConstraint};

use crate::data::{
    fr_from_u64, BaseContinuationTag, Continuation, Expression, Op1, Op2, Rel2, Store, Tag, Tagged,
    TaggedHash, Thunk, POSEIDON_CONSTANTS_4, POSEIDON_CONSTANTS_6, POSEIDON_CONSTANTS_8,
};
use crate::eval::{Control, Frame, Witness, IO};
use crate::gadgets::constraints::{
    self, alloc_equal, alloc_is_zero, enforce_implication, equal, implies, or, pick,
};
use crate::gadgets::data::{
    allocate_constant, pick_tagged_hash, AllocatedTaggedHash, GlobalAllocations,
};

fn bind_input<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    expr: &Option<Expression>,
) -> Result<AllocatedTaggedHash, SynthesisError> {
    let tagged_hash = expr.as_ref().map(|e| e.tagged_hash());
    let tag = AllocatedNum::alloc(cs.namespace(|| "tag"), || {
        tagged_hash
            .as_ref()
            .map(|th| th.tag)
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    tag.inputize(cs.namespace(|| "tag input"))?;

    let hash = AllocatedNum::alloc(cs.namespace(|| "hash"), || {
        tagged_hash
            .as_ref()
            .map(|th| th.hash)
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    hash.inputize(cs.namespace(|| "hash input"))?;

    Ok(AllocatedTaggedHash::from_tag_and_hash(tag, hash))
}

fn bind_input_cont<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    cont: &Option<Continuation>,
) -> Result<AllocatedTaggedHash, SynthesisError> {
    let tag = AllocatedNum::alloc(cs.namespace(|| "continuation tag"), || {
        cont.as_ref()
            .map(|c| c.get_continuation_tag().cont_tag_fr())
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    tag.inputize(cs.namespace(|| "continuation tag input"))?;

    let hash = AllocatedNum::alloc(cs.namespace(|| "continuation hash"), || {
        cont.as_ref()
            .map(|c| c.get_hash())
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    hash.inputize(cs.namespace(|| "continuation hash input"))?;

    Ok(AllocatedTaggedHash::from_tag_and_hash(tag, hash))
}

fn bind_tag_hash<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    expr: Option<Expression>,
) -> Result<(AllocatedNum<Fr>, AllocatedNum<Fr>), SynthesisError> {
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

fn bind_continuation_tag_hash<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    cont: Option<Continuation>,
) -> Result<(AllocatedNum<Fr>, AllocatedNum<Fr>), SynthesisError> {
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

impl Circuit<Fr> for Frame<IO, Witness> {
    fn synthesize<CS: ConstraintSystem<Fr>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        if let Some(w) = &self.witness {
            if let Some(s) = &w.store {
                if let Some(o) = &self.output {
                    dbg!(&s.write_expr_str(&o.expr));
                }
                if let Some(i) = &self.input {
                    dbg!(&s.write_expr_str(&i.expr));
                }
            }
        };
        ////////////////////////////////////////////////////////////////////////////////
        // Bind public inputs.
        //
        // The frame's input:
        let input_expr = bind_input(
            &mut cs.namespace(|| "input expression"),
            &self.input.as_ref().map(|input| input.expr.clone()),
        )?;

        let input_env = bind_input(
            &mut cs.namespace(|| "input env"),
            &self.input.as_ref().map(|input| input.env.clone()),
        )?;

        let input_cont = bind_input_cont(
            &mut cs.namespace(|| "input cont"),
            &self.input.as_ref().map(|input| input.cont.clone()),
        )?;

        // The frame's output:
        let output_expr = bind_input(
            &mut cs.namespace(|| "output expression"),
            &self.output.as_ref().map(|output| output.expr.clone()),
        )?;

        let output_env = bind_input(
            &mut cs.namespace(|| "output env"),
            &self.output.as_ref().map(|output| output.env.clone()),
        )?;

        let output_cont = bind_input_cont(
            &mut cs.namespace(|| "output cont"),
            &self.output.as_ref().map(|output| output.cont.clone()),
        )?;

        // The initial input to the IVC computation.
        let initial_expr = bind_input(
            &mut cs.namespace(|| "initial expression"),
            &self.initial.as_ref().map(|initial| initial.expr.clone()),
        )?;

        let initial_env = bind_input(
            &mut cs.namespace(|| "initial env"),
            &self.initial.as_ref().map(|initial| initial.env.clone()),
        )?;

        let initial_cont = bind_input_cont(
            &mut cs.namespace(|| "initial cont"),
            &self.initial.as_ref().map(|initial| initial.cont.clone()),
        )?;

        // We don't currently need this, but we could expose access to it for logging, etc.
        // The frame counter:
        let frame_counter = cs.alloc_input(
            || "frame counter",
            || {
                self.i
                    .map(|i| fr_from_u64(i as u64))
                    .ok_or(SynthesisError::AssignmentMissing)
            },
        );
        //
        // End public inputs.
        ////////////////////////////////////////////////////////////////////////////////

        let (new_expr, new_env, new_cont) = evaluate_expression(
            &mut cs.namespace(|| "evaluate expression"),
            &input_expr,
            &input_env,
            &input_cont,
            &self.witness,
        )?;

        output_expr.enforce_equal(&mut cs.namespace(|| "output expr is correct"), &new_expr);
        output_env.enforce_equal(&mut cs.namespace(|| "output env is correct"), &new_env);
        output_cont.enforce_equal(&mut cs.namespace(|| "output cont is correct"), &new_cont);
        dbg!(
            output_expr.tag.get_value(),
            output_expr.hash.get_value(),
            new_expr.tag.get_value(),
            new_expr.hash.get_value()
        );
        dbg!(
            output_env.tag.get_value(),
            output_env.hash.get_value(),
            new_env.tag.get_value(),
            new_env.hash.get_value()
        );
        dbg!(
            output_cont.tag.get_value(),
            output_cont.hash.get_value(),
            new_cont.tag.get_value(),
            new_cont.hash.get_value(),
        );

        Ok(())
    }
}

fn evaluate_expression<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    expr: &AllocatedTaggedHash,
    env: &AllocatedTaggedHash,
    cont: &AllocatedTaggedHash,
    witness: &Option<Witness>,
) -> Result<
    (
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedTaggedHash,
    ),
    SynthesisError,
> {
    dbg!("evaluate_expression");
    let store = if let Some(w) = witness {
        w.store.clone().expect("Store missing.")
    } else {
        Store::default()
    };
    dbg!(&expr.fetch_and_write_str(&store));
    dbg!(&env.fetch_and_write_str(&store));
    dbg!(
        &expr.tagged_hash().map(|x| x.tag),
        &expr.tagged_hash().map(|x| x.hash),
        &cont.tagged_hash().map(|x| x.tag),
        &cont.tagged_hash().map(|x| x.hash)
    );

    let global_allocations =
        GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), witness)?;
    let mut result_expr_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_expr_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_env_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_env_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_cont_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_cont_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_invoke_continuation_clauses: Vec<CaseClause<Fr>> = Vec::new();

    let mut add_clauses = |key,
                           (result_expr, result_env, result_cont, result_invoke_continuation): (
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedNum<Fr>,
    )| {
        let add_clause =
            |mut clauses: &mut Vec<CaseClause<Fr>>, value| clauses.push(CaseClause { key, value });

        add_clause(&mut result_expr_tag_clauses, result_expr.tag);
        add_clause(&mut result_expr_hash_clauses, result_expr.hash);

        add_clause(&mut result_env_tag_clauses, result_env.tag);
        add_clause(&mut result_env_hash_clauses, result_env.hash);

        add_clause(&mut result_cont_tag_clauses, result_cont.tag);
        add_clause(&mut result_cont_hash_clauses, result_cont.hash);

        add_clause(
            &mut result_invoke_continuation_clauses,
            result_invoke_continuation,
        );
    };

    {
        // Self-evaluating expressions

        add_clauses(
            Tag::Nil.fr(),
            (
                expr.clone(),
                env.clone(),
                cont.clone(),
                global_allocations.true_num.clone(),
            ),
        );

        add_clauses(
            Tag::Num.fr(),
            (
                expr.clone(),
                env.clone(),
                cont.clone(),
                global_allocations.true_num.clone(),
            ),
        );

        add_clauses(
            Tag::Fun.fr(),
            (
                expr.clone(),
                env.clone(),
                cont.clone(),
                global_allocations.true_num.clone(),
            ),
        );
    }

    {
        let (expr_thunk_hash, expr_thunk_value, expr_thunk_continuation) = expr
            .allocate_thunk_components(&mut cs.namespace(|| "allocate thunk components"), &store)?;

        // Enforce (expr.tag == thunk_tag) implies (expr_thunk_hash == expr.hash).
        let expr_is_a_thunk = constraints::alloc_equal(
            &mut cs.namespace(|| "expr.tag == thunk_tag"),
            &expr.tag,
            &global_allocations.thunk_tag,
        )?;
        let expr_is_the_thunk = constraints::alloc_equal(
            &mut cs.namespace(|| "thunk_hash == expr.hash"),
            &expr_thunk_hash,
            &expr.hash,
        )?;

        enforce_implication(
            &mut cs
                .namespace(|| "(expr.tag == thunk_continuation) implies (thunk_hash == expr.hash)"),
            &expr_is_a_thunk,
            &expr_is_the_thunk,
        );

        add_clauses(
            Tag::Thunk.fr(),
            (
                expr_thunk_value,
                env.clone(),
                expr_thunk_continuation,
                global_allocations.true_num.clone(),
            ),
        );
    }
    {
        let eval_sym_not_dummy = alloc_equal(
            &mut cs.namespace(|| "eval_sym_not_dummy"),
            &expr.tag,
            &global_allocations.sym_tag,
        )?;

        let (result, env, cont, invoke_cont) = eval_sym(
            &mut cs.namespace(|| "eval Sym"),
            expr,
            env,
            cont,
            &eval_sym_not_dummy,
            witness,
            &global_allocations,
        )?;

        add_clauses(Tag::Sym.fr(), (result, env, cont, invoke_cont));
    }

    {
        let eval_cons_not_dummy = alloc_equal(
            &mut cs.namespace(|| "eval_cons_not_dummy"),
            &expr.tag,
            &global_allocations.cons_tag,
        )?;

        let (result, env, cont, invoke_cont) = eval_cons(
            &mut cs.namespace(|| "eval Cons"),
            expr,
            env,
            cont,
            &eval_cons_not_dummy,
            witness,
            &global_allocations,
        )?;

        add_clauses(Tag::Cons.fr(), (result, env, cont, invoke_cont));
    }

    let all_clauses = [
        result_expr_tag_clauses.as_slice(),
        result_expr_hash_clauses.as_slice(),
        result_env_tag_clauses.as_slice(),
        result_env_hash_clauses.as_slice(),
        result_cont_tag_clauses.as_slice(),
        result_cont_hash_clauses.as_slice(),
        result_invoke_continuation_clauses.as_slice(),
    ];

    let case_results = multi_case(
        &mut cs.namespace(|| "input expr tag case"),
        &expr.tag,
        &all_clauses,
        &[
            global_allocations.default.clone(),
            global_allocations.default.clone(),
            global_allocations.default.clone(),
            global_allocations.default.clone(),
            global_allocations.default.clone(),
            global_allocations.default.clone(),
            global_allocations.false_num.clone(),
        ],
    )?;

    let first_result_expr = tagged_hash_by_index(0, &case_results);

    let first_result_env = tagged_hash_by_index(1, &case_results);
    let first_result_cont = tagged_hash_by_index(2, &case_results);
    let first_result_invoke_continuation: &AllocatedNum<Fr> = &case_results[6];

    let invoke_continuation_boolean = Boolean::not(&alloc_is_zero(
        &mut cs.namespace(|| "invoke_continuation_is_zero"),
        first_result_invoke_continuation,
    )?);

    let invoke_continuation_results = invoke_continuation(
        &mut cs.namespace(|| "invoke_continuation-make_thunk"),
        &first_result_cont,
        &first_result_expr,
        &first_result_env,
        &invoke_continuation_boolean,
        witness,
        &global_allocations,
    )?;

    let invoke_continuation_make_thunk: AllocatedNum<Fr> = invoke_continuation_results.3;

    let result_expr0 = pick_tagged_hash(
        &mut cs.namespace(|| "pick maybe invoke_continuation expr"),
        &invoke_continuation_boolean,
        &invoke_continuation_results.0,
        &first_result_expr,
    )?;

    let result_env0 = pick_tagged_hash(
        &mut cs.namespace(|| "pick maybe invoke_continuation env"),
        &invoke_continuation_boolean,
        &invoke_continuation_results.1,
        &first_result_env,
    )?;

    let result_cont0 = pick_tagged_hash(
        &mut cs.namespace(|| "pick maybe invoke_continuation cont"),
        &invoke_continuation_boolean,
        &invoke_continuation_results.2,
        &first_result_cont,
    )?;

    let make_thunk_num = pick(
        &mut cs.namespace(|| "pick make_thunk_boolean"),
        &invoke_continuation_boolean,
        &invoke_continuation_make_thunk,
        &global_allocations.false_num,
    )?;

    // True if make_thunk is called.
    let make_thunk_boolean = Boolean::not(&alloc_is_zero(
        &mut cs.namespace(|| "invoke_continuation_make_thunk is zero"),
        &make_thunk_num,
    )?);

    let thunk_results = make_thunk(
        &mut cs.namespace(|| "make_thunk"),
        &result_cont0,
        &result_expr0,
        &result_env0,
        &make_thunk_boolean,
        witness,
        &global_allocations,
    )?;

    let result_expr = pick_tagged_hash(
        &mut cs.namespace(|| "pick maybe make_thunk expr"),
        &make_thunk_boolean,
        &thunk_results.0,
        &result_expr0,
    )?;

    let result_env = pick_tagged_hash(
        &mut cs.namespace(|| "pick maybe make_thunk env"),
        &make_thunk_boolean,
        &thunk_results.1,
        &result_env0,
    )?;

    let result_cont = pick_tagged_hash(
        &mut cs.namespace(|| "pick maybe make_thunk cont"),
        &make_thunk_boolean,
        &thunk_results.2,
        &result_cont0,
    )?;

    Ok((result_expr, result_env, result_cont))
}

fn eval_sym<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    expr: &AllocatedTaggedHash,
    env: &AllocatedTaggedHash,
    cont: &AllocatedTaggedHash,
    not_dummy: &Boolean,
    witness: &Option<Witness>,
    g: &GlobalAllocations,
) -> Result<
    (
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedNum<Fr>,
    ),
    SynthesisError,
> {
    let store = if let Some(w) = witness {
        w.store.clone().expect("Store missing.")
    } else {
        Store::default()
    };
    let output_expr = Expression::allocate_tagged_hash(
        &mut cs.namespace(|| "output_expr"),
        witness
            .as_ref()
            .and_then(|w| w.prethunk_output_expr.clone()),
    )?;
    let output_env = Expression::allocate_tagged_hash(
        &mut cs.namespace(|| "output_env"),
        witness.as_ref().and_then(|w| w.prethunk_output_env.clone()),
    )?;
    let output_cont = Continuation::allocate_tagged_hash(
        &mut cs.namespace(|| "output_cont"),
        witness
            .as_ref()
            .and_then(|w| w.prethunk_output_cont.clone()),
    )?;

    let sym_is_nil = expr.alloc_equal(&mut cs.namespace(|| "sym is nil"), &g.nil_tagged_hash)?;
    let sym_is_t = expr.alloc_equal(&mut cs.namespace(|| "sym is t"), &g.t_tagged_hash)?;

    let sym_is_self_evaluating = or!(cs, &sym_is_nil, &sym_is_t)?;
    let sym_otherwise = Boolean::not(&sym_is_self_evaluating);

    let (binding, smaller_env) = car_cdr(
        &mut cs.namespace(|| "If unevaled_args cons"),
        g,
        env,
        &store,
    )?;

    let binding_is_nil =
        binding.alloc_equal(&mut cs.namespace(|| "binding is nil"), &g.nil_tagged_hash)?;

    let binding_not_nil = Boolean::not(&binding_is_nil);

    let otherwise_and_binding_is_nil = and!(cs, &sym_otherwise, &binding_is_nil)?;
    let otherwise_and_binding_not_nil = and!(cs, &sym_otherwise, &binding_not_nil)?;

    let (var_or_rec_binding, val_or_more_rec_env) =
        car_cdr(&mut cs.namespace(|| "car_cdr binding"), g, &binding, &store)?;

    let var_or_rec_binding_is_sym = alloc_equal(
        &mut cs.namespace(|| "var_or_rec_binding_is_sym"),
        &var_or_rec_binding.tag,
        &g.sym_tag,
    )?;

    let v = var_or_rec_binding.clone();
    let val = val_or_more_rec_env.clone();
    let v_is_expr1 = expr.alloc_equal(&mut cs.namespace(|| "v_is_expr1"), &v)?;
    let v_not_expr1 = Boolean::not(&v_is_expr1);

    let otherwise_and_sym = and!(cs, &v_not_expr1, &var_or_rec_binding_is_sym)?;
    let otherwise_and_v_expr_and_sym = and!(cs, &v_is_expr1, &var_or_rec_binding_is_sym)?;

    let v_is_expr1_real = and!(cs, &v_is_expr1, &otherwise_and_v_expr_and_sym)?;

    let var_or_rec_binding_is_cons = alloc_equal(
        &mut cs.namespace(|| "var_or_rec_binding_is_cons"),
        &var_or_rec_binding.tag,
        &g.cons_tag,
    )?;

    let otherwise_and_cons = and!(
        cs,
        &otherwise_and_binding_not_nil,
        &var_or_rec_binding_is_cons
    )?;

    let (v2, val2) = car_cdr(
        &mut cs.namespace(|| "car_cdr var_or_rec_binding"),
        g,
        &var_or_rec_binding,
        &store,
    )?;

    let val2_is_fun = alloc_equal(cs.namespace(|| "val2_is_fun"), &val2.tag, &g.fun_tag)?;
    let v2_is_expr = v2.alloc_equal(&mut cs.namespace(|| "v2_is_expr"), expr)?;
    let v2_is_expr_real = and!(cs, &v2_is_expr, &otherwise_and_cons)?;

    let v2_not_expr = Boolean::not(&v2_is_expr);
    let otherwise_and_v2_not_expr = and!(cs, &v2_not_expr, &otherwise_and_cons)?;

    let var_or_rec_binding_is_neither = Boolean::not(&or!(
        cs,
        &var_or_rec_binding_is_sym,
        &var_or_rec_binding_is_cons
    )?);

    let otherwise_neither = and!(
        cs,
        &var_or_rec_binding_is_neither,
        &otherwise_and_binding_not_nil
    )?;

    let invoke_cont_bool0 = or!(cs, &sym_is_self_evaluating, &v_is_expr1_real)?;
    let invoke_cont_bool = or!(cs, &invoke_cont_bool0, &v2_is_expr_real)?;

    let invoke_cont_num = ifx!(cs, &invoke_cont_bool, &g.true_num, &g.false_num)?;

    let cont_is_lookup = alloc_equal(
        &mut cs.namespace(|| "cont_is_lookup"),
        &cont.tag,
        &g.lookup_cont_tag,
    )?;

    let cont_is_lookup_sym = and!(cs, &cont_is_lookup, &otherwise_and_sym)?;
    let cont_not_lookup_sym = and!(cs, &Boolean::not(&cont_is_lookup), &otherwise_and_sym)?;

    let cont_is_lookup_cons = and!(cs, &cont_is_lookup, &otherwise_and_v2_not_expr)?;
    let cont_not_lookup_cons = and!(
        cs,
        &Boolean::not(&cont_is_lookup),
        &otherwise_and_v2_not_expr
    )?;

    let lookup_continuation = Continuation::construct(
        &mut cs.namespace(|| "lookup_continuation"),
        &g.lookup_cont_tag.clone(),
        // Mirrors Continuation::get_hash_components()
        &[
            env.tag.clone(),
            env.hash.clone(),
            cont.tag.clone(),
            cont.hash.clone(),
            g.default.clone(),
            g.default.clone(),
            g.default.clone(),
            g.default.clone(),
        ],
    )?;

    let rec_env = binding;
    let val2_is_fun = equal!(cs, &val2.tag, &g.fun_tag)?;

    let (fun_hash, fun_arg, fun_body, fun_closed_env) = Expression::allocate_maybe_fun(
        &mut cs.namespace(|| "extend closure"),
        witness.clone().and_then(|w| w.extended_closure),
    )?;

    let extended_env = Expression::construct_cons(
        &mut cs.namespace(|| "extended_env"),
        g,
        &rec_env,
        &fun_closed_env,
    )?;

    let extended_fun = Expression::construct_fun(
        &mut cs.namespace(|| "extended_fun"),
        g,
        &fun_arg,
        &fun_body,
        &extended_env,
    )?;

    let val_to_use = pick_tagged_hash(
        &mut cs.namespace(|| "val_to_use"),
        &val2_is_fun,
        &extended_fun,
        &val2,
    )?;

    let smaller_rec_env = val_or_more_rec_env;
    let smaller_rec_env_is_nil = smaller_rec_env.alloc_equal(
        &mut cs.namespace(|| "smaller_rec_env_is_nil"),
        &g.nil_tagged_hash,
    )?;

    let with_smaller_rec_env = Expression::construct_cons(
        &mut cs.namespace(|| "with_smaller_rec_env"),
        g,
        &smaller_rec_env,
        &smaller_env,
    )?;

    let env_to_use = ifx_t!(
        cs,
        &smaller_rec_env_is_nil,
        &smaller_env,
        &with_smaller_rec_env
    )?;

    let cs = &mut cs.namespace(|| "sym_is_self_evaluating");
    let cond1 = and!(cs, &sym_is_self_evaluating, not_dummy)?;

    // NOTE: The commented-out implies_equal lines in the rest of this function
    // indicate the natural structure of this translation from eval.rs.
    // In order to reduce constraints, duplicated results are factored out below,
    // but the original structure is left intact so it can be checked against
    // the manual optimization.
    {
        // implies_equal_t!(cs, &cond1, &output_expr, &expr);
        // implies_equal_t!(cs, &cond1, &output_env, &env);
        // implies_equal_t!(cs, &cond1, &output_cont, &cont);

        implies_equal_t!(cs, &cond1, &output_cont, &cont);
    }

    let cs = &mut cs.namespace(|| "otherwise_and_binding_is_nil");
    let cond2 = and!(cs, &otherwise_and_binding_is_nil, not_dummy)?;
    {
        // let cond = and!(cs, &otherwise_and_binding_is_nil, not_dummy)?;

        // implies_equal_t!(cs, &cond2, &output_expr, &expr);
        // implies_equal_t!(cs, &cond2, &output_env, &env);
        implies_equal_t!(cs, &cond2, &output_cont, &g.error_tagged_hash);
    }
    let cs = &mut cs.namespace(|| "v_is_expr1_real");

    let cond3 = and!(cs, &v_is_expr1_real, not_dummy)?;
    {
        implies_equal_t!(cs, &cond3, &output_expr, &val);
        // implies_equal_t!(cs, &cond3, &output_env, &env);
        // implies_equal_t!(cs, &cond3, &output_cont, &cont);
    }
    let cs = &mut cs.namespace(|| "cont_is_lookup_sym");
    let cond4 = and!(cs, &cont_is_lookup_sym, not_dummy)?;
    {
        // implies_equal_t!(cs, &cond4, &output_expr, &expr);
        implies_equal_t!(cs, &cond4, &output_env, &smaller_env);

        //implies_equal_t!(cs, &cond, &output_cont, &cont);
    }
    let cs = &mut cs.namespace(|| "cont_not_lookup_sym");
    let cond5 = and!(cs, &cont_not_lookup_sym, not_dummy)?;
    {
        // implies_equal_t!(cs, &cond5, &output_expr, &expr);
        implies_equal_t!(cs, &cond5, &output_env, &smaller_env);

        implies_equal_t!(cs, &cond5, &output_cont, &lookup_continuation);
    }

    let cs = &mut cs.namespace(|| "v2_is_expr_real");
    let cond6 = and!(cs, &v2_is_expr_real, not_dummy)?;
    {
        implies_equal_t!(cs, &cond6, &output_expr, &val_to_use);
        // implies_equal_t!(cs, &cond6, &output_env, &env);
        // implies_equal_t!(cs, &cond6, &output_cont, &cont);
    }

    let cs = &mut cs.namespace(|| "otherwise_and_v2_not_expr");
    let cond7 = and!(cs, &otherwise_and_v2_not_expr, not_dummy)?;
    {
        // implies_equal_t!(cs, &cond7, &output_expr, &expr);
        implies_equal_t!(cs, &cond7, &output_env, &env_to_use);
    }

    let cs = &mut cs.namespace(|| "cont_is_lookup_cons");
    let cond8 = and!(cs, &cont_is_lookup_cons, not_dummy)?;
    // {
    //     // implies_equal_t!(cs, &cond8, &output_cont, &cont);
    // }

    let cs = &mut cs.namespace(|| "cont_not_lookup_cons");
    let cond9 = and!(cs, &cont_not_lookup_cons, not_dummy)?;
    {
        implies_equal_t!(cs, &cond9, &output_cont, &lookup_continuation);
    }

    let cs = &mut cs.namespace(|| "otherwise_neither");
    let cond10 = and!(cs, &otherwise_neither, not_dummy)?;
    {
        // "Bad form"
        implies_equal_t!(cs, &cond10, &output_cont, &g.error_tagged_hash);
    }

    let conda = or!(cs, &cond1, &cond2)?; // cond1, cond2
    let condb = or!(cs, &cond4, &cond6)?; // cond4, cond6
    let condc = or!(cs, &conda, &cond8)?; // cond1, cond2, cond8

    let condx = or!(cs, &cond4, &cond5)?; // cond4, cond5
    let condy = or!(cs, &cond3, &cond6)?; // cond3, cond6

    // cond1, cond2, cond4, cond5 // cond_expr
    let cond_expr = or!(cs, &conda, &condx)?; // cond1, cond2, cond4, cond5
    implies_equal_t!(cs, &cond_expr, &output_expr, &expr);

    // cond1, cond2, cond3, cond6 // cond_env
    let cond_env = or!(cs, &conda, &condy)?; // cond1, cond2, cond3, cond6
    implies_equal_t!(cs, &cond_env, &output_env, &env);

    // cond1, cond3, cond4, cond6, cond // cond_cont
    let cond_cont = or!(cs, &condb, &condc)?; // cond1, cond2, cond4, cond6, cond8
    implies_equal_t!(cs, &cond_cont, &output_cont, &cont);

    Ok((output_expr, output_env, output_cont, invoke_cont_num))
}

fn eval_cons<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    expr: &AllocatedTaggedHash,
    env: &AllocatedTaggedHash,
    cont: &AllocatedTaggedHash,
    not_dummy: &Boolean,
    witness: &Option<Witness>,
    g: &GlobalAllocations,
) -> Result<
    (
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedNum<Fr>,
    ),
    SynthesisError,
> {
    let store = if let Some(w) = witness {
        w.store.clone().expect("Store missing.")
    } else {
        Store::default()
    };

    let lambda = g.lambda_tagged_hash.clone();
    let dummy_arg = g.dummy_arg_tagged_hash.clone();

    let lambda_hash = Expression::read_sym("LAMBDA").get_hash();
    let quote_hash = Expression::read_sym("QUOTE").get_hash();
    let letstar = Expression::read_sym("LET*");
    let letstar_t = letstar.allocate_constant_tagged_hash(&mut cs.namespace(|| "letstar_t"))?;
    let letstar_hash = letstar.get_hash();
    let letrecstar = Expression::read_sym("LETREC*");
    let letrecstar_t =
        letrecstar.allocate_constant_tagged_hash(&mut cs.namespace(|| "letrecstar"))?;
    let letrecstar_hash = letrecstar.get_hash();
    let cons_hash = Expression::read_sym("CAR").get_hash();
    let car_hash = Expression::read_sym("CAR").get_hash();
    let cdr_hash = Expression::read_sym("CDR").get_hash();
    let atom_hash = Expression::read_sym("ATOM").get_hash();
    let sum_hash = Expression::read_sym("+").get_hash();
    let diff_hash = Expression::read_sym("-").get_hash();
    let product_hash = Expression::read_sym("*").get_hash();
    let quotient_hash = Expression::read_sym("/").get_hash();
    let numequal_hash = Expression::read_sym("=").get_hash();
    let equal_hash = Expression::read_sym("EQ").get_hash();
    let current_env_hash = Expression::read_sym("CURRENT-ENV").get_hash();
    let if_hash = Expression::read_sym("IF").get_hash();

    let (head, rest) = car_cdr(&mut cs.namespace(|| "eval_cons expr"), g, expr, &store)?;

    let not_dummy = alloc_equal(&mut cs.namespace(|| "rest is cons"), &rest.tag, &g.cons_tag)?;

    let (arg1, more) = car_cdr(&mut cs.namespace(|| "car_cdr(rest)"), g, &rest, &store)?;

    let mut result_expr_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_expr_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_env_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_env_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_cont_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_cont_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_invoke_cont_clauses: Vec<CaseClause<Fr>> = Vec::new();

    let mut add_clauses = |key,
                           (result_expr, result_env, result_cont, invoke_cont): (
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedNum<Fr>,
    )| {
        let add_clause_aux =
            |mut clauses: &mut Vec<CaseClause<Fr>>, value| clauses.push(CaseClause { key, value });

        let add_clause = |mut tag_clauses: &mut Vec<CaseClause<Fr>>,
                          mut hash_clauses: &mut Vec<CaseClause<Fr>>,

                          expr: AllocatedTaggedHash| {
            add_clause_aux(tag_clauses, expr.tag);
            add_clause_aux(hash_clauses, expr.hash);
        };

        add_clause(
            &mut result_expr_tag_clauses,
            &mut result_expr_hash_clauses,
            result_expr,
        );
        add_clause(
            &mut result_env_tag_clauses,
            &mut result_env_hash_clauses,
            result_env,
        );
        add_clause(
            &mut result_cont_tag_clauses,
            &mut result_cont_hash_clauses,
            result_cont,
        );
        add_clause_aux(&mut result_invoke_cont_clauses, invoke_cont);
    };

    {
        // head == LAMBDA
        let (args, body) = (arg1.clone(), more.clone());
        let args_is_nil =
            args.alloc_equal(&mut cs.namespace(|| "args_is_nil"), &g.nil_tagged_hash)?;

        let not_dummy1 = Boolean::not(&args_is_nil);
        let not_dummy2 = Boolean::and(&mut cs.namespace(|| "not_dummy2"), &not_dummy, &not_dummy1)?;

        let (car_args, cdr_args) = car_cdr(&mut cs.namespace(|| "car_cdr args"), g, &args, &store)?;

        // FIXME: There maybe some cases where cdr_args is wrong/differs from eval.rs.

        let arg = pick_tagged_hash(
            &mut cs.namespace(|| "maybe dummy arg"),
            &args_is_nil,
            &g.dummy_arg_tagged_hash,
            &car_args,
        )?;

        let inner = Expression::construct_cons(&mut cs.namespace(|| "inner"), g, &cdr_args, &body)?;
        let l = Expression::construct_cons(&mut cs.namespace(|| "l"), g, &lambda, &inner)?;
        let cdr_args_is_nil =
            cdr_args.alloc_equal(&mut cs.namespace(|| "cdr_args_is_nil"), &g.nil_tagged_hash)?;

        let list = Expression::construct_list(&mut cs.namespace(|| "list"), g, &[l])?;
        let inner_body = pick_tagged_hash(
            &mut cs.namespace(|| "inner_body"),
            &cdr_args_is_nil,
            &body,
            &list,
        )?;

        let function =
            Expression::construct_fun(&mut cs.namespace(|| "function"), g, &arg, &inner_body, env)?;

        add_clauses(
            lambda_hash,
            (function, env.clone(), cont.clone(), g.true_num.clone()),
        );
    }
    {
        // head == QUOTE
        let (quoted, end) = (arg1.clone(), more.clone());

        add_clauses(
            quote_hash,
            (quoted, env.clone(), cont.clone(), g.true_num.clone()),
        );
    }
    {
        // head == LET*
        // or head == LETREC*

        let cs = &mut cs.namespace(|| "LET(REC)*");

        let (bindings, body) = (arg1.clone(), more.clone());
        let (body1, rest_body) = car_cdr(&mut cs.namespace(|| "car_cdr body"), g, &body, &store)?;
        let (binding1, rest_bindings) = car_cdr(
            &mut cs.namespace(|| "car_cdr bindings"),
            g,
            &bindings,
            &store,
        )?;
        let (var, more_vals) = car_cdr(
            &mut cs.namespace(|| "car_cdr binding1"),
            g,
            &binding1,
            &store,
        )?;
        let (val, end) = car_cdr(
            &mut cs.namespace(|| "car_cdr more_vals"),
            g,
            &more_vals,
            &store,
        )?;

        // FIXME: assert end == NIL
        let expanded1 = Expression::construct_list(
            &mut cs.namespace(|| ""),
            g,
            &[letstar_t, rest_bindings.clone(), body1.clone()],
        )?;
        let bindings_is_nil =
            bindings.alloc_equal(&mut cs.namespace(|| "bindings_is_nil"), &g.nil_tagged_hash)?;

        let rest_bindings_is_nil = rest_bindings.alloc_equal(
            &mut cs.namespace(|| "rest_bindings_is_nil"),
            &g.nil_tagged_hash,
        )?;
        let expanded = pick_tagged_hash(
            &mut cs.namespace(|| "expanded"),
            &rest_bindings_is_nil,
            &body1,
            &expanded1,
        )?;

        let continuation1_letstar = Continuation::construct(
            &mut cs.namespace(|| "let* continuation"),
            &g.letstar_cont_tag,
            &[
                var.tag.clone(),
                var.hash.clone(),
                expanded.tag.clone(),
                expanded.hash.clone(),
                env.tag.clone(),
                env.hash.clone(),
                cont.tag.clone(),
                cont.hash.clone(),
            ],
        )?;

        let continuation_letstar = pick_tagged_hash(
            &mut cs.namespace(|| "continuation let*"),
            &bindings_is_nil,
            cont,
            &continuation1_letstar,
        )?;

        let continuation1_letrecstar = Continuation::construct(
            &mut cs.namespace(|| "letrec* continuation"),
            &g.letrecstar_cont_tag,
            &[
                var.tag.clone(),
                var.hash,
                expanded.tag.clone(),
                expanded.hash,
                env.tag.clone(),
                env.hash.clone(),
                cont.tag.clone(),
                cont.hash.clone(),
            ],
        )?;

        let continuation_letrecstar = pick_tagged_hash(
            &mut cs.namespace(|| "continuation letrec*"),
            &bindings_is_nil,
            cont,
            &continuation1_letrecstar,
        )?;

        let ret = pick_tagged_hash(&mut cs.namespace(|| "ret"), &bindings_is_nil, &body1, &val)?;

        add_clauses(
            letstar_hash,
            (
                val.clone(),
                env.clone(),
                continuation_letstar,
                g.false_num.clone(),
            ),
        );
        add_clauses(
            letrecstar_hash,
            (
                val,
                env.clone(),
                continuation_letrecstar,
                g.false_num.clone(),
            ),
        );
    }
    {
        // head == CONS

        let continuation = Continuation::construct(
            &mut cs.namespace(|| "binop cons"),
            &g.binop_cont_tag,
            &[
                g.op2_cons_tag.clone(),
                g.default.clone(),
                env.tag.clone(),
                env.hash.clone(),
                more.tag.clone(),
                more.hash.clone(),
                cont.tag.clone(),
                cont.hash.clone(),
            ],
        )?;

        add_clauses(
            cons_hash,
            (arg1.clone(), env.clone(), continuation, g.false_num.clone()),
        );
    }
    {
        // head == CAR
        let end = more.clone();
        // FIXME: Error if end != NIL.

        // TODO: Factor out the hashing involved in constructing the continuation,
        // since it happens in many of the branches here.
        let continuation = Continuation::construct(
            &mut cs.namespace(|| "unop car"),
            &g.unop_cont_tag,
            &[
                g.op1_car_tag.clone(),
                g.default.clone(),
                arg1.tag.clone(),
                arg1.hash.clone(),
                env.tag.clone(),
                env.hash.clone(),
                g.default.clone(),
                g.default.clone(),
            ],
        )?;

        add_clauses(
            car_hash,
            (arg1.clone(), env.clone(), continuation, g.false_num.clone()),
        );
    }
    {
        // head == CDR
        // FIXME: Error if end != NIL.

        let continuation = Continuation::construct(
            &mut cs.namespace(|| "unop cdr"),
            &g.unop_cont_tag,
            &[
                g.op1_cdr_tag.clone(),
                g.default.clone(),
                arg1.tag.clone(),
                arg1.hash.clone(),
                env.tag.clone(),
                env.hash.clone(),
                g.default.clone(),
                g.default.clone(),
            ],
        )?;

        add_clauses(
            cdr_hash,
            (arg1.clone(), env.clone(), continuation, g.false_num.clone()),
        );
    }
    {
        // head == ATOM
        // FIXME: Error if end != NIL.

        let continuation = Continuation::construct(
            &mut cs.namespace(|| "unop atom"),
            &g.unop_cont_tag,
            &[
                g.op1_atom_tag.clone(),
                g.default.clone(),
                arg1.tag.clone(),
                arg1.hash.clone(),
                env.tag.clone(),
                env.hash.clone(),
                g.default.clone(),
                g.default.clone(),
            ],
        )?;

        add_clauses(
            atom_hash,
            (arg1.clone(), env.clone(), continuation, g.false_num.clone()),
        );
    }
    {
        // head == +

        let continuation = Continuation::construct(
            &mut cs.namespace(|| "binop sum"),
            &g.binop_cont_tag,
            &[
                g.op2_sum_tag.clone(),
                g.default.clone(),
                env.tag.clone(),
                env.hash.clone(),
                more.tag.clone(),
                more.hash.clone(),
                cont.tag.clone(),
                cont.hash.clone(),
            ],
        )?;

        add_clauses(
            sum_hash,
            (arg1.clone(), env.clone(), continuation, g.false_num.clone()),
        );
    }
    {
        // head == -

        let continuation = Continuation::construct(
            &mut cs.namespace(|| "binop diff"),
            &g.binop_cont_tag,
            &[
                g.op2_diff_tag.clone(),
                g.default.clone(),
                env.tag.clone(),
                env.hash.clone(),
                more.tag.clone(),
                more.hash.clone(),
                cont.tag.clone(),
                cont.hash.clone(),
            ],
        )?;

        add_clauses(
            diff_hash,
            (arg1.clone(), env.clone(), continuation, g.false_num.clone()),
        );
    }
    {
        // head == *
        let continuation = Continuation::construct(
            &mut cs.namespace(|| "binop product"),
            &g.binop_cont_tag,
            &[
                g.op2_product_tag.clone(),
                g.default.clone(),
                env.tag.clone(),
                env.hash.clone(),
                more.tag.clone(),
                more.hash.clone(),
                cont.tag.clone(),
                cont.hash.clone(),
            ],
        )?;

        add_clauses(
            product_hash,
            (arg1.clone(), env.clone(), continuation, g.false_num.clone()),
        );
    }
    {
        // head == /

        let continuation = Continuation::construct(
            &mut cs.namespace(|| "binop quotient"),
            &g.binop_cont_tag,
            &[
                g.op2_quotient_tag.clone(),
                g.default.clone(),
                env.tag.clone(),
                env.hash.clone(),
                more.tag.clone(),
                more.hash.clone(),
                cont.tag.clone(),
                cont.hash.clone(),
            ],
        )?;

        add_clauses(
            quotient_hash,
            (arg1.clone(), env.clone(), continuation, g.false_num.clone()),
        );
    }
    {
        // head == =

        let continuation = Continuation::construct(
            &mut cs.namespace(|| "Relop NumEqual"),
            &g.relop_cont_tag,
            &[
                g.rel2_numequal_tag.clone(),
                g.default.clone(),
                env.tag.clone(),
                env.hash.clone(),
                more.tag.clone(),
                more.hash.clone(),
                cont.tag.clone(),
                cont.hash.clone(),
            ],
        )?;

        add_clauses(
            numequal_hash,
            (arg1.clone(), env.clone(), continuation, g.false_num.clone()),
        );
    }
    {
        // head == EQ

        let continuation = Continuation::construct(
            &mut cs.namespace(|| "Relop Equal"),
            &g.relop_cont_tag,
            &[
                g.rel2_equal_tag.clone(),
                g.default.clone(),
                env.tag.clone(),
                env.hash.clone(),
                more.tag.clone(),
                more.hash.clone(),
                cont.tag.clone(),
                cont.hash.clone(),
            ],
        )?;

        add_clauses(
            equal_hash,
            (arg1.clone(), env.clone(), continuation, g.false_num.clone()),
        );
    }
    {
        // head == IF

        let condition = arg1.clone();
        let unevaled_args = more.clone();

        let continuation = Continuation::construct(
            &mut cs.namespace(|| "If"),
            &g.if_cont_tag,
            &[
                unevaled_args.tag.clone(),
                unevaled_args.hash,
                cont.tag.clone(),
                cont.hash.clone(),
                g.default.clone(),
                g.default.clone(),
                g.default.clone(),
                g.default.clone(),
            ],
        )?;

        add_clauses(
            if_hash,
            (condition, env.clone(), continuation, g.false_num.clone()),
        );
    }
    {
        // head == CURRENT-ENV
        // FIXME: Error if rest != NIL.

        add_clauses(
            current_env_hash,
            (env.clone(), env.clone(), cont.clone(), g.true_num.clone()),
        );
    }
    let defaults = {
        // head == (FN . ARGS)

        let fun_form = head.clone();
        let args = rest;

        let call_continuation = Continuation::construct(
            &mut cs.namespace(|| "Call"),
            &g.call_cont_tag,
            &[
                env.tag.clone(),
                env.hash.clone(),
                arg1.tag.clone(),
                arg1.hash.clone(),
                cont.tag.clone(),
                cont.hash.clone(),
                g.default.clone(),
                g.default.clone(),
            ],
        )?;

        let expanded_inner = Expression::construct_list(
            &mut cs.namespace(|| "expanded_inner"),
            g,
            &[fun_form.clone(), arg1],
        )?;

        let expanded = Expression::construct_cons(
            &mut cs.namespace(|| "expanded"),
            g,
            &expanded_inner,
            &more,
        )?;

        let more_args_is_nil =
            more.alloc_equal(&mut cs.namespace(|| "more_args_is_nil"), &g.nil_tagged_hash)?;

        let res = pick_tagged_hash(
            &mut cs.namespace(|| "pick res"),
            &more_args_is_nil,
            &fun_form,
            &expanded,
        )?;

        let continuation = pick_tagged_hash(
            &mut cs.namespace(|| "pick continuation"),
            &more_args_is_nil,
            &call_continuation,
            cont,
        )?;

        let env = env.clone();
        &[
            res.tag,
            res.hash,
            env.tag,
            env.hash,
            continuation.tag,
            continuation.hash,
            g.false_num.clone(),
        ]
    };

    let all_clauses = [
        result_expr_tag_clauses.as_slice(),
        result_expr_hash_clauses.as_slice(),
        result_env_tag_clauses.as_slice(),
        result_env_hash_clauses.as_slice(),
        result_cont_tag_clauses.as_slice(),
        result_cont_hash_clauses.as_slice(),
        result_invoke_cont_clauses.as_slice(),
    ];

    let case_results = multi_case(
        &mut cs.namespace(|| "input expr hash case"),
        &head.hash,
        &all_clauses,
        defaults,
    )?;

    let result_expr = tagged_hash_by_index(0, &case_results);
    let result_env = tagged_hash_by_index(1, &case_results);
    let result_cont = tagged_hash_by_index(2, &case_results);
    let result_invoke_cont: &AllocatedNum<Fr> = &case_results[6];

    Ok((
        result_expr,
        result_env,
        result_cont,
        result_invoke_cont.clone(),
    ))
}

fn make_thunk<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    cont: &AllocatedTaggedHash,
    result: &AllocatedTaggedHash,
    env: &AllocatedTaggedHash,
    not_dummy: &Boolean,
    witness: &Option<Witness>,
    global_allocations: &GlobalAllocations,
) -> Result<
    (
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedTaggedHash,
    ),
    SynthesisError,
> {
    let store = if let Some(w) = witness {
        w.store.clone().expect("Store missing")
    } else {
        Store::default()
    };

    let mut result_expr_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_expr_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_env_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_env_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_cont_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_cont_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();

    let mut add_clauses = |key,
                           (result_expr, result_env, result_cont): (
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedTaggedHash,
    )| {
        let add_clause_aux =
            |mut clauses: &mut Vec<CaseClause<Fr>>, value| clauses.push(CaseClause { key, value });
        let add_clause = |mut tag_clauses: &mut Vec<CaseClause<Fr>>,
                          mut hash_clauses: &mut Vec<CaseClause<Fr>>,
                          expr: AllocatedTaggedHash| {
            add_clause_aux(tag_clauses, expr.tag);
            add_clause_aux(hash_clauses, expr.hash);
        };

        add_clause(
            &mut result_expr_tag_clauses,
            &mut result_expr_hash_clauses,
            result_expr,
        );
        add_clause(
            &mut result_env_tag_clauses,
            &mut result_env_hash_clauses,
            result_env,
        );
        add_clause(
            &mut result_cont_tag_clauses,
            &mut result_cont_hash_clauses,
            result_cont,
        );
    };

    let (computed_cont_hash, cont_components) = Continuation::allocate_maybe_dummy_components(
        &mut cs.namespace(|| "cont components"),
        &witness.clone().and_then(|w| w.make_thunk_cont),
        // FIXME AAA: It would be better if the following (commented-out) code worked.
        // For some reason, sometimes the relevant continuation disappears from the store,
        // even though having been observably added during evaluation.
        //
        // &cont
        // .tagged_hash()
        // .and_then(|c| store.fetch_continuation(&c)),
    )?;

    implies_equal!(cs, not_dummy, &computed_cont_hash, &cont.hash);

    // Otherwise, these are the results.
    let tail_results: (
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedTaggedHash,
    ) = {
        // Applies to Tail continuations only.
        let saved_env = tagged_hash_by_index(0, &cont_components);

        // Applies to Tail continuations
        let continuation = tagged_hash_by_index(1, &cont_components);

        let cont_is_tail = alloc_equal(
            &mut cs.namespace(|| "cont_is_tail"),
            &cont.tag,
            &global_allocations.tail_cont_tag,
        )?;

        let thunk_hash = Thunk::hash_components(
            &mut cs.namespace(|| "tail thunk_hash"),
            &[
                result.tag.clone(),
                result.hash.clone(),
                continuation.tag.clone(),
                continuation.hash,
            ],
        )?;

        let result_expr = AllocatedTaggedHash::from_tag_and_hash(
            global_allocations.thunk_tag.clone(),
            thunk_hash,
        );

        (
            result_expr,
            saved_env,
            global_allocations.dummy_tagged_hash.clone(),
        )
    };

    add_clauses(BaseContinuationTag::Tail.cont_tag_fr(), tail_results);

    add_clauses(
        BaseContinuationTag::Outermost.cont_tag_fr(),
        (
            (*result).clone(),
            (*env).clone(),
            global_allocations.terminal_tagged_hash.clone(),
        ),
    );

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
        [
            global_allocations.thunk_tag.clone(),
            thunk_hash,
            env.tag.clone(),
            env.hash.clone(),
            global_allocations.dummy_tagged_hash.tag.clone(),
            global_allocations.dummy_tagged_hash.hash.clone(),
        ]
    };

    let all_clauses = [
        result_expr_tag_clauses.as_slice(),
        result_expr_hash_clauses.as_slice(),
        result_env_tag_clauses.as_slice(),
        result_env_hash_clauses.as_slice(),
        result_cont_tag_clauses.as_slice(),
        result_cont_hash_clauses.as_slice(),
    ];

    let case_results = multi_case(
        &mut cs.namespace(|| "make_thunk case"),
        &cont.tag,
        &all_clauses,
        &defaults,
    )?;

    let result_expr = tagged_hash_by_index(0, &case_results);
    let result_env = tagged_hash_by_index(1, &case_results);
    let result_cont = tagged_hash_by_index(2, &case_results);

    Ok((result_expr, result_env, result_cont))
}

fn invoke_continuation<CS: ConstraintSystem<Fr>>(
    mut cs: CS,
    cont: &AllocatedTaggedHash,
    result: &AllocatedTaggedHash,
    env: &AllocatedTaggedHash,
    not_dummy: &Boolean,
    witness: &Option<Witness>,
    global_allocations: &GlobalAllocations,
) -> Result<
    (
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedNum<Fr>,
    ),
    SynthesisError,
> {
    let store = if let Some(w) = witness {
        w.store.clone().expect("Store missing")
    } else {
        Store::default()
    };

    let mut result_expr_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_expr_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_env_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_env_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_cont_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_cont_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_make_thunk_num_clauses: Vec<CaseClause<Fr>> = Vec::new();

    let defaults = [
        global_allocations.default.clone(),
        global_allocations.default.clone(),
        global_allocations.default.clone(),
        global_allocations.default.clone(),
        global_allocations.default.clone(),
        global_allocations.default.clone(),
        global_allocations.false_num.clone(),
    ];

    let mut add_clauses = |key,
                           (result_expr, result_env, result_cont, make_thunk_num): (
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedNum<Fr>,
    )| {
        let add_clause_aux =
            |mut clauses: &mut Vec<CaseClause<Fr>>, value| clauses.push(CaseClause { key, value });

        let add_clause = |mut tag_clauses: &mut Vec<CaseClause<Fr>>,
                          mut hash_clauses: &mut Vec<CaseClause<Fr>>,
                          expr: AllocatedTaggedHash| {
            add_clause_aux(tag_clauses, expr.tag);
            add_clause_aux(hash_clauses, expr.hash);
        };

        add_clause(
            &mut result_expr_tag_clauses,
            &mut result_expr_hash_clauses,
            result_expr,
        );
        add_clause(
            &mut result_env_tag_clauses,
            &mut result_env_hash_clauses,
            result_env,
        );
        add_clause(
            &mut result_cont_tag_clauses,
            &mut result_cont_hash_clauses,
            result_cont,
        );
        add_clause_aux(&mut result_make_thunk_num_clauses, make_thunk_num);
    };

    // FIXME: Handle Terminal and Dummy continuations,
    // which should return Error continuations, but what else?
    // We need to specify this.

    {
        let thunk_continuation = global_allocations.destructured_thunk_continuation.clone();
        let thunk_value = global_allocations.destructured_thunk_value.clone();
        let thunk_hash = global_allocations.destructured_thunk_hash.clone();

        // Enforce (result.tag == thunk_tag) implies (thunk_hash == result.hash).
        let result_is_a_thunk = constraints::alloc_equal(
            &mut cs.namespace(|| "result.tag == thunk_tag"),
            &result.tag,
            &global_allocations.thunk_tag,
        )?;
        let result_is_the_thunk = constraints::alloc_equal(
            &mut cs.namespace(|| "thunk_hash = result.hash"),
            &thunk_hash,
            &result.hash,
        )?;
        enforce_implication(
            &mut cs.namespace(|| {
                "(result.tag == thunk_continuation) implies (thunk_hash == result.hash)"
            }),
            &result_is_a_thunk,
            &result_is_the_thunk,
        );

        let picked = pick_tagged_hash(
            &mut cs.namespace(|| "pick result or thunk"),
            &result_is_a_thunk,
            &thunk_value,
            result,
        )?;

        add_clauses(
            BaseContinuationTag::Outermost.cont_tag_fr(),
            (
                picked,
                env.clone(),
                global_allocations.terminal_tagged_hash.clone(),
                global_allocations.false_num.clone(),
            ),
        );
    }

    let (continuation_hash, continuation_components) =
        Continuation::allocate_maybe_dummy_components(
            &mut cs.namespace(|| "allocate_continuation_components"),
            &witness.clone().and_then(|w| w.invoke_continuation_cont),
        )?;

    {
        // Continuation::Call
        let saved_env = tagged_hash_by_index(0, &continuation_components);
        let arg = tagged_hash_by_index(1, &continuation_components);
        let continuation = tagged_hash_by_index(2, &continuation_components);

        let function = result;
        let next_expr = arg;

        let call2_components = [global_allocations.call2_cont_tag.clone()];
        let newer_cont = Continuation::construct(
            &mut cs.namespace(|| "construct newer_cont"),
            &global_allocations.call2_cont_tag.clone(),
            // Mirrors Continuation::get_hash_components()
            &[
                saved_env.tag,
                saved_env.hash,
                function.tag.clone(),
                function.hash.clone(),
                continuation.tag,
                continuation.hash,
                global_allocations.default.clone(),
                global_allocations.default.clone(),
            ],
        )?;

        let result_is_fun = alloc_equal(
            cs.namespace(|| "result_is_fun"),
            &result.tag,
            &global_allocations.fun_tag,
        )?;

        let next = pick_tagged_hash(
            &mut cs.namespace(|| "call_next"),
            &result_is_fun,
            &next_expr,
            result,
        )?;

        let the_cont = pick_tagged_hash(
            &mut cs.namespace(|| "call_cont"),
            &result_is_fun,
            &newer_cont,
            &global_allocations.error_tagged_hash,
        )?;

        add_clauses(
            BaseContinuationTag::Call.cont_tag_fr(),
            (
                next,
                env.clone(),
                the_cont,
                global_allocations.false_num.clone(),
            ),
        );
    }
    {
        // Continuation::Call2
        let saved_env = tagged_hash_by_index(0, &continuation_components);
        let fun = tagged_hash_by_index(1, &continuation_components);
        let continuation = tagged_hash_by_index(2, &continuation_components);
        {
            let (hash, arg_t, body_t, closed_env) = Expression::allocate_maybe_fun(
                &mut cs.namespace(|| "allocate Call2 fun"),
                fun.tagged_hash().as_ref().and_then(|t| store.fetch(t)),
            )?;

            // BOOKMARK: WHy does this cause unconstrainted variable?
            // Something about the overloaded Options?
            let (body_form, _) = car_cdr(
                &mut cs.namespace(|| "body_form"),
                global_allocations,
                &body_t,
                &store,
            )?;

            let fun_is_correct = constraints::alloc_equal(
                &mut cs.namespace(|| "fun hash is correct"),
                &fun.hash,
                &hash,
            )?;

            let cont_is_call2 = constraints::alloc_equal(
                &mut cs.namespace(|| "Call2 branch taken"),
                &cont.tag,
                &global_allocations.call2_cont_tag,
            )?;

            let cont_is_call2_and_not_dummy = and!(cs, &cont_is_call2, not_dummy)?;

            enforce_implication(
                &mut cs.namespace(|| "Call2 implies non-dummy fun"),
                &cont_is_call2_and_not_dummy,
                &fun_is_correct,
            );

            let newer_env = extend(
                &mut cs.namespace(|| "Call2 extend env"),
                global_allocations,
                &closed_env,
                &arg_t,
                result,
                &store,
            )?;

            let tail_cont = make_tail_continuation(
                &mut cs.namespace(|| "Call2 make_tail_continuation"),
                global_allocations,
                &saved_env,
                &continuation,
            )?;

            add_clauses(
                BaseContinuationTag::Call2.cont_tag_fr(),
                (
                    body_form,
                    newer_env,
                    tail_cont,
                    global_allocations.false_num.clone(),
                ),
            );
        }
    }

    {
        // Continuation::LetStar
        let var = tagged_hash_by_index(0, &continuation_components);
        let body = tagged_hash_by_index(1, &continuation_components);
        let saved_env = tagged_hash_by_index(2, &continuation_components);
        let cont = tagged_hash_by_index(3, &continuation_components);

        let extended_env = extend(
            &mut cs.namespace(|| "LetStar extend env"),
            global_allocations,
            env,
            &var,
            result,
            &store,
        )?;

        let tail_cont = make_tail_continuation(
            &mut cs.namespace(|| "LetStar make_tail_continuation"),
            global_allocations,
            &saved_env,
            &cont,
        )?;

        add_clauses(
            BaseContinuationTag::LetStar.cont_tag_fr(),
            (
                body,
                extended_env,
                tail_cont,
                global_allocations.false_num.clone(),
            ),
        );
    }
    {
        // Continuation::LetRecStar
        let var = tagged_hash_by_index(0, &continuation_components);
        let body = tagged_hash_by_index(1, &continuation_components);
        let saved_env = tagged_hash_by_index(2, &continuation_components);
        let cont = tagged_hash_by_index(3, &continuation_components);

        let extended_env = extend_rec(
            &mut cs.namespace(|| "LetRecStar extend_rec env"),
            global_allocations,
            env,
            &var,
            result,
            &store,
        )?;

        let is_error = extended_env.alloc_equal(
            &mut cs.namespace(|| "is_error"),
            &global_allocations.error_tagged_hash,
        )?;

        let tail_cont = make_tail_continuation(
            &mut cs.namespace(|| "LetRecStar make_tail_continuation"),
            global_allocations,
            &saved_env,
            &cont,
        )?;

        let return_cont = pick_tagged_hash(
            &mut cs.namespace(|| "return_cont"),
            &is_error,
            &global_allocations.error_tagged_hash,
            &tail_cont,
        )?;

        add_clauses(
            BaseContinuationTag::LetRecStar.cont_tag_fr(),
            (
                body,
                extended_env,
                return_cont,
                global_allocations.false_num.clone(),
            ),
        );
    }
    {
        // Continuation::Unop
        let op1 = tagged_hash_by_index(0, &continuation_components);
        let continuation = tagged_hash_by_index(1, &continuation_components);

        let not_dummy = alloc_equal(
            &mut cs.namespace(|| "Unop not dummy"),
            &cont.tag,
            &global_allocations.unop_cont_tag,
        )?;

        let (allocated_car, allocated_cdr) = car_cdr(
            &mut cs.namespace(|| "Unop cons"),
            global_allocations,
            result,
            &store,
        )?;

        let result_is_cons = alloc_equal(
            &mut cs.namespace(|| "result_is_cons"),
            &result.tag,
            &global_allocations.cons_tag,
        )?;

        let atom_tagged_hash = pick_tagged_hash(
            &mut cs.namespace(|| "atom val"),
            &result_is_cons,
            &global_allocations.nil_tagged_hash,
            &global_allocations.t_tagged_hash,
        )?;

        let cont_is_unop = alloc_equal(
            &mut cs.namespace(|| "cont is Unop"),
            &global_allocations.unop_cont_tag,
            &continuation.tag,
        );

        let val = multi_case(
            &mut cs.namespace(|| "Unop case"),
            &op1.tag,
            &[
                &[
                    CaseClause {
                        key: Op1::Car.fr(),
                        value: allocated_car.tag,
                    },
                    CaseClause {
                        key: Op1::Cdr.fr(),
                        value: allocated_cdr.tag,
                    },
                    CaseClause {
                        key: Op1::Atom.fr(),
                        value: atom_tagged_hash.tag,
                    },
                ],
                &[
                    CaseClause {
                        key: Op1::Car.fr(),
                        value: allocated_car.hash,
                    },
                    CaseClause {
                        key: Op1::Cdr.fr(),
                        value: allocated_cdr.hash,
                    },
                    CaseClause {
                        key: Op1::Atom.fr(),
                        value: atom_tagged_hash.hash,
                    },
                ],
            ],
            &[
                global_allocations.default.clone(),
                global_allocations.default.clone(),
                global_allocations.default.clone(),
            ],
        )?;

        add_clauses(
            BaseContinuationTag::Unop.cont_tag_fr(),
            (
                tagged_hash_by_index(0, &val),
                env.clone(),
                cont.clone(),
                global_allocations.true_num.clone(),
            ),
        );
    }
    {
        // Continuation::Binop
        let op2 = continuation_components[0].clone();
        let saved_env = tagged_hash_by_index(1, &continuation_components);
        let unevaled_args = tagged_hash_by_index(2, &continuation_components);
        let continuation = tagged_hash_by_index(3, &continuation_components);

        let not_dummy = alloc_equal(
            &mut cs.namespace(|| "Binop not dummy"),
            &cont.tag,
            &global_allocations.binop_cont_tag,
        )?;

        let (allocated_arg2, allocated_rest) = car_cdr(
            &mut cs.namespace(|| "Binop cons"),
            global_allocations,
            &unevaled_args,
            &store,
        )?;

        let binop2_components = [
            op2,
            global_allocations.default.clone(),
            result.tag.clone(),
            result.hash.clone(),
            continuation.tag,
            continuation.hash,
            global_allocations.default.clone(),
            global_allocations.default.clone(),
        ];
        let binop2_cont = Continuation::construct(
            &mut cs.namespace(|| "Binop2"),
            &global_allocations.binop2_cont_tag,
            &binop2_components,
        )?;

        // FIXME: If allocated_rest != Nil, then error.
        add_clauses(
            BaseContinuationTag::Binop.cont_tag_fr(),
            (
                allocated_arg2,
                saved_env,
                binop2_cont,
                global_allocations.false_num.clone(),
            ),
        );
    }
    {
        // Continuation::Binop2
        let op2 = tagged_hash_by_index(0, &continuation_components);
        let arg1 = tagged_hash_by_index(1, &continuation_components);
        let continuation = tagged_hash_by_index(2, &continuation_components);

        let arg2 = result;

        let arg1_is_num = alloc_equal(
            &mut cs.namespace(|| "arg1_is_num"),
            &arg1.tag,
            &global_allocations.num_tag,
        )?;
        let arg2_is_num = alloc_equal(
            &mut cs.namespace(|| "arg2_is_num"),
            &arg2.tag,
            &global_allocations.num_tag,
        )?;
        let both_args_are_nums = Boolean::and(
            &mut cs.namespace(|| "both_args_are_nums"),
            &arg1_is_num,
            &arg2_is_num,
        )?;

        let (a, b) = (arg1.hash.clone(), arg2.hash.clone()); // For Nums, the 'hash' is an immediate value.

        let not_dummy = alloc_equal(
            &mut cs.namespace(|| "Binop2 not dummy"),
            &cont.tag,
            &global_allocations.binop2_cont_tag,
        )?;

        let sum = constraints::add(&mut cs.namespace(|| "sum"), &a, &b)?;
        let diff = constraints::sub(&mut cs.namespace(|| "difference"), &a, &b)?;
        let product = constraints::mul(&mut cs.namespace(|| "product"), &a, &b)?;

        // FIXME: We need to check that b is not zero, returning an error if so.

        // In dummy paths, we need to use a non-zero dummy value for b.
        let divisor = //if dummy then 1 otherwise b.
            pick(&mut cs.namespace(||"maybe-dummy divisor"),
                 &not_dummy,
                 &b,
                 &global_allocations.true_num,
                 )?;

        let quotient = constraints::div(&mut cs.namespace(|| "quotient"), &a, &divisor)?;

        let cons = Expression::construct_cons(
            &mut cs.namespace(|| "cons"),
            global_allocations,
            &arg1,
            arg2,
        )?;

        let val = case(
            &mut cs.namespace(|| "Binop2 case"),
            &op2.tag,
            &[
                CaseClause {
                    key: Op2::Sum.fr(),
                    value: sum,
                },
                CaseClause {
                    key: Op2::Diff.fr(),
                    value: diff,
                },
                CaseClause {
                    key: Op2::Product.fr(),
                    value: product,
                },
                CaseClause {
                    key: Op2::Quotient.fr(),
                    value: quotient,
                },
                CaseClause {
                    key: Op2::Cons.fr(),
                    value: cons.hash,
                },
            ],
            &global_allocations.default.clone(),
        )?;

        let is_cons = alloc_equal(
            &mut cs.namespace(|| "Op2 is Cons"),
            &op2.tag,
            &global_allocations.op2_cons_tag,
        )?;

        let res_tag = pick(
            &mut cs.namespace(|| "Op2 result tag"),
            &is_cons,
            &global_allocations.cons_tag,
            &global_allocations.num_tag,
        )?;

        let res = AllocatedTaggedHash {
            tag: res_tag,
            hash: val,
        };

        let valid_types = constraints::or(
            &mut cs.namespace(|| "Op2 called with valid types"),
            &is_cons,
            &both_args_are_nums,
        )?;

        // FIXME: error if op2 is not actually an Op2.
        // Currently, this will return the default value, treated as Num.

        let c = pick_tagged_hash(
            &mut cs.namespace(|| "maybe type error"),
            &valid_types,
            &continuation,
            &global_allocations.error_tagged_hash,
        )?;

        add_clauses(
            BaseContinuationTag::Binop2.cont_tag_fr(),
            (res, env.clone(), c, global_allocations.true_num.clone()),
        );
    }
    {
        // Continuation::Relop
        let relop2 = continuation_components[0].clone();
        let saved_env = tagged_hash_by_index(1, &continuation_components);
        let unevaled_args = tagged_hash_by_index(2, &continuation_components);
        let continuation = tagged_hash_by_index(3, &continuation_components);

        let not_dummy = alloc_equal(
            &mut cs.namespace(|| "Relop not dummy"),
            &continuation.tag,
            &global_allocations.binop_cont_tag,
        )?;

        let (allocated_arg2, allocated_rest) = car_cdr(
            &mut cs.namespace(|| "Relops cons"),
            global_allocations,
            &unevaled_args,
            &store,
        )?;

        // FIXME: If allocated_rest != Nil, then error.
        let relop2_cont = Continuation::construct(
            &mut cs.namespace(|| "Relop2"),
            &global_allocations.relop2_cont_tag,
            &[
                relop2,
                global_allocations.default.clone(),
                result.tag.clone(),
                result.hash.clone(),
                continuation.tag,
                continuation.hash,
                global_allocations.default.clone(),
                global_allocations.default.clone(),
            ],
        )?;

        add_clauses(
            BaseContinuationTag::Relop.cont_tag_fr(),
            (
                allocated_arg2,
                saved_env,
                relop2_cont,
                global_allocations.false_num.clone(),
            ),
        );
    }
    {
        // Continuation::Relop2
        let rel2 = tagged_hash_by_index(0, &continuation_components);
        let arg1 = tagged_hash_by_index(1, &continuation_components);
        let continuation = tagged_hash_by_index(2, &continuation_components);
        let arg2 = result;

        let tags_equal = alloc_equal(
            &mut cs.namespace(|| "Relop2 tags equal"),
            &arg1.tag,
            &arg2.tag,
        )?;

        let vals_equal = alloc_equal(
            &mut cs.namespace(|| "Relop2 vals equal"),
            &arg1.hash,
            &arg2.hash,
        )?;

        let tag_is_num = alloc_equal(
            &mut cs.namespace(|| "arg1 tag is num"),
            &arg1.tag,
            &global_allocations.num_tag,
        )?;

        let rel2_is_equal = alloc_equal(
            &mut cs.namespace(|| "rel2 tag is Equal"),
            &rel2.tag,
            &global_allocations.rel2_equal_tag,
        )?;

        let args_equal =
            Boolean::and(&mut cs.namespace(|| "args equal"), &tags_equal, &vals_equal)?;

        // FIXME: This logic may be wrong. Look at it again carefully.
        // What we want is that Relop2::NumEqual not be used with any non-numeric arguments.
        // That should be an error.

        // not_num_tag_without_nums = args_equal && (tag_is_num || rel2_is_equal)
        let not_num_tag_without_nums =
            constraints::or(&mut cs.namespace(|| "sub_res"), &tag_is_num, &rel2_is_equal)?;

        let boolean_res = Boolean::and(
            &mut cs.namespace(|| "boolean_res"),
            &args_equal,
            &not_num_tag_without_nums,
        )?;

        let res = pick_tagged_hash(
            &mut cs.namespace(|| "res"),
            &boolean_res,
            &global_allocations.t_tagged_hash,
            &global_allocations.nil_tagged_hash,
        )?;

        // FIXME: Still need to handle:
        // - bad rel2 value (bad input)
        // - NumEqual rel2 without both args being Num (type error).

        add_clauses(
            BaseContinuationTag::Relop2.cont_tag_fr(),
            (
                res,
                env.clone(),
                continuation,
                global_allocations.true_num.clone(),
            ),
        );
    }
    {
        // Continuation::If
        let unevaled_args = tagged_hash_by_index(0, &continuation_components);
        let continuation = tagged_hash_by_index(1, &continuation_components);

        let condition = result;

        let not_dummy = alloc_equal(
            &mut cs.namespace(|| "If not dummy"),
            &continuation.tag,
            &global_allocations.if_cont_tag,
        )?;

        // NOTE: There was a tricky bug here.
        // When the actual continuation was Relop, and the operation is Numequal (for example),
        // Then this appears to be an invalid but not dummy continuation, since Numequal has a Relop tag value of 1,
        // the same as Cons.
        //
        // We address this by adding 2 to the tags returned by Op2 and Rel2 fr() methods, so this collision cannot happen.
        // TODO: It might make even more sense to make all disjoint.
        let (arg1, more) = car_cdr(
            &mut cs.namespace(|| "If unevaled_args cons"),
            global_allocations,
            &unevaled_args,
            &store,
        )?;

        let condition_is_nil = condition.alloc_equal(
            &mut cs.namespace(|| "condition is nil"),
            &global_allocations.nil_tagged_hash,
        )?;

        let (arg2, end) = car_cdr(
            &mut cs.namespace(|| "If more cons"),
            global_allocations,
            &more,
            &store,
        )?;

        let res = pick_tagged_hash(
            &mut cs.namespace(|| "pick arg1 or arg2"),
            &condition_is_nil,
            &arg2,
            &arg1,
        )?;

        add_clauses(
            BaseContinuationTag::If.cont_tag_fr(),
            (
                res,
                env.clone(),
                continuation,
                global_allocations.false_num.clone(),
            ),
        );
    }
    {
        // Continuation::Lookup
        let saved_env = tagged_hash_by_index(0, &continuation_components);
        let continuation = tagged_hash_by_index(1, &continuation_components);

        add_clauses(
            BaseContinuationTag::Lookup.cont_tag_fr(),
            (
                result.clone(),
                saved_env,
                continuation,
                global_allocations.true_num.clone(),
            ),
        );
    }
    {
        // Continuation::Simple
        let continuation = tagged_hash_by_index(0, &continuation_components);

        add_clauses(
            BaseContinuationTag::Simple.cont_tag_fr(),
            (
                result.clone(),
                env.clone(),
                continuation,
                global_allocations.true_num.clone(),
            ),
        );
    }
    {
        // Continuation::Tail
        let saved_env = tagged_hash_by_index(0, &continuation_components);
        let continuation = tagged_hash_by_index(1, &continuation_components);

        add_clauses(
            BaseContinuationTag::Tail.cont_tag_fr(),
            (
                result.clone(),
                saved_env,
                continuation,
                global_allocations.true_num.clone(),
            ),
        );
    }

    let all_clauses = [
        result_expr_tag_clauses.as_slice(),
        result_expr_hash_clauses.as_slice(),
        result_env_tag_clauses.as_slice(),
        result_env_hash_clauses.as_slice(),
        result_cont_tag_clauses.as_slice(),
        result_cont_hash_clauses.as_slice(),
        result_make_thunk_num_clauses.as_slice(),
    ];

    let case_results = multi_case(
        &mut cs.namespace(|| "invoke_continuation case"),
        &cont.tag,
        &all_clauses,
        &defaults,
    )?;

    let result_expr = tagged_hash_by_index(0, &case_results);
    let result_env = tagged_hash_by_index(1, &case_results);
    let result_cont = tagged_hash_by_index(2, &case_results);
    let make_thunk_num = case_results[6].clone();

    Ok((result_expr, result_env, result_cont, make_thunk_num))
}

fn car_cdr<CS: ConstraintSystem<Fr>>(
    mut cs: CS,
    g: &GlobalAllocations,
    maybe_cons: &AllocatedTaggedHash,
    store: &Store,
) -> Result<(AllocatedTaggedHash, AllocatedTaggedHash), SynthesisError> {
    // A dummy value will never have the cons tag.
    let not_dummy = alloc_equal(
        &mut cs.namespace(|| "not_dummy"),
        &maybe_cons.tag,
        &g.cons_tag,
    )?;

    let (car, cdr) = if not_dummy.get_value().expect("not_dummy missing") {
        if let Some(tagged_hash) = &maybe_cons.tagged_hash() {
            let found = store.fetch(tagged_hash);
            if let Some(found) = found {
                store.car_cdr(&found)
            } else {
                (Expression::Nil, Expression::Nil)
            }
        } else {
            // Dummy
            (Expression::Nil, Expression::Nil)
        }
    } else {
        // Dummy
        (Expression::Nil, Expression::Nil)
    };

    let allocated_car = car.allocated_tagged_hash(&mut cs.namespace(|| "car"))?;
    let allocated_cdr = cdr.allocated_tagged_hash(&mut cs.namespace(|| "cdr"))?;

    let constructed_cons = Expression::construct_cons(
        &mut cs.namespace(|| "cons"),
        g,
        &allocated_car,
        &allocated_cdr,
    )?;

    let real_cons = alloc_equal(
        &mut cs.namespace(|| "cons is real"),
        &maybe_cons.hash,
        &constructed_cons.hash,
    )?;

    enforce_implication(
        &mut cs.namespace(|| "not dummy implies real cons"),
        &not_dummy,
        &real_cons,
    )?;

    Ok((allocated_car, allocated_cdr))
}

fn extend<CS: ConstraintSystem<Fr>>(
    mut cs: CS,
    g: &GlobalAllocations,
    env: &AllocatedTaggedHash,
    var: &AllocatedTaggedHash,
    val: &AllocatedTaggedHash,
    store: &Store,
) -> Result<AllocatedTaggedHash, SynthesisError> {
    let new_binding =
        Expression::construct_cons(&mut cs.namespace(|| "extend binding"), g, var, val)?;
    Expression::construct_cons(cs, g, &new_binding, env)
}

fn extend_rec<CS: ConstraintSystem<Fr>>(
    mut cs: CS,
    g: &GlobalAllocations,
    env: &AllocatedTaggedHash,
    var: &AllocatedTaggedHash,
    val: &AllocatedTaggedHash,
    store: &Store,
) -> Result<AllocatedTaggedHash, SynthesisError> {
    let (binding_or_env, rest) = car_cdr(&mut cs.namespace(|| "car_cdr env"), g, env, store)?;
    let (var_or_binding, val_or_more_bindings) = car_cdr(
        &mut cs.namespace(|| "car_cdr binding_or_env"),
        g,
        &binding_or_env,
        store,
    )?;

    let cons = Expression::construct_cons(&mut cs.namespace(|| "cons var val"), g, var, val)?;
    let list = Expression::construct_list(&mut cs.namespace(|| "list cons"), g, &[cons.clone()])?;

    let new_env_if_sym_or_nil =
        Expression::construct_cons(&mut cs.namespace(|| "new_env_if_sym_or_nil"), g, &list, env)?;

    let cons2 = Expression::construct_cons(
        &mut cs.namespace(|| "cons cons binding_or_env"),
        g,
        &cons,
        &binding_or_env,
    )?;

    let cons3 =
        Expression::construct_cons(&mut cs.namespace(|| "cons cons2 rest"), g, &cons2, &rest)?;

    let is_sym = constraints::alloc_equal(
        &mut cs.namespace(|| "var_or_binding is sym"),
        &var_or_binding.tag,
        &g.sym_tag,
    )?;

    let is_nil = constraints::alloc_equal(
        &mut cs.namespace(|| "var_or_binding is nil"),
        &var_or_binding.tag,
        &g.nil_tag,
    )?;

    let is_sym_or_nil = or!(cs, &is_sym, &is_nil)?;

    let is_cons = constraints::alloc_equal(
        &mut cs.namespace(|| "var_or_binding is cons"),
        &var_or_binding.tag,
        &g.cons_tag,
    )?;

    let new_env_if_cons = pick_tagged_hash(
        &mut cs.namespace(|| "new_env_if_cons"),
        &is_cons,
        &cons3,
        &g.error_tagged_hash, // This is being used as a signal, since extend_rec is expected to return a valid env.
    )?;

    pick_tagged_hash(
        &mut cs.namespace(|| "extend_rec result"),
        &is_sym_or_nil,
        &new_env_if_sym_or_nil,
        &new_env_if_cons,
    )
}

fn make_tail_continuation<CS: ConstraintSystem<Fr>>(
    mut cs: CS,
    g: &GlobalAllocations,
    env: &AllocatedTaggedHash,
    continuation: &AllocatedTaggedHash,
) -> Result<AllocatedTaggedHash, SynthesisError> {
    let continuation_is_tail = alloc_equal(
        &mut cs.namespace(|| "continuation is tail"),
        &continuation.tag,
        &g.tail_cont_tag,
    )?;

    let new_tail = Continuation::construct(
        &mut cs.namespace(|| "new tail continuation"),
        &g.tail_cont_tag,
        &[
            env.tag.clone(),
            env.hash.clone(),
            continuation.tag.clone(),
            continuation.hash.clone(),
            g.default.clone(),
            g.default.clone(),
            g.default.clone(),
            g.default.clone(),
        ],
    )?;

    pick_tagged_hash(
        &mut cs.namespace(|| "the tail continuation"),
        &continuation_is_tail,
        continuation,
        &new_tail,
    )
}

fn tagged_hash_by_index(n: usize, case_results: &[AllocatedNum<Fr>]) -> AllocatedTaggedHash {
    AllocatedTaggedHash::from_tag_and_hash(
        case_results[n * 2].clone(),
        case_results[1 + n * 2].clone(),
    )
}

#[cfg(test)]

mod tests {
    use super::*;
    use crate::data::Store;
    use crate::eval::{empty_sym_env, Evaluable, Witness, IO};
    use crate::proof::Provable;
    use bellperson::util_cs::{
        metric_cs::MetricCS, test_cs::TestConstraintSystem, Comparable, Delta,
    };

    #[test]
    fn num_self_evaluating() {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let num = Expression::num(123);

        let mut input = IO {
            expr: num.clone(),
            env: env.clone(),
            cont: Continuation::Outermost,
        };

        let initial = input.clone();
        let (_, witness) = input.eval(&mut store);

        let groth_params = Frame::groth_params().unwrap();
        let vk = &groth_params.vk;

        let test_with_output = |output, expect_success, pvk| {
            let mut cs = TestConstraintSystem::new();

            let mut cs_blank = MetricCS::<Fr>::new();
            let blank_frame = Frame::blank();
            blank_frame
                .synthesize(&mut cs_blank)
                .expect("failed to synthesize");

            let frame = Frame {
                input: Some(input.clone()),
                output: Some(output),
                initial: Some(initial.clone()),
                i: Some(0),
                witness: Some(witness.clone()),
            };

            frame
                .clone()
                .synthesize(&mut cs)
                .expect("failed to synthesize");

            let delta = cs.delta(&cs_blank, false);
            assert!(delta == Delta::Equal);

            assert_eq!(31401, cs.num_constraints());
            assert_eq!(20, cs.num_inputs());
            assert_eq!(31349, cs.aux().len());

            let public_inputs = frame.public_inputs();
            let mut rng = rand::thread_rng();

            let proof = frame.clone().prove(Some(&groth_params), &mut rng).unwrap();
            let cs_verified = cs.is_satisfied() && cs.verify(&public_inputs);
            let verified = Frame::verify_groth16_proof(pvk, proof, frame).unwrap();

            if expect_success {
                assert!(cs_verified);
                assert!(verified);
            } else {
                assert!(!cs_verified);
                assert!(!verified)
            };
        };

        // Success
        {
            let output = IO {
                expr: num.clone(),
                env: env.clone(),
                cont: Continuation::Terminal,
            };

            test_with_output(output, true, groth16::prepare_verifying_key(vk));
        }

        // Failure
        {}
        {
            // Wrong type, so tag should differ.
            let bad_output_tag = IO {
                expr: store.intern("SYMBOL"),
                env: env.clone(),
                cont: Continuation::Terminal,
            };

            test_with_output(bad_output_tag, false, groth16::prepare_verifying_key(vk));
        }

        {
            // Wrong value, so hash should differ.
            let bad_output_value = IO {
                expr: Expression::num(999),
                env: env.clone(),
                cont: Continuation::Terminal,
            };

            test_with_output(bad_output_value, false, groth16::prepare_verifying_key(vk));
        }

        {
            // Wrong new env.
            let bad_output_tag = IO {
                expr: num.clone(),
                env: store.intern("not-an-env"),
                cont: Continuation::Terminal,
            };

            test_with_output(bad_output_tag, false, groth16::prepare_verifying_key(vk));
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
        };

        let initial = input.clone();
        let (_, witness) = input.eval(&mut store);

        let mut test_with_output = |output, expect_success| {
            let mut cs = TestConstraintSystem::new();

            let frame = Frame {
                input: Some(input.clone()),
                output: Some(output),
                initial: Some(initial.clone()),
                i: Some(0),
                witness: Some(witness.clone()),
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

    //#[test]
    fn t_self_evaluating() {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let t = store.intern("T");

        let mut input = IO {
            expr: t.clone(),
            env: env.clone(),
            cont: Continuation::Outermost,
        };

        let initial = input.clone();
        // let witness = input.compute_witness(&mut store);

        let (_, witness) = input.eval(&mut store);

        let test_with_output = |output, expect_success| {
            let mut cs = TestConstraintSystem::new();

            let frame = Frame {
                input: Some(input.clone()),
                output: Some(output),
                initial: Some(initial.clone()),
                i: Some(0),
                witness: Some(witness.clone()),
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
        let body = store.list(&mut [var.clone()]);
        let fun = Expression::Fun(
            var.tagged_hash().clone(),
            body.tagged_hash().clone(),
            env.tagged_hash().clone(),
        );

        let mut input = IO {
            expr: fun.clone(),
            env: env.clone(),
            cont: Continuation::Outermost,
        };

        let initial = input.clone();
        let (_, witness) = input.eval(&mut store);

        let test_with_output = |output, expect_success| {
            let mut cs = TestConstraintSystem::new();

            let frame = Frame {
                input: Some(input.clone()),
                output: Some(output),
                initial: Some(initial.clone()),
                i: Some(0),
                witness: Some(witness.clone()),
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
        };

        let initial = input.clone();
        let (_, witness) = input.eval(&mut store);

        let test_with_output = |output, expect_success| {
            let mut cs = TestConstraintSystem::new();

            let frame = Frame {
                input: Some(input.clone()),
                output: Some(output),
                initial: Some(initial.clone()),
                i: Some(0),
                witness: Some(witness.clone()),
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
