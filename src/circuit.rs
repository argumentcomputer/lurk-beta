#![allow(clippy::too_many_arguments)]

use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    Circuit, ConstraintSystem, SynthesisError,
};
use blstrs::Scalar as Fr;

use crate::{
    gadgets::{
        case::{case, multi_case, CaseClause},
        data::{pick_ptr, GlobalAllocations},
        pointer::{AllocatedContPtr, AllocatedPtr},
    },
    pool::ScalarPointer,
};

use crate::eval::{Frame, Witness, IO};
use crate::gadgets::constraints::{
    self, alloc_equal, alloc_is_zero, enforce_implication, or, pick,
};
use crate::pool::{ContPtr, ContTag, Op1, Op2, Pool, Ptr, Tag, Thunk};
use crate::writer::Write;

fn bind_input<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    expr: Option<&Ptr>,
    pool: &Pool,
) -> Result<AllocatedPtr, SynthesisError> {
    let ptr = expr.and_then(|e| pool.hash_expr(e));

    let tag = AllocatedNum::alloc(cs.namespace(|| "tag"), || {
        ptr.as_ref()
            .map(|th| *th.tag())
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    tag.inputize(cs.namespace(|| "tag input"))?;

    let hash = AllocatedNum::alloc(cs.namespace(|| "hash"), || {
        ptr.as_ref()
            .map(|th| *th.value())
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    hash.inputize(cs.namespace(|| "hash input"))?;

    Ok(AllocatedPtr::from_allocated_parts_unchecked(tag, hash))
}

#[derive(Clone)]
pub struct CircuitFrame<'a, T, W> {
    pub pool: &'a Pool,
    pub input: Option<T>,
    pub output: Option<T>,
    pub initial: Option<T>,
    pub i: Option<usize>,
    pub witness: Option<W>,
}

impl<'a, T: Clone, W> CircuitFrame<'a, T, W> {
    pub fn from_frame(initial: T, frame: Frame<T, W>, pool: &'a Pool) -> Self {
        CircuitFrame {
            pool,
            input: Some(frame.input),
            output: Some(frame.output),
            initial: Some(initial),
            i: Some(frame.i),
            witness: Some(frame.witness),
        }
    }
}

impl Circuit<Fr> for CircuitFrame<'_, IO, Witness> {
    fn synthesize<CS: ConstraintSystem<Fr>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        if let Some(o) = &self.output {
            dbg!(o.expr.fmt_to_string(self.pool));
        }
        if let Some(i) = &self.input {
            dbg!(i.expr.fmt_to_string(self.pool));
        }

        ////////////////////////////////////////////////////////////////////////////////
        // Bind public inputs.
        //
        // The frame's input:
        let input_expr = bind_input(
            &mut cs.namespace(|| "input expression"),
            self.input.as_ref().map(|input| &input.expr),
            self.pool,
        )?;

        let input_env = bind_input(
            &mut cs.namespace(|| "input env"),
            self.input.as_ref().map(|input| &input.env),
            self.pool,
        )?;

        let input_cont = AllocatedContPtr::bind_input(
            &mut cs.namespace(|| "input cont"),
            self.input.as_ref().map(|input| &input.cont),
            self.pool,
        )?;

        // The frame's output:
        let output_expr = bind_input(
            &mut cs.namespace(|| "output expression"),
            self.output.as_ref().map(|output| &output.expr),
            self.pool,
        )?;

        let output_env = bind_input(
            &mut cs.namespace(|| "output env"),
            self.output.as_ref().map(|output| &output.env),
            self.pool,
        )?;

        let output_cont = AllocatedContPtr::bind_input(
            &mut cs.namespace(|| "output cont"),
            self.output.as_ref().map(|output| &output.cont),
            self.pool,
        )?;

        // The initial input to the IVC computation.
        // FIXME: use?
        let _initial_expr = bind_input(
            &mut cs.namespace(|| "initial expression"),
            self.initial.as_ref().map(|initial| &initial.expr),
            self.pool,
        )?;

        // FIXME: use?
        let _initial_env = bind_input(
            &mut cs.namespace(|| "initial env"),
            self.initial.as_ref().map(|initial| &initial.env),
            self.pool,
        )?;

        // FIXME: use?
        let _initial_cont = AllocatedContPtr::bind_input(
            &mut cs.namespace(|| "initial cont"),
            self.initial.as_ref().map(|initial| &initial.cont),
            self.pool,
        )?;

        // We don't currently need this, but we could expose access to it for logging, etc.
        // The frame counter:
        // FIXME: use?
        let _frame_counter = cs.alloc_input(
            || "frame counter",
            || {
                self.i
                    .map(|i| Fr::from(i as u64))
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
            self.pool,
        )?;

        dbg!(&output_expr, &new_expr,);
        dbg!(&output_env, &new_env,);
        dbg!(&output_cont, &new_cont,);

        dbg!(output_expr.fetch_and_write_str(self.pool),);
        dbg!(new_expr.fetch_and_write_str(self.pool));

        dbg!(output_env.fetch_and_write_str(self.pool),);
        dbg!(new_env.fetch_and_write_str(self.pool));

        dbg!(output_cont.fetch_and_write_cont_str(self.pool),);
        dbg!(new_cont.fetch_and_write_cont_str(self.pool));

        output_expr.enforce_equal(&mut cs.namespace(|| "output expr is correct"), &new_expr);
        output_env.enforce_equal(&mut cs.namespace(|| "output env is correct"), &new_env);
        output_cont.enforce_equal(&mut cs.namespace(|| "output cont is correct"), &new_cont);

        Ok(())
    }
}

#[derive(Default)]
struct Results<'a> {
    expr_tag_clauses: Vec<CaseClause<'a, Fr>>,
    expr_hash_clauses: Vec<CaseClause<'a, Fr>>,
    env_tag_clauses: Vec<CaseClause<'a, Fr>>,
    env_hash_clauses: Vec<CaseClause<'a, Fr>>,
    cont_tag_clauses: Vec<CaseClause<'a, Fr>>,
    cont_hash_clauses: Vec<CaseClause<'a, Fr>>,
    invoke_continuation_clauses: Vec<CaseClause<'a, Fr>>,
    make_thunk_num_clauses: Vec<CaseClause<'a, Fr>>,
}

fn add_clause<'a>(
    tag_clauses: &mut Vec<CaseClause<'a, Fr>>,
    hash_clauses: &mut Vec<CaseClause<'a, Fr>>,
    key: Fr,
    expr: &'a AllocatedPtr,
) {
    add_clause_single(tag_clauses, key, expr.tag());
    add_clause_single(hash_clauses, key, expr.hash());
}

fn add_clause_cont<'a>(
    tag_clauses: &mut Vec<CaseClause<'a, Fr>>,
    hash_clauses: &mut Vec<CaseClause<'a, Fr>>,
    key: Fr,
    cont: &'a AllocatedContPtr,
) {
    add_clause_single(tag_clauses, key, cont.tag());
    add_clause_single(hash_clauses, key, cont.hash());
}

fn add_clause_single<'a>(
    clauses: &mut Vec<CaseClause<'a, Fr>>,
    key: Fr,
    value: &'a AllocatedNum<Fr>,
) {
    clauses.push(CaseClause { key, value });
}

impl<'a> Results<'a> {
    fn add_clauses_expr(
        &mut self,
        key: Tag,
        result_expr: &'a AllocatedPtr,
        result_env: &'a AllocatedPtr,
        result_cont: &'a AllocatedContPtr,
        result_invoke_continuation: &'a AllocatedNum<Fr>,
    ) {
        let key = key.as_field();
        add_clause(
            &mut self.expr_tag_clauses,
            &mut self.expr_hash_clauses,
            key,
            result_expr,
        );

        add_clause(
            &mut self.env_tag_clauses,
            &mut self.env_hash_clauses,
            key,
            result_env,
        );

        add_clause_cont(
            &mut self.cont_tag_clauses,
            &mut self.cont_hash_clauses,
            key,
            result_cont,
        );

        add_clause_single(
            &mut self.invoke_continuation_clauses,
            key,
            result_invoke_continuation,
        );
    }

    fn add_clauses_cons(
        &mut self,
        key: Fr,
        result_expr: &'a AllocatedPtr,
        result_env: &'a AllocatedPtr,
        result_cont: &'a AllocatedContPtr,
        invoke_cont: &'a AllocatedNum<Fr>,
    ) {
        add_clause(
            &mut self.expr_tag_clauses,
            &mut self.expr_hash_clauses,
            key,
            result_expr,
        );
        add_clause(
            &mut self.env_tag_clauses,
            &mut self.env_hash_clauses,
            key,
            result_env,
        );
        add_clause_cont(
            &mut self.cont_tag_clauses,
            &mut self.cont_hash_clauses,
            key,
            result_cont,
        );
        add_clause_single(&mut self.invoke_continuation_clauses, key, invoke_cont);
    }

    fn add_clauses_thunk(
        &mut self,
        key: ContTag,
        result_expr: &'a AllocatedPtr,
        result_env: &'a AllocatedPtr,
        result_cont: &'a AllocatedContPtr,
    ) {
        let key = key.as_field();
        add_clause(
            &mut self.expr_tag_clauses,
            &mut self.expr_hash_clauses,
            key,
            result_expr,
        );
        add_clause(
            &mut self.env_tag_clauses,
            &mut self.env_hash_clauses,
            key,
            result_env,
        );
        add_clause_cont(
            &mut self.cont_tag_clauses,
            &mut self.cont_hash_clauses,
            key,
            result_cont,
        );
    }

    fn add_clauses_cont(
        &mut self,
        key: ContTag,
        result_expr: &'a AllocatedPtr,
        result_env: &'a AllocatedPtr,
        result_cont: &'a AllocatedContPtr,
        make_thunk_num: &'a AllocatedNum<Fr>,
    ) {
        let key = key.as_field();
        add_clause(
            &mut self.expr_tag_clauses,
            &mut self.expr_hash_clauses,
            key,
            result_expr,
        );
        add_clause(
            &mut self.env_tag_clauses,
            &mut self.env_hash_clauses,
            key,
            result_env,
        );
        add_clause_cont(
            &mut self.cont_tag_clauses,
            &mut self.cont_hash_clauses,
            key,
            result_cont,
        );
        add_clause_single(&mut self.make_thunk_num_clauses, key, make_thunk_num);
    }
}

fn evaluate_expression<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    expr: &AllocatedPtr,
    env: &AllocatedPtr,
    cont: &AllocatedContPtr,
    witness: &Option<Witness>,
    pool: &Pool,
) -> Result<(AllocatedPtr, AllocatedPtr, AllocatedContPtr), SynthesisError> {
    dbg!("evaluate_expression");

    dbg!(&expr.fetch_and_write_str(pool));
    dbg!(&env.fetch_and_write_str(pool));
    dbg!(expr, cont);

    let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), pool, witness)?;

    let mut results = Results::default();
    {
        // Self-evaluating expressions
        results.add_clauses_expr(Tag::Nil, expr, env, cont, &g.true_num);
        results.add_clauses_expr(Tag::Num, expr, env, cont, &g.true_num);
        results.add_clauses_expr(Tag::Fun, expr, env, cont, &g.true_num);
    }

    let (expr_thunk_hash, expr_thunk_value, expr_thunk_continuation) =
        expr.allocate_thunk_components(&mut cs.namespace(|| "allocate thunk components"), pool)?;
    {
        // Enforce (expr.tag == thunk_tag) implies (expr_thunk_hash == expr.hash).
        let expr_is_a_thunk = constraints::alloc_equal(
            &mut cs.namespace(|| "expr.tag == thunk_tag"),
            expr.tag(),
            &g.thunk_tag,
        )?;
        let expr_is_the_thunk = constraints::alloc_equal(
            &mut cs.namespace(|| "thunk_hash == expr.hash"),
            &expr_thunk_hash,
            expr.hash(),
        )?;

        enforce_implication(
            &mut cs
                .namespace(|| "(expr.tag == thunk_continuation) implies (thunk_hash == expr.hash)"),
            &expr_is_a_thunk,
            &expr_is_the_thunk,
        )?;

        results.add_clauses_expr(
            Tag::Thunk,
            &expr_thunk_value,
            env,
            &expr_thunk_continuation,
            &g.true_num,
        );
    }

    // --
    let eval_sym_not_dummy = alloc_equal(
        &mut cs.namespace(|| "eval_sym_not_dummy"),
        expr.tag(),
        &g.sym_tag,
    )?;

    let (sym_result, sym_env, sym_cont, sym_invoke_cont) = eval_sym(
        &mut cs.namespace(|| "eval Sym"),
        expr,
        env,
        cont,
        &eval_sym_not_dummy,
        witness,
        pool,
        &g,
    )?;

    results.add_clauses_expr(Tag::Sym, &sym_result, &sym_env, &sym_cont, &sym_invoke_cont);
    // --

    // --
    let eval_cons_not_dummy = alloc_equal(
        &mut cs.namespace(|| "eval_cons_not_dummy"),
        expr.tag(),
        &g.cons_tag,
    )?;

    let (cons_result, cons_env, cons_cont, cons_invoke_cont) = eval_cons(
        &mut cs.namespace(|| "eval Cons"),
        expr,
        env,
        cont,
        &eval_cons_not_dummy,
        witness,
        pool,
        &g,
    )?;

    results.add_clauses_expr(
        Tag::Cons,
        &cons_result,
        &cons_env,
        &cons_cont,
        &cons_invoke_cont,
    );

    // --

    let all_clauses = [
        &results.expr_tag_clauses[..],
        &results.expr_hash_clauses[..],
        &results.env_tag_clauses[..],
        &results.env_hash_clauses[..],
        &results.cont_tag_clauses[..],
        &results.cont_hash_clauses[..],
        &results.invoke_continuation_clauses[..],
    ];
    let defaults = [
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.false_num,
    ];

    let case_results = multi_case(
        &mut cs.namespace(|| "input expr tag case"),
        expr.tag(),
        &all_clauses,
        &defaults,
    )?;

    let first_result_expr = ptr_by_index(0, &case_results, pool);

    let first_result_env = ptr_by_index(1, &case_results, pool);
    let first_result_cont = AllocatedContPtr::by_index(2, &case_results);
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
        pool,
        &g,
    )?;

    let invoke_continuation_make_thunk: AllocatedNum<Fr> = invoke_continuation_results.3;

    let result_expr0 = pick_ptr(
        &mut cs.namespace(|| "pick maybe invoke_continuation expr"),
        &invoke_continuation_boolean,
        &invoke_continuation_results.0,
        &first_result_expr,
        pool,
    )?;

    let result_env0 = pick_ptr(
        &mut cs.namespace(|| "pick maybe invoke_continuation env"),
        &invoke_continuation_boolean,
        &invoke_continuation_results.1,
        &first_result_env,
        pool,
    )?;

    let result_cont0 = AllocatedContPtr::pick(
        &mut cs.namespace(|| "pick maybe invoke_continuation cont"),
        &invoke_continuation_boolean,
        dbg!(&invoke_continuation_results.2),
        dbg!(&first_result_cont),
    )?;

    let make_thunk_num = pick(
        &mut cs.namespace(|| "pick make_thunk_boolean"),
        &invoke_continuation_boolean,
        &invoke_continuation_make_thunk,
        &g.false_num,
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
        pool,
        &g,
    )?;

    let result_expr = pick_ptr(
        &mut cs.namespace(|| "pick maybe make_thunk expr"),
        &make_thunk_boolean,
        &thunk_results.0,
        &result_expr0,
        pool,
    )?;

    let result_env = pick_ptr(
        &mut cs.namespace(|| "pick maybe make_thunk env"),
        &make_thunk_boolean,
        &thunk_results.1,
        &result_env0,
        pool,
    )?;

    let result_cont = AllocatedContPtr::pick(
        &mut cs.namespace(|| "pick maybe make_thunk cont"),
        &make_thunk_boolean,
        &thunk_results.2,
        &result_cont0,
    )?;

    Ok((result_expr, result_env, result_cont))
}

fn eval_sym<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    expr: &AllocatedPtr,
    env: &AllocatedPtr,
    cont: &AllocatedContPtr,
    not_dummy: &Boolean,
    witness: &Option<Witness>,
    pool: &Pool,
    g: &GlobalAllocations,
) -> Result<
    (
        AllocatedPtr,
        AllocatedPtr,
        AllocatedContPtr,
        AllocatedNum<Fr>,
    ),
    SynthesisError,
> {
    let output_expr = AllocatedPtr::from_ptr(
        &mut cs.namespace(|| "output_expr"),
        pool,
        witness.as_ref().map(|w| &w.prethunk_output_expr),
    )?;
    let output_env = AllocatedPtr::from_ptr(
        &mut cs.namespace(|| "output_env"),
        pool,
        witness.as_ref().map(|w| &w.prethunk_output_env),
    )?;
    let output_cont =
        AllocatedContPtr::alloc_cont_ptr(&mut cs.namespace(|| "output_cont"), pool, || {
            witness
                .as_ref()
                .map(|w| &w.prethunk_output_cont)
                .ok_or(SynthesisError::AssignmentMissing)
        })?;

    let sym_is_nil = expr.alloc_equal(&mut cs.namespace(|| "sym is nil"), &g.nil_ptr)?;
    let sym_is_t = expr.alloc_equal(&mut cs.namespace(|| "sym is t"), &g.t_ptr)?;

    let sym_is_self_evaluating = or!(cs, &sym_is_nil, &sym_is_t)?;
    let sym_otherwise = Boolean::not(&sym_is_self_evaluating);

    let (binding, smaller_env) =
        car_cdr(&mut cs.namespace(|| "If unevaled_args cons"), g, env, pool)?;

    let binding_is_nil = binding.alloc_equal(&mut cs.namespace(|| "binding is nil"), &g.nil_ptr)?;

    let binding_not_nil = Boolean::not(&binding_is_nil);

    let otherwise_and_binding_is_nil = and!(cs, &sym_otherwise, &binding_is_nil)?;
    let otherwise_and_binding_not_nil = and!(cs, &sym_otherwise, &binding_not_nil)?;

    let (var_or_rec_binding, val_or_more_rec_env) =
        car_cdr(&mut cs.namespace(|| "car_cdr binding"), g, &binding, pool)?;

    let var_or_rec_binding_is_sym = alloc_equal(
        &mut cs.namespace(|| "var_or_rec_binding_is_sym"),
        var_or_rec_binding.tag(),
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
        var_or_rec_binding.tag(),
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
        pool,
    )?;

    let val2_is_fun = alloc_equal(cs.namespace(|| "val2_is_fun"), val2.tag(), &g.fun_tag)?;
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
        cont.tag(),
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

    let lookup_continuation = AllocatedContPtr::construct(
        &mut cs.namespace(|| "lookup_continuation"),
        &g.lookup_cont_tag,
        // Mirrors Continuation::get_hash_components()
        &[
            env,
            cont,
            &[&g.default_num, &g.default_num],
            &[&g.default_num, &g.default_num],
        ],
        pool,
    )?;

    let rec_env = binding;

    let (_fun_hash, fun_arg, fun_body, fun_closed_env) = Ptr::allocate_maybe_fun(
        &mut cs.namespace(|| "extend closure"),
        pool,
        witness.as_ref().and_then(|w| w.extended_closure.as_ref()),
    )?;

    let extended_env = Ptr::construct_cons(
        &mut cs.namespace(|| "extended_env"),
        g,
        &rec_env,
        &fun_closed_env,
        pool,
    )?;

    let extended_fun = Ptr::construct_fun(
        &mut cs.namespace(|| "extended_fun"),
        g,
        &fun_arg,
        &fun_body,
        &extended_env,
        pool,
    )?;

    let val_to_use = pick_ptr(
        &mut cs.namespace(|| "val_to_use"),
        &val2_is_fun,
        &extended_fun,
        &val2,
        pool,
    )?;

    let smaller_rec_env = val_or_more_rec_env;
    let smaller_rec_env_is_nil =
        smaller_rec_env.alloc_equal(&mut cs.namespace(|| "smaller_rec_env_is_nil"), &g.nil_ptr)?;

    let with_smaller_rec_env = Ptr::construct_cons(
        &mut cs.namespace(|| "with_smaller_rec_env"),
        g,
        &smaller_rec_env,
        &smaller_env,
        pool,
    )?;

    let env_to_use = ifx_t!(
        cs,
        &smaller_rec_env_is_nil,
        &smaller_env,
        &with_smaller_rec_env,
        pool
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

        implies_equal_t!(cs, &cond1, &output_cont, cont);
    }

    let cs = &mut cs.namespace(|| "otherwise_and_binding_is_nil");
    let cond2 = and!(cs, &otherwise_and_binding_is_nil, not_dummy)?;
    {
        // let cond = and!(cs, &otherwise_and_binding_is_nil, not_dummy)?;

        // implies_equal_t!(cs, &cond2, &output_expr, &expr);
        // implies_equal_t!(cs, &cond2, &output_env, &env);
        implies_equal_t!(cs, &cond2, &output_cont, &g.error_ptr);
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
        implies_equal_t!(cs, &cond10, &output_cont, &g.error_ptr);
    }

    let conda = or!(cs, &cond1, &cond2)?; // cond1, cond2
    let condb = or!(cs, &cond4, &cond6)?; // cond4, cond6
    let condc = or!(cs, &conda, &cond8)?; // cond1, cond2, cond8

    let condx = or!(cs, &cond4, &cond5)?; // cond4, cond5
    let condy = or!(cs, &cond3, &cond6)?; // cond3, cond6

    // cond1, cond2, cond4, cond5 // cond_expr
    let cond_expr = or!(cs, &conda, &condx)?; // cond1, cond2, cond4, cond5
    implies_equal_t!(cs, &cond_expr, &output_expr, expr);

    // cond1, cond2, cond3, cond6 // cond_env
    let cond_env = or!(cs, &conda, &condy)?; // cond1, cond2, cond3, cond6
    implies_equal_t!(cs, &cond_env, &output_env, env);

    // cond1, cond3, cond4, cond6, cond // cond_cont
    let cond_cont = or!(cs, &condb, &condc)?; // cond1, cond2, cond4, cond6, cond8
    implies_equal_t!(cs, &cond_cont, &output_cont, cont);

    Ok((output_expr, output_env, output_cont, invoke_cont_num))
}

fn eval_cons<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    expr: &AllocatedPtr,
    env: &AllocatedPtr,
    cont: &AllocatedContPtr,
    _not_dummy: &Boolean,
    _witness: &Option<Witness>,
    pool: &Pool,
    g: &GlobalAllocations,
) -> Result<
    (
        AllocatedPtr,
        AllocatedPtr,
        AllocatedContPtr,
        AllocatedNum<Fr>,
    ),
    SynthesisError,
> {
    let lambda = g.lambda_ptr.clone();

    let hash_sym = |sym: &str| pool.get_sym(sym).and_then(|s| pool.hash_sym(s)).unwrap();

    let lambda_hash = hash_sym("LAMBDA");
    let quote_hash = hash_sym("QUOTE");
    let letstar = hash_sym("LET*");
    let letstar_t = letstar.allocate_constant_ptr(&mut cs.namespace(|| "letstar_t"))?;
    let letstar_hash = letstar.value();
    let letrecstar = hash_sym("LETREC*");
    let letrecstar_t = letrecstar.allocate_constant_ptr(&mut cs.namespace(|| "letrecstar"))?;
    let letrecstar_hash = letrecstar.value();
    let cons_hash = hash_sym("CAR");
    let car_hash = hash_sym("CAR");
    let cdr_hash = hash_sym("CDR");
    let atom_hash = hash_sym("ATOM");
    let sum_hash = hash_sym("+");
    let diff_hash = hash_sym("-");
    let product_hash = hash_sym("*");
    let quotient_hash = hash_sym("/");
    let numequal_hash = hash_sym("=");
    let equal_hash = hash_sym("EQ");
    let current_env_hash = hash_sym("CURRENT-ENV");
    let if_hash = hash_sym("IF");

    let (head, rest) = car_cdr(&mut cs.namespace(|| "eval_cons expr"), g, expr, pool)?;

    // let not_dummy = alloc_equal(&mut cs.namespace(|| "rest is cons"), &rest.tag, &g.cons_tag)?;

    let (arg1, more) = car_cdr(&mut cs.namespace(|| "car_cdr(rest)"), g, &rest, pool)?;

    let mut results = Results::default();

    // --
    let function = {
        // head == LAMBDA
        let (args, body) = (arg1.clone(), more.clone());
        let args_is_nil = args.alloc_equal(&mut cs.namespace(|| "args_is_nil"), &g.nil_ptr)?;

        // let not_dummy1 = Boolean::not(&args_is_nil);
        // let not_dummy2 = Boolean::and(&mut cs.namespace(|| "not_dummy2"), &not_dummy, &not_dummy1)?;

        let (car_args, cdr_args) = car_cdr(&mut cs.namespace(|| "car_cdr args"), g, &args, pool)?;

        // FIXME: There maybe some cases where cdr_args is wrong/differs from eval.rs.

        let arg = pick_ptr(
            &mut cs.namespace(|| "maybe dummy arg"),
            &args_is_nil,
            &g.dummy_arg_ptr,
            &car_args,
            pool,
        )?;

        let inner = Ptr::construct_cons(&mut cs.namespace(|| "inner"), g, &cdr_args, &body, pool)?;
        let l = Ptr::construct_cons(&mut cs.namespace(|| "l"), g, &lambda, &inner, pool)?;
        let cdr_args_is_nil =
            cdr_args.alloc_equal(&mut cs.namespace(|| "cdr_args_is_nil"), &g.nil_ptr)?;

        let list = Ptr::construct_list(&mut cs.namespace(|| "list"), g, &[&l], pool)?;
        let inner_body = pick_ptr(
            &mut cs.namespace(|| "inner_body"),
            &cdr_args_is_nil,
            &body,
            &list,
            pool,
        )?;

        Ptr::construct_fun(
            &mut cs.namespace(|| "function"),
            g,
            &arg,
            &inner_body,
            env,
            pool,
        )?
    };

    results.add_clauses_cons(*lambda_hash.value(), &function, env, cont, &g.true_num);

    {
        // head == QUOTE
        results.add_clauses_cons(*quote_hash.value(), &arg1, env, cont, &g.true_num);
    }

    let (val, continuation_letstar, continuation_letrecstar) = {
        // head == LET*
        // or head == LETREC*

        let mut cs_letrec = cs.namespace(|| "LET(REC)*");

        let (bindings, body) = (arg1.clone(), more.clone());
        let (body1, _rest_body) =
            car_cdr(&mut cs_letrec.namespace(|| "car_cdr body"), g, &body, pool)?;
        let (binding1, rest_bindings) = car_cdr(
            &mut cs_letrec.namespace(|| "car_cdr bindings"),
            g,
            &bindings,
            pool,
        )?;
        let (var, more_vals) = car_cdr(
            &mut cs_letrec.namespace(|| "car_cdr binding1"),
            g,
            &binding1,
            pool,
        )?;
        let (val, _end) = car_cdr(
            &mut cs_letrec.namespace(|| "car_cdr more_vals"),
            g,
            &more_vals,
            pool,
        )?;

        // FIXME: assert end == NIL
        let expanded1 = Ptr::construct_list(
            &mut cs_letrec.namespace(|| "expanded1"),
            g,
            &[&letstar_t, &rest_bindings, &body1],
            pool,
        )?;
        let bindings_is_nil =
            bindings.alloc_equal(&mut cs_letrec.namespace(|| "bindings_is_nil"), &g.nil_ptr)?;

        let rest_bindings_is_nil = rest_bindings.alloc_equal(
            &mut cs_letrec.namespace(|| "rest_bindings_is_nil"),
            &g.nil_ptr,
        )?;

        let expanded = pick_ptr(
            &mut cs_letrec.namespace(|| "expanded"),
            &rest_bindings_is_nil,
            &body1,
            &expanded1,
            pool,
        )?;

        let continuation1_letstar = AllocatedContPtr::construct(
            &mut cs_letrec.namespace(|| "let* continuation"),
            &g.letstar_cont_tag,
            &[&var, &expanded, env, cont],
            pool,
        )?;

        let continuation_letstar = AllocatedContPtr::pick(
            &mut cs_letrec.namespace(|| "continuation let*"),
            &bindings_is_nil,
            cont,
            &continuation1_letstar,
        )?;

        let expanded2 = Ptr::construct_list(
            &mut cs_letrec.namespace(|| "expanded2"),
            g,
            &[&letrecstar_t, &rest_bindings, &body1],
            pool,
        )?;

        let expanded_star = pick_ptr(
            &mut cs_letrec.namespace(|| "expanded_star"),
            &rest_bindings_is_nil,
            &body1,
            &expanded2,
            pool,
        )?;

        let continuation1_letrecstar = AllocatedContPtr::construct(
            &mut cs_letrec.namespace(|| "letrec* continuation"),
            &g.letrecstar_cont_tag,
            &[&var, &expanded_star, env, cont],
            pool,
        )?;

        let continuation_letrecstar = AllocatedContPtr::pick(
            &mut cs_letrec.namespace(|| "continuation letrec*"),
            &bindings_is_nil,
            cont,
            &continuation1_letrecstar,
        )?;

        (val, continuation_letstar, continuation_letrecstar)
    };

    results.add_clauses_cons(
        *letstar_hash,
        &val,
        env,
        &continuation_letstar,
        &g.false_num,
    );
    results.add_clauses_cons(
        *letrecstar_hash,
        &val,
        env,
        &continuation_letrecstar,
        &g.false_num,
    );

    // head == CONS
    let continuation = AllocatedContPtr::construct(
        &mut cs.namespace(|| "binop cons"),
        &g.binop_cont_tag,
        &[&[&g.op2_cons_tag, &g.default_num], env, &more, cont],
        pool,
    )?;

    results.add_clauses_cons(*cons_hash.value(), &arg1, env, &continuation, &g.false_num);

    // head == CAR
    // let end = more.clone();
    // FIXME: Error if end != NIL.

    // TODO: Factor out the hashing involved in constructing the continuation,
    // since it happens in many of the branches here.
    let continuation = AllocatedContPtr::construct(
        &mut cs.namespace(|| "unop car"),
        &g.unop_cont_tag,
        &[
            &[&g.op1_car_tag, &g.default_num],
            &arg1,
            env,
            &[&g.default_num, &g.default_num],
        ],
        pool,
    )?;

    results.add_clauses_cons(*car_hash.value(), &arg1, env, &continuation, &g.false_num);

    // head == CDR
    // FIXME: Error if end != NIL.
    let continuation = AllocatedContPtr::construct(
        &mut cs.namespace(|| "unop cdr"),
        &g.unop_cont_tag,
        &[
            &[&g.op1_cdr_tag, &g.default_num],
            &arg1,
            env,
            &[&g.default_num, &g.default_num],
        ],
        pool,
    )?;

    results.add_clauses_cons(*cdr_hash.value(), &arg1, env, &continuation, &g.false_num);

    // head == ATOM
    // FIXME: Error if end != NIL.
    let continuation = AllocatedContPtr::construct(
        &mut cs.namespace(|| "unop atom"),
        &g.unop_cont_tag,
        &[
            &[&g.op1_atom_tag, &g.default_num],
            &arg1,
            env,
            &[&g.default_num, &g.default_num],
        ],
        pool,
    )?;

    results.add_clauses_cons(*atom_hash.value(), &arg1, env, &continuation, &g.false_num);

    // head == +
    let continuation = AllocatedContPtr::construct(
        &mut cs.namespace(|| "binop sum"),
        &g.binop_cont_tag,
        &[&[&g.op2_sum_tag, &g.default_num], env, &more, cont],
        pool,
    )?;

    results.add_clauses_cons(*sum_hash.value(), &arg1, env, &continuation, &g.false_num);

    // head == -
    let continuation = AllocatedContPtr::construct(
        &mut cs.namespace(|| "binop diff"),
        &g.binop_cont_tag,
        &[&[&g.op2_diff_tag, &g.default_num], env, &more, cont],
        pool,
    )?;

    results.add_clauses_cons(*diff_hash.value(), &arg1, env, &continuation, &g.false_num);

    // head == *
    let continuation = AllocatedContPtr::construct(
        &mut cs.namespace(|| "binop product"),
        &g.binop_cont_tag,
        &[&[&g.op2_product_tag, &g.default_num], env, &more, cont],
        pool,
    )?;

    results.add_clauses_cons(
        *product_hash.value(),
        &arg1,
        env,
        &continuation,
        &g.false_num,
    );

    // head == /
    let continuation = AllocatedContPtr::construct(
        &mut cs.namespace(|| "binop quotient"),
        &g.binop_cont_tag,
        &[&[&g.op2_quotient_tag, &g.default_num], env, &more, cont],
        pool,
    )?;

    results.add_clauses_cons(
        *quotient_hash.value(),
        &arg1,
        env,
        &continuation,
        &g.false_num,
    );

    // head == =
    let continuation = AllocatedContPtr::construct(
        &mut cs.namespace(|| "Relop NumEqual"),
        &g.relop_cont_tag,
        &[&[&g.rel2_numequal_tag, &g.default_num], env, &more, cont],
        pool,
    )?;

    results.add_clauses_cons(
        *numequal_hash.value(),
        &arg1,
        env,
        &continuation,
        &g.false_num,
    );

    // head == EQ
    let continuation = AllocatedContPtr::construct(
        &mut cs.namespace(|| "Relop Equal"),
        &g.relop_cont_tag,
        &[&[&g.rel2_equal_tag, &g.default_num], env, &more, cont],
        pool,
    )?;

    results.add_clauses_cons(*equal_hash.value(), &arg1, env, &continuation, &g.false_num);

    // head == IF
    let continuation = {
        let unevaled_args = more.clone();
        AllocatedContPtr::construct(
            &mut cs.namespace(|| "If"),
            &g.if_cont_tag,
            &[
                &unevaled_args,
                cont,
                &[&g.default_num, &g.default_num],
                &[&g.default_num, &g.default_num],
            ],
            pool,
        )?
    };

    results.add_clauses_cons(*if_hash.value(), &arg1, env, &continuation, &g.false_num);

    {
        // head == CURRENT-ENV
        // FIXME: Error if rest != NIL.

        results.add_clauses_cons(*current_env_hash.value(), env, env, cont, &g.true_num);
    }

    let (res, continuation) = {
        // head == (FN . ARGS)
        let fun_form = &head;

        let call_continuation = AllocatedContPtr::construct(
            &mut cs.namespace(|| "Call"),
            &g.call_cont_tag,
            &[env, &arg1, cont, &[&g.default_num, &g.default_num]],
            pool,
        )?;

        let expanded_inner = Ptr::construct_list(
            &mut cs.namespace(|| "expanded_inner"),
            g,
            &[fun_form, &arg1],
            pool,
        )?;

        let expanded = Ptr::construct_cons(
            &mut cs.namespace(|| "expanded"),
            g,
            &expanded_inner,
            &more,
            pool,
        )?;

        let more_args_is_nil =
            more.alloc_equal(&mut cs.namespace(|| "more_args_is_nil"), &g.nil_ptr)?;

        let res = pick_ptr(
            &mut cs.namespace(|| "pick res"),
            &more_args_is_nil,
            fun_form,
            &expanded,
            pool,
        )?;

        let continuation = AllocatedContPtr::pick(
            &mut cs.namespace(|| "pick continuation"),
            &more_args_is_nil,
            &call_continuation,
            cont,
        )?;

        (res, continuation)
    };

    let defaults = [
        res.tag(),
        res.hash(),
        env.tag(),
        env.hash(),
        continuation.tag(),
        continuation.hash(),
        &g.false_num,
    ];

    let all_clauses = [
        &results.expr_tag_clauses[..],
        &results.expr_hash_clauses[..],
        &results.env_tag_clauses[..],
        &results.env_hash_clauses[..],
        &results.cont_tag_clauses[..],
        &results.cont_hash_clauses[..],
        &results.invoke_continuation_clauses[..],
    ];

    let case_results = multi_case(
        &mut cs.namespace(|| "input expr hash case"),
        head.hash(),
        &all_clauses,
        &defaults,
    )?;

    let result_expr = ptr_by_index(0, &case_results, pool);
    let result_env = ptr_by_index(1, &case_results, pool);
    let result_cont = AllocatedContPtr::by_index(2, &case_results);
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
    cont: &AllocatedContPtr,
    result: &AllocatedPtr,
    env: &AllocatedPtr,
    not_dummy: &Boolean,
    _witness: &Option<Witness>,
    pool: &Pool,
    g: &GlobalAllocations,
) -> Result<(AllocatedPtr, AllocatedPtr, AllocatedContPtr), SynthesisError> {
    let mut results = Results::default();

    let (computed_cont_hash, cont_components) = ContPtr::allocate_maybe_dummy_components(
        &mut cs.namespace(|| "cont components"),
        cont.get_cont_ptr(pool).as_ref(),
        pool,
    )?;

    let ptr = cont.get_cont_ptr(pool);
    dbg!(
        ptr,
        ptr.map(|p| p.fmt_to_string(pool)),
        not_dummy.get_value(),
        computed_cont_hash.get_value(),
        cont.tag().get_value(),
        cont.hash().get_value(),
    );
    implies_equal!(cs, not_dummy, &computed_cont_hash, cont.hash());

    let (result_expr, saved_env) = {
        // Otherwise, these are the results.
        // Applies to Tail continuations only.
        let saved_env = ptr_by_index(0, &cont_components, pool);

        // Applies to Tail continuations
        let continuation = AllocatedContPtr::by_index(1, &cont_components);

        let thunk_hash = Thunk::hash_components(
            &mut cs.namespace(|| "tail thunk_hash"),
            result,
            &continuation,
        )?;

        let result_expr = AllocatedPtr::from_allocated_parts(g.thunk_tag.clone(), thunk_hash, pool);

        (result_expr, saved_env)
    };

    results.add_clauses_thunk(ContTag::Tail, &result_expr, &saved_env, &g.dummy_ptr);

    results.add_clauses_thunk(ContTag::Outermost, result, env, &g.terminal_ptr);

    let thunk_hash = Thunk::hash_components(&mut cs.namespace(|| "thunk_hash"), result, cont)?;
    let defaults = [
        &g.thunk_tag,
        &thunk_hash,
        env.tag(),
        env.hash(),
        g.dummy_ptr.tag(),
        g.dummy_ptr.hash(),
    ];

    let all_clauses = [
        &results.expr_tag_clauses[..],
        &results.expr_hash_clauses[..],
        &results.env_tag_clauses[..],
        &results.env_hash_clauses[..],
        &results.cont_tag_clauses[..],
        &results.cont_hash_clauses[..],
    ];

    let case_results = multi_case(
        &mut cs.namespace(|| "make_thunk case"),
        cont.tag(),
        &all_clauses,
        &defaults,
    )?;

    let result_expr = ptr_by_index(0, &case_results, pool);
    let result_env = ptr_by_index(1, &case_results, pool);
    let result_cont = AllocatedContPtr::by_index(2, &case_results);

    Ok((result_expr, result_env, result_cont))
}

fn invoke_continuation<CS: ConstraintSystem<Fr>>(
    mut cs: CS,
    cont: &AllocatedContPtr,
    result: &AllocatedPtr,
    env: &AllocatedPtr,
    not_dummy: &Boolean,
    witness: &Option<Witness>,
    pool: &Pool,
    g: &GlobalAllocations,
) -> Result<
    (
        AllocatedPtr,
        AllocatedPtr,
        AllocatedContPtr,
        AllocatedNum<Fr>,
    ),
    SynthesisError,
> {
    let mut results = Results::default();

    // FIXME: Handle Terminal and Dummy continuations,
    // which should return Error continuations, but what else?
    // We need to specify this.

    let picked = {
        // let thunk_continuation = g.destructured_thunk_continuation.clone();
        let thunk_value = g.destructured_thunk_value.clone();
        let thunk_hash = g.destructured_thunk_hash.clone();

        // Enforce (result.tag == thunk_tag) implies (thunk_hash == result.hash).
        let result_is_a_thunk = constraints::alloc_equal(
            &mut cs.namespace(|| "result.tag == thunk_tag"),
            result.tag(),
            &g.thunk_tag,
        )?;
        let result_is_the_thunk = constraints::alloc_equal(
            &mut cs.namespace(|| "thunk_hash = result.hash"),
            &thunk_hash,
            result.hash(),
        )?;
        enforce_implication(
            &mut cs.namespace(|| {
                "(result.tag == thunk_continuation) implies (thunk_hash == result.hash)"
            }),
            &result_is_a_thunk,
            &result_is_the_thunk,
        )?;

        pick_ptr(
            &mut cs.namespace(|| "pick result or thunk"),
            &result_is_a_thunk,
            &thunk_value,
            result,
            pool,
        )?
    };

    results.add_clauses_cont(
        ContTag::Outermost,
        &picked,
        env,
        &g.terminal_ptr,
        &g.false_num,
    );

    let (_continuation_hash, continuation_components) = ContPtr::allocate_maybe_dummy_components(
        &mut cs.namespace(|| "allocate_continuation_components"),
        witness
            .as_ref()
            .and_then(|w| w.invoke_continuation_cont.as_ref()),
        pool,
    )?;

    let (next, the_cont) = {
        // Continuation::Call
        let saved_env = ptr_by_index(0, &continuation_components, pool);
        let arg = ptr_by_index(1, &continuation_components, pool);
        let continuation = AllocatedContPtr::by_index(2, &continuation_components);

        let function = result;
        let next_expr = arg;

        // let call2_components = [g.call2_cont_tag.clone()];
        let newer_cont = AllocatedContPtr::construct(
            &mut cs.namespace(|| "construct newer_cont"),
            &g.call2_cont_tag,
            // Mirrors Continuation::get_hash_components()
            &[
                &saved_env,
                function,
                &continuation,
                &[&g.default_num, &g.default_num],
            ],
            pool,
        )?;

        let result_is_fun =
            alloc_equal(cs.namespace(|| "result_is_fun"), result.tag(), &g.fun_tag)?;

        let next = pick_ptr(
            &mut cs.namespace(|| "call_next"),
            &result_is_fun,
            &next_expr,
            result,
            pool,
        )?;

        let the_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "call_cont"),
            &result_is_fun,
            &newer_cont,
            &g.error_ptr_cont,
        )?;
        (next, the_cont)
    };
    results.add_clauses_cont(ContTag::Call, &next, env, &the_cont, &g.false_num);

    let (body_form, newer_env, tail_cont) = {
        // Continuation::Call2
        let saved_env = ptr_by_index(0, &continuation_components, pool);
        let fun = ptr_by_index(1, &continuation_components, pool);
        let continuation = AllocatedContPtr::by_index(2, &continuation_components);

        {
            let (hash, arg_t, body_t, closed_env) = Ptr::allocate_maybe_fun(
                &mut cs.namespace(|| "allocate Call2 fun"),
                pool,
                fun.ptr(pool).as_ref(),
            )?;

            // BOOKMARK: WHy does this cause unconstrainted variable?
            // Something about the overloaded Options?
            let (body_form, _) = car_cdr(&mut cs.namespace(|| "body_form"), g, &body_t, pool)?;

            let fun_is_correct = constraints::alloc_equal(
                &mut cs.namespace(|| "fun hash is correct"),
                fun.hash(),
                &hash,
            )?;

            let cont_is_call2 = constraints::alloc_equal(
                &mut cs.namespace(|| "Call2 branch taken"),
                cont.tag(),
                &g.call2_cont_tag,
            )?;

            let cont_is_call2_and_not_dummy = and!(cs, &cont_is_call2, not_dummy)?;

            enforce_implication(
                &mut cs.namespace(|| "Call2 implies non-dummy fun"),
                &cont_is_call2_and_not_dummy,
                &fun_is_correct,
            )?;

            let newer_env = extend(
                &mut cs.namespace(|| "Call2 extend env"),
                g,
                &closed_env,
                &arg_t,
                result,
                pool,
            )?;

            let tail_cont = make_tail_continuation(
                &mut cs.namespace(|| "Call2 make_tail_continuation"),
                g,
                &saved_env,
                &continuation,
                pool,
            )?;

            (body_form, newer_env, tail_cont)
        }
    };

    results.add_clauses_cont(
        ContTag::Call2,
        &body_form,
        &newer_env,
        &tail_cont,
        &g.false_num,
    );

    let (body, extended_env, tail_cont) = {
        // Continuation::LetStar
        let var = ptr_by_index(0, &continuation_components, pool);
        let body = ptr_by_index(1, &continuation_components, pool);
        let saved_env = ptr_by_index(2, &continuation_components, pool);
        let cont = AllocatedContPtr::by_index(3, &continuation_components);

        let extended_env = extend(
            &mut cs.namespace(|| "LetStar extend env"),
            g,
            env,
            &var,
            result,
            pool,
        )?;

        let tail_cont = make_tail_continuation(
            &mut cs.namespace(|| "LetStar make_tail_continuation"),
            g,
            &saved_env,
            &cont,
            pool,
        )?;

        (body, extended_env, tail_cont)
    };
    results.add_clauses_cont(
        ContTag::LetStar,
        &body,
        &extended_env,
        &tail_cont,
        &g.false_num,
    );

    let (body, extended_env, return_cont) = {
        // Continuation::LetRecStar
        let var = ptr_by_index(0, &continuation_components, pool);
        let body = ptr_by_index(1, &continuation_components, pool);
        let saved_env = ptr_by_index(2, &continuation_components, pool);
        let cont = AllocatedContPtr::by_index(3, &continuation_components);

        let extended_env = extend_rec(
            &mut cs.namespace(|| "LetRecStar extend_rec env"),
            g,
            env,
            &var,
            result,
            pool,
        )?;

        let is_error = extended_env.alloc_equal(&mut cs.namespace(|| "is_error"), &g.error_ptr)?;

        let tail_cont = make_tail_continuation(
            &mut cs.namespace(|| "LetRecStar make_tail_continuation"),
            g,
            &saved_env,
            &cont,
            pool,
        )?;

        let return_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "return_cont"),
            &is_error,
            &g.error_ptr_cont,
            &tail_cont,
        )?;

        (body, extended_env, return_cont)
    };

    results.add_clauses_cont(
        ContTag::LetRecStar,
        &body,
        &extended_env,
        &return_cont,
        &g.false_num,
    );

    let unop_val = {
        // Continuation::Unop
        let op1 = ptr_by_index(0, &continuation_components, pool);

        let (allocated_car, allocated_cdr) =
            car_cdr(&mut cs.namespace(|| "Unop cons"), g, result, pool)?;

        let result_is_cons = alloc_equal(
            &mut cs.namespace(|| "result_is_cons"),
            result.tag(),
            &g.cons_tag,
        )?;

        let atom_ptr = pick_ptr(
            &mut cs.namespace(|| "atom val"),
            &result_is_cons,
            &g.nil_ptr,
            &g.t_ptr,
            pool,
        )?;

        let res = multi_case(
            &mut cs.namespace(|| "Unop case"),
            op1.tag(),
            &[
                &[
                    CaseClause {
                        key: Op1::Car.as_field(),
                        value: allocated_car.tag(),
                    },
                    CaseClause {
                        key: Op1::Cdr.as_field(),
                        value: allocated_cdr.tag(),
                    },
                    CaseClause {
                        key: Op1::Atom.as_field(),
                        value: atom_ptr.tag(),
                    },
                ],
                &[
                    CaseClause {
                        key: Op1::Car.as_field(),
                        value: allocated_car.hash(),
                    },
                    CaseClause {
                        key: Op1::Cdr.as_field(),
                        value: allocated_cdr.hash(),
                    },
                    CaseClause {
                        key: Op1::Atom.as_field(),
                        value: atom_ptr.hash(),
                    },
                ],
            ],
            &[&g.default_num, &g.default_num, &g.default_num],
        )?;

        ptr_by_index(0, &res, pool)
    };

    let continuation = AllocatedContPtr::by_index(1, &continuation_components);

    results.add_clauses_cont(ContTag::Unop, &unop_val, env, &continuation, &g.true_num);

    let (allocated_arg2, saved_env, binop2_cont) = {
        // Continuation::Binop
        let op2 = &continuation_components[0];
        let saved_env = ptr_by_index(1, &continuation_components, pool);
        let unevaled_args = ptr_by_index(2, &continuation_components, pool);
        let continuation = AllocatedContPtr::by_index(3, &continuation_components);

        let (allocated_arg2, _allocated_rest) =
            car_cdr(&mut cs.namespace(|| "Binop cons"), g, &unevaled_args, pool)?;

        let binop2_cont = AllocatedContPtr::construct(
            &mut cs.namespace(|| "Binop2"),
            &g.binop2_cont_tag,
            &[
                &[op2, &g.default_num],
                result,
                &continuation,
                &[&g.default_num, &g.default_num],
            ],
            pool,
        )?;

        (allocated_arg2, saved_env, binop2_cont)
    };

    // FIXME: If allocated_rest != Nil, then error.
    results.add_clauses_cont(
        ContTag::Binop,
        &allocated_arg2,
        &saved_env,
        &binop2_cont,
        &g.false_num,
    );

    let (res, c) = {
        // Continuation::Binop2
        let op2 = ptr_by_index(0, &continuation_components, pool);
        let arg1 = ptr_by_index(1, &continuation_components, pool);
        let continuation = AllocatedContPtr::by_index(3, &continuation_components);

        let arg2 = result;

        let arg1_is_num = alloc_equal(&mut cs.namespace(|| "arg1_is_num"), arg1.tag(), &g.num_tag)?;
        let arg2_is_num = alloc_equal(&mut cs.namespace(|| "arg2_is_num"), arg2.tag(), &g.num_tag)?;
        let both_args_are_nums = Boolean::and(
            &mut cs.namespace(|| "both_args_are_nums"),
            &arg1_is_num,
            &arg2_is_num,
        )?;

        let (a, b) = (arg1.hash(), arg2.hash()); // For Nums, the 'hash' is an immediate value.

        let not_dummy = alloc_equal(
            &mut cs.namespace(|| "Binop2 not dummy"),
            cont.tag(),
            &g.binop2_cont_tag,
        )?;

        let sum = constraints::add(&mut cs.namespace(|| "sum"), a, b)?;
        let diff = constraints::sub(&mut cs.namespace(|| "difference"), a, b)?;
        let product = constraints::mul(&mut cs.namespace(|| "product"), a, b)?;

        // FIXME: We need to check that b is not zero, returning an error if so.

        // In dummy paths, we need to use a non-zero dummy value for b.
        let divisor = //if dummy then 1 otherwise b.
            pick(&mut cs.namespace(||"maybe-dummy divisor"),
                 &not_dummy,
                 b,
                 &g.true_num,
                 )?;

        let quotient = constraints::div(&mut cs.namespace(|| "quotient"), a, &divisor)?;

        let cons = Ptr::construct_cons(&mut cs.namespace(|| "cons"), g, &arg1, arg2, pool)?;

        let val = case(
            &mut cs.namespace(|| "Binop2 case"),
            op2.tag(),
            &[
                CaseClause {
                    key: Op2::Sum.as_field(),
                    value: &sum,
                },
                CaseClause {
                    key: Op2::Diff.as_field(),
                    value: &diff,
                },
                CaseClause {
                    key: Op2::Product.as_field(),
                    value: &product,
                },
                CaseClause {
                    key: Op2::Quotient.as_field(),
                    value: &quotient,
                },
                CaseClause {
                    key: Op2::Cons.as_field(),
                    value: cons.hash(),
                },
            ],
            &g.default_num,
        )?;

        let is_cons = alloc_equal(
            &mut cs.namespace(|| "Op2 is Cons"),
            op2.tag(),
            &g.op2_cons_tag,
        )?;

        let res_tag = pick(
            &mut cs.namespace(|| "Op2 result tag"),
            &is_cons,
            &g.cons_tag,
            &g.num_tag,
        )?;

        let res = AllocatedPtr::from_allocated_parts(res_tag, val, pool);

        let valid_types = constraints::or(
            &mut cs.namespace(|| "Op2 called with valid types"),
            &is_cons,
            &both_args_are_nums,
        )?;

        // FIXME: error if op2 is not actually an Op2.
        // Currently, this will return the default value, treated as Num.

        let c = AllocatedContPtr::pick(
            &mut cs.namespace(|| "maybe type error"),
            &valid_types,
            &continuation,
            &g.error_ptr_cont,
        )?;

        (res, c)
    };

    results.add_clauses_cont(ContTag::Binop2, &res, env, &c, &g.true_num);

    let (allocated_arg2, saved_env, relop2_cont) = {
        // Continuation::Relop
        let relop2 = &continuation_components[0];
        let saved_env = ptr_by_index(1, &continuation_components, pool);
        let unevaled_args = ptr_by_index(2, &continuation_components, pool);
        let continuation = AllocatedContPtr::by_index(3, &continuation_components);

        let (allocated_arg2, _allocated_rest) =
            car_cdr(&mut cs.namespace(|| "Relops cons"), g, &unevaled_args, pool)?;

        // FIXME: If allocated_rest != Nil, then error.
        let relop2_cont = AllocatedContPtr::construct(
            &mut cs.namespace(|| "Relop2"),
            &g.relop2_cont_tag,
            &[
                &[relop2, &g.default_num],
                result,
                &continuation,
                &[&g.default_num, &g.default_num],
            ],
            pool,
        )?;

        (allocated_arg2, saved_env, relop2_cont)
    };

    results.add_clauses_cont(
        ContTag::Relop,
        &allocated_arg2,
        &saved_env,
        &relop2_cont,
        &g.false_num,
    );

    let (res, continuation) = {
        // Continuation::Relop2
        let rel2 = ptr_by_index(0, &continuation_components, pool);
        let arg1 = ptr_by_index(1, &continuation_components, pool);
        let continuation = AllocatedContPtr::by_index(2, &continuation_components);
        let arg2 = result;

        let tags_equal = alloc_equal(
            &mut cs.namespace(|| "Relop2 tags equal"),
            arg1.tag(),
            arg2.tag(),
        )?;

        let vals_equal = alloc_equal(
            &mut cs.namespace(|| "Relop2 vals equal"),
            arg1.hash(),
            arg2.hash(),
        )?;

        let tag_is_num = alloc_equal(
            &mut cs.namespace(|| "arg1 tag is num"),
            arg1.tag(),
            &g.num_tag,
        )?;

        let rel2_is_equal = alloc_equal(
            &mut cs.namespace(|| "rel2 tag is Equal"),
            rel2.tag(),
            &g.rel2_equal_tag,
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

        let res = pick_ptr(
            &mut cs.namespace(|| "res"),
            &boolean_res,
            &g.t_ptr,
            &g.nil_ptr,
            pool,
        )?;

        // FIXME: Still need to handle:
        // - bad rel2 value (bad input)
        // - NumEqual rel2 without both args being Num (type error).
        (res, continuation)
    };
    results.add_clauses_cont(ContTag::Relop2, &res, env, &continuation, &g.true_num);

    let (res, continuation) = {
        // Continuation::If
        let unevaled_args = ptr_by_index(0, &continuation_components, pool);
        let continuation = AllocatedContPtr::by_index(1, &continuation_components);

        let condition = result;

        // NOTE: There was a tricky bug here.
        // When the actual continuation was Relop, and the operation is Numequal (for example),
        // Then this appears to be an invalid but not dummy continuation, since Numequal has a Relop tag value of 1,
        // the same as Cons.
        //
        // We address this by adding 2 to the tags returned by Op2 and Rel2 fr() methods, so this collision cannot happen.
        // TODO: It might make even more sense to make all disjoint.
        let (arg1, more) = car_cdr(
            &mut cs.namespace(|| "If unevaled_args cons"),
            g,
            &unevaled_args,
            pool,
        )?;

        let condition_is_nil =
            condition.alloc_equal(&mut cs.namespace(|| "condition is nil"), &g.nil_ptr)?;

        let (arg2, _end) = car_cdr(&mut cs.namespace(|| "If more cons"), g, &more, pool)?;

        let res = pick_ptr(
            &mut cs.namespace(|| "pick arg1 or arg2"),
            &condition_is_nil,
            &arg2,
            &arg1,
            pool,
        )?;
        (res, continuation)
    };

    results.add_clauses_cont(ContTag::If, &res, env, &continuation, &g.false_num);

    // Continuation::Lookup
    let saved_env = ptr_by_index(0, &continuation_components, pool);
    let continuation = AllocatedContPtr::by_index(1, &continuation_components);
    results.add_clauses_cont(
        ContTag::Lookup,
        result,
        &saved_env,
        &continuation,
        &g.true_num,
    );

    // Continuation::Simple
    let continuation = AllocatedContPtr::by_index(0, &continuation_components);
    results.add_clauses_cont(ContTag::Simple, result, env, &continuation, &g.true_num);

    // Continuation::Tail
    let saved_env = ptr_by_index(0, &continuation_components, pool);
    let continuation = AllocatedContPtr::by_index(1, &continuation_components);

    results.add_clauses_cont(
        ContTag::Tail,
        result,
        &saved_env,
        &continuation,
        &g.true_num,
    );

    let all_clauses = [
        &results.expr_tag_clauses[..],
        &results.expr_hash_clauses[..],
        &results.env_tag_clauses[..],
        &results.env_hash_clauses[..],
        &results.cont_tag_clauses[..],
        &results.cont_hash_clauses[..],
        &results.make_thunk_num_clauses[..],
    ];
    let defaults = [
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.false_num,
    ];

    let case_results = multi_case(
        &mut cs.namespace(|| "invoke_continuation case"),
        cont.tag(),
        &all_clauses,
        &defaults,
    )?;

    for i in 0..7 {
        dbg!(i);
        dbg!(&all_clauses[i]);
        dbg!(defaults[i].get_value());
        dbg!(case_results[i].get_value());
    }

    let result_expr = ptr_by_index(0, &case_results, pool);
    let result_env = ptr_by_index(1, &case_results, pool);
    let result_cont = AllocatedContPtr::by_index(2, &case_results);
    let make_thunk_num = case_results[6].clone();

    Ok((result_expr, result_env, result_cont, make_thunk_num))
}

fn car_cdr<CS: ConstraintSystem<Fr>>(
    mut cs: CS,
    g: &GlobalAllocations,
    maybe_cons: &AllocatedPtr,
    pool: &Pool,
) -> Result<(AllocatedPtr, AllocatedPtr), SynthesisError> {
    // A dummy value will never have the cons tag.
    let not_dummy = alloc_equal(
        &mut cs.namespace(|| "not_dummy"),
        maybe_cons.tag(),
        &g.cons_tag,
    )?;

    let (car, cdr) = if not_dummy.get_value().expect("not_dummy missing") {
        if let Some(ptr) = maybe_cons.ptr(pool).as_ref() {
            pool.car_cdr(&ptr)
        } else {
            // Dummy
            (pool.alloc_nil(), pool.alloc_nil())
        }
    } else {
        // Dummy
        (pool.alloc_nil(), pool.alloc_nil())
    };

    dbg!(maybe_cons, &car, &cdr);
    let allocated_car = car.allocate_ptr(&mut cs.namespace(|| "car"), pool)?;
    let allocated_cdr = cdr.allocate_ptr(&mut cs.namespace(|| "cdr"), pool)?;
    dbg!(&allocated_car, &allocated_cdr);

    let constructed_cons = Ptr::construct_cons(
        &mut cs.namespace(|| "cons"),
        g,
        &allocated_car,
        &allocated_cdr,
        pool,
    )?;

    let real_cons = alloc_equal(
        &mut cs.namespace(|| "cons is real"),
        maybe_cons.hash(),
        constructed_cons.hash(),
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
    env: &AllocatedPtr,
    var: &AllocatedPtr,
    val: &AllocatedPtr,
    pool: &Pool,
) -> Result<AllocatedPtr, SynthesisError> {
    let new_binding =
        Ptr::construct_cons(&mut cs.namespace(|| "extend binding"), g, var, val, pool)?;
    Ptr::construct_cons(cs, g, &new_binding, env, pool)
}

fn extend_rec<CS: ConstraintSystem<Fr>>(
    mut cs: CS,
    g: &GlobalAllocations,
    env: &AllocatedPtr,
    var: &AllocatedPtr,
    val: &AllocatedPtr,
    pool: &Pool,
) -> Result<AllocatedPtr, SynthesisError> {
    let (binding_or_env, rest) = car_cdr(&mut cs.namespace(|| "car_cdr env"), g, env, pool)?;
    let (var_or_binding, _val_or_more_bindings) = car_cdr(
        &mut cs.namespace(|| "car_cdr binding_or_env"),
        g,
        &binding_or_env,
        pool,
    )?;

    let cons = Ptr::construct_cons(&mut cs.namespace(|| "cons var val"), g, var, val, pool)?;
    let list = Ptr::construct_list(&mut cs.namespace(|| "list cons"), g, &[&cons], pool)?;

    let new_env_if_sym_or_nil = Ptr::construct_cons(
        &mut cs.namespace(|| "new_env_if_sym_or_nil"),
        g,
        &list,
        env,
        pool,
    )?;

    let cons2 = Ptr::construct_cons(
        &mut cs.namespace(|| "cons cons binding_or_env"),
        g,
        &cons,
        &binding_or_env,
        pool,
    )?;

    let cons3 = Ptr::construct_cons(
        &mut cs.namespace(|| "cons cons2 rest"),
        g,
        &cons2,
        &rest,
        pool,
    )?;

    let is_sym = constraints::alloc_equal(
        &mut cs.namespace(|| "var_or_binding is sym"),
        var_or_binding.tag(),
        &g.sym_tag,
    )?;

    let is_nil = constraints::alloc_equal(
        &mut cs.namespace(|| "var_or_binding is nil"),
        var_or_binding.tag(),
        g.nil_ptr.tag(),
    )?;

    let is_sym_or_nil = or!(cs, &is_sym, &is_nil)?;

    let is_cons = constraints::alloc_equal(
        &mut cs.namespace(|| "var_or_binding is cons"),
        var_or_binding.tag(),
        &g.cons_tag,
    )?;

    let new_env_if_cons = pick_ptr(
        &mut cs.namespace(|| "new_env_if_cons"),
        &is_cons,
        &cons3,
        &g.error_ptr, // This is being used as a signal, since extend_rec is expected to return a valid env.
        pool,
    )?;

    pick_ptr(
        &mut cs.namespace(|| "extend_rec result"),
        &is_sym_or_nil,
        &new_env_if_sym_or_nil,
        &new_env_if_cons,
        pool,
    )
}

fn make_tail_continuation<CS: ConstraintSystem<Fr>>(
    mut cs: CS,
    g: &GlobalAllocations,
    env: &AllocatedPtr,
    continuation: &AllocatedContPtr,
    pool: &Pool,
) -> Result<AllocatedContPtr, SynthesisError> {
    let continuation_is_tail = alloc_equal(
        &mut cs.namespace(|| "continuation is tail"),
        continuation.tag(),
        &g.tail_cont_tag,
    )?;

    let new_tail = AllocatedContPtr::construct(
        &mut cs.namespace(|| "new tail continuation"),
        &g.tail_cont_tag,
        &[
            env,
            continuation,
            &[&g.default_num, &g.default_num],
            &[&g.default_num, &g.default_num],
        ],
        pool,
    )?;

    AllocatedContPtr::pick(
        &mut cs.namespace(|| "the tail continuation"),
        &continuation_is_tail,
        &continuation,
        &new_tail,
    )
}

fn ptr_by_index(n: usize, case_results: &[AllocatedNum<Fr>], pool: &Pool) -> AllocatedPtr {
    AllocatedPtr::from_allocated_parts(
        case_results[n * 2].clone(),
        case_results[1 + n * 2].clone(),
        pool,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::{empty_sym_env, Evaluable, IO};
    use crate::pool::Pool;
    use crate::proof::Provable;
    use bellperson::groth16;
    use bellperson::util_cs::{
        metric_cs::MetricCS, test_cs::TestConstraintSystem, Comparable, Delta,
    };

    #[test]
    fn num_self_evaluating() {
        let mut pool = Pool::default();
        let env = empty_sym_env(&pool);
        let num = pool.alloc_num(123);

        let input = IO {
            expr: num,
            env,
            cont: pool.alloc_cont_outermost(),
        };

        let initial = input.clone();
        let (_, witness) = input.eval(&mut pool);

        let groth_params = CircuitFrame::groth_params().unwrap();
        let vk = &groth_params.vk;
        let pvk = groth16::prepare_verifying_key(vk);

        let test_with_output = |output: IO, expect_success: bool, pool: &Pool| {
            let mut cs = TestConstraintSystem::new();

            let mut cs_blank = MetricCS::<Fr>::new();
            let blank_frame = CircuitFrame::blank(pool);
            blank_frame
                .synthesize(&mut cs_blank)
                .expect("failed to synthesize");

            let frame = CircuitFrame::from_frame(
                initial.clone(),
                Frame {
                    input: input.clone(),
                    output,
                    i: 0,
                    witness: witness.clone(),
                },
                pool,
            );

            frame
                .clone()
                .synthesize(&mut cs)
                .expect("failed to synthesize");

            let delta = cs.delta(&cs_blank, false);
            assert!(delta == Delta::Equal);

            assert_eq!(32499, cs.num_constraints());
            assert_eq!(20, cs.num_inputs());
            assert_eq!(32455, cs.aux().len());

            let public_inputs = frame.public_inputs(pool);
            let mut rng = rand::thread_rng();

            let proof = frame.clone().prove(Some(&groth_params), &mut rng).unwrap();
            let cs_verified = cs.is_satisfied() && cs.verify(&public_inputs);
            let verified = frame.verify_groth16_proof(&pvk, proof).unwrap();

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
                cont: pool.alloc_cont_terminal(),
            };

            test_with_output(output, true, &pool);
        }

        // Failure
        {
            // Wrong type, so tag should differ.
            let bad_output_tag = IO {
                expr: pool.alloc_sym("SYMBOL"),
                env,
                cont: pool.alloc_cont_terminal(),
            };

            test_with_output(bad_output_tag, false, &pool);
        }

        {
            // Wrong value, so hash should differ.
            let bad_output_value = IO {
                expr: pool.alloc_num(999),
                env,
                cont: pool.alloc_cont_terminal(),
            };

            test_with_output(bad_output_value, false, &pool);
        }

        {
            // Wrong new env.
            let bad_output_tag = IO {
                expr: num,
                env: pool.alloc_sym("not-an-env"),
                cont: pool.alloc_cont_terminal(),
            };

            test_with_output(bad_output_tag, false, &pool);
        }
    }

    #[test]
    fn nil_self_evaluating() {
        let mut pool = Pool::default();
        let env = empty_sym_env(&pool);
        let nil = pool.alloc_nil();

        let input = IO {
            expr: nil,
            env,
            cont: pool.alloc_cont_outermost(),
        };

        let initial = input.clone();
        let (_, witness) = input.eval(&mut pool);

        let test_with_output = |output: IO, expect_success: bool, pool: &Pool| {
            let mut cs = TestConstraintSystem::new();

            let frame = Frame {
                input: input.clone(),
                output,
                i: 0,
                witness: witness.clone(),
            };

            CircuitFrame::from_frame(initial.clone(), frame, pool)
                .synthesize(&mut cs)
                .expect("failed to synthesize");

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
                cont: pool.alloc_cont_terminal(),
            };

            test_with_output(output, true, &pool);
        }

        // Failure
        {
            {
                // Wrong type, so tag should differ.
                let bad_output_tag = IO {
                    expr: pool.alloc_sym("SYMBOL"),
                    env,
                    cont: pool.alloc_cont_terminal(),
                };

                test_with_output(bad_output_tag, false, &pool);
            }
            {
                // Wrong value, so hash should differ.
                let bad_output_value = IO {
                    expr: pool.alloc_num(999),
                    env: env.clone(),
                    cont: pool.alloc_cont_terminal(),
                };

                test_with_output(bad_output_value, false, &pool);
            }
        }
    }

    //#[test]
    #[allow(dead_code)]
    fn t_self_evaluating() {
        let mut pool = Pool::default();
        let env = empty_sym_env(&pool);
        let t = pool.alloc_sym("T");

        let input = IO {
            expr: t,
            env,
            cont: pool.alloc_cont_outermost(),
        };

        let initial = input.clone();
        // let witness = input.compute_witness(&mut pool);

        let (_, witness) = input.eval(&mut pool);

        let test_with_output = |output: IO, expect_success: bool, pool: &Pool| {
            let mut cs = TestConstraintSystem::new();

            let frame = Frame {
                input: input.clone(),
                output,
                i: 0,
                witness: witness.clone(),
            };

            CircuitFrame::from_frame(initial.clone(), frame, pool)
                .synthesize(&mut cs)
                .expect("failed to synthesize");

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
                cont: pool.alloc_cont_terminal(),
            };

            test_with_output(output, true, &pool);
        }

        // Failure
        {
            {
                // Wrong type, so tag should differ.
                let bad_output_tag = IO {
                    expr: pool.alloc_num(999),
                    env,
                    cont: pool.alloc_cont_terminal(),
                };

                test_with_output(bad_output_tag, false, &pool);
            }
            {
                // Wrong symbol, so hash should differ.
                let bad_output_value = IO {
                    expr: pool.alloc_sym("S"),
                    env: env.clone(),
                    cont: pool.alloc_cont_terminal(),
                };
                test_with_output(bad_output_value, false, &pool);
            }
        }
    }

    #[test]
    fn fun_self_evaluating() {
        let mut pool = Pool::default();
        let env = empty_sym_env(&pool);
        let var = pool.alloc_sym("a");
        let body = pool.alloc_list(&[var]);
        let fun = pool.alloc_fun(var, body, env);

        let input = IO {
            expr: fun.clone(),
            env: env.clone(),
            cont: pool.alloc_cont_outermost(),
        };

        let initial = input.clone();
        let (_, witness) = input.eval(&mut pool);

        let test_with_output = |output: IO, expect_success: bool, pool: &Pool| {
            let mut cs = TestConstraintSystem::new();

            let frame = Frame {
                input: input.clone(),
                output,
                i: 0,
                witness: witness.clone(),
            };

            CircuitFrame::from_frame(initial.clone(), frame, pool)
                .synthesize(&mut cs)
                .expect("failed to synthesize");

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
                cont: pool.alloc_cont_terminal(),
            };

            test_with_output(output, true, &pool);
        }

        // Failure
        {
            {
                // Wrong type, so tag should differ.
                let bad_output_tag = IO {
                    expr: pool.alloc_sym("SYMBOL"),
                    env: env.clone(),
                    cont: pool.alloc_cont_terminal(),
                };

                test_with_output(bad_output_tag, false, &pool);
            }
            {
                // Wrong value, so hash should differ.
                let bad_output_value = IO {
                    expr: pool.alloc_num(999),
                    env: env.clone(),
                    cont: pool.alloc_cont_terminal(),
                };

                test_with_output(bad_output_value, false, &pool);
            }
        }
    }

    //#[test]
    #[allow(dead_code)]
    fn non_self_evaluating() {
        let mut pool = Pool::default();
        let env = empty_sym_env(&pool);

        // Input is not self-evaluating.
        let expr = pool.read("(+ 1 2)").unwrap();
        let input = IO {
            expr: expr.clone(),
            env: env.clone(),
            cont: pool.alloc_cont_outermost(),
        };

        let initial = input.clone();
        let (_, witness) = input.eval(&mut pool);

        let test_with_output = |output, expect_success, pool: &mut Pool| {
            let mut cs = TestConstraintSystem::new();

            let frame = Frame {
                input: input.clone(),
                output,
                i: 0,
                witness: witness.clone(),
            };

            CircuitFrame::from_frame(initial.clone(), frame, &pool)
                .synthesize(&mut cs)
                .expect("failed to synthesize");

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
                    expr: pool.alloc_num(987),
                    env,
                    cont: pool.alloc_cont_terminal(),
                };

                test_with_output(output, true, &mut pool);
            }
            {
                // However, output is permitted to equal input.
                // Input could theoretically be a single-step quine.
                // This is impossible in the current language for other reasons.
                let output = IO {
                    expr: expr.clone(),
                    env: env.clone(),
                    cont: pool.alloc_cont_terminal(),
                };

                test_with_output(output, true, &mut pool);
            }
        }
    }
}
