use std::fmt::Debug;

use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    util_cs::Comparable,
    Circuit, ConstraintSystem, SynthesisError,
};

use crate::{
    circuit::gadgets::{
        case::{case, multi_case, multi_case_aux, CaseClause},
        data::GlobalAllocations,
        pointer::{AllocatedContPtr, AllocatedPtr, AsAllocatedHashComponents},
    },
    field::LurkField,
    store::ScalarPointer,
};

use super::gadgets::constraints::{
    self, alloc_equal, alloc_is_zero, boolean_to_num, enforce_implication, or, pick,
};
use crate::circuit::ToInputs;
use crate::eval::{Frame, Witness, IO};
use crate::proof::Provable;
use crate::store::{ContPtr, ContTag, Op1, Op2, Ptr, Store, Tag, Thunk};

#[derive(Clone, Copy, Debug)]
pub struct CircuitFrame<'a, F: LurkField, T, W> {
    pub store: Option<&'a Store<F>>,
    pub input: Option<T>,
    pub output: Option<T>,
    pub witness: Option<W>,
}

#[derive(Clone)]
pub struct MultiFrame<'a, F: LurkField, T: Copy, W> {
    pub store: Option<&'a Store<F>>,
    pub input: Option<T>,
    pub output: Option<T>,
    pub frames: Option<Vec<CircuitFrame<'a, F, T, W>>>,
    pub count: usize,
}

impl<'a, F: LurkField, T: Clone + Copy, W: Copy> CircuitFrame<'a, F, T, W> {
    pub fn blank() -> Self {
        Self {
            store: None,
            input: None,
            output: None,
            witness: None,
        }
    }

    pub fn from_frame(frame: &Frame<T, W>, store: &'a Store<F>) -> Self {
        CircuitFrame {
            store: Some(store),
            input: Some(frame.input),
            output: Some(frame.output),
            witness: Some(frame.witness),
        }
    }
}

impl<'a, F: LurkField, T: Clone + Copy + std::cmp::PartialEq, W: Copy> MultiFrame<'a, F, T, W> {
    pub fn blank(count: usize) -> Self {
        Self {
            store: None,
            input: None,
            output: None,
            frames: None,
            count,
        }
    }

    pub fn get_store(&self) -> &Store<F> {
        self.store.expect("store missing")
    }

    pub fn frame_count(&self) -> usize {
        self.count
    }

    pub fn from_frames(count: usize, frames: &[Frame<T, W>], store: &'a Store<F>) -> Vec<Self> {
        // `count` is the number of `Frames` to include per `MultiFrame`.
        let total_frames = frames.len();
        let n = total_frames / count + (total_frames % count != 0) as usize;
        let mut multi_frames = Vec::with_capacity(n);

        for chunk in frames.chunks(count) {
            let mut inner_frames = Vec::with_capacity(count);

            for x in chunk {
                let circuit_frame = CircuitFrame::from_frame(x, store);
                inner_frames.push(circuit_frame);
            }

            let last_frame = chunk.last().expect("chunk must not be empty");
            let last_circuit_frame = *inner_frames.last().expect("chunk must not be empty");

            // Fill out the MultiFrame, if needed, and capture output of the final actual frame.
            for _ in chunk.len()..count {
                inner_frames.push(last_circuit_frame);
            }

            let output = last_frame.output;
            debug_assert!(!inner_frames.is_empty());

            let mf = MultiFrame {
                store: Some(store),
                input: Some(chunk[0].input),
                output: Some(output),
                frames: Some(inner_frames),
                count,
            };

            multi_frames.push(mf);
        }

        multi_frames
    }

    /// Make a dummy `MultiFrame`, duplicating `self`'s final `CircuitFrame`.
    pub(crate) fn make_dummy(
        count: usize,
        circuit_frame: Option<CircuitFrame<'a, F, T, W>>,
        store: &'a Store<F>,
    ) -> Self {
        let (frames, input, output) = if let Some(circuit_frame) = circuit_frame {
            (
                Some(vec![circuit_frame; count]),
                circuit_frame.input,
                circuit_frame.output,
            )
        } else {
            (None, None, None)
        };
        Self {
            store: Some(store),
            input,
            output,
            frames,
            count,
        }
    }
}

impl<F: LurkField, T: PartialEq + Debug, W> CircuitFrame<'_, F, T, W> {
    pub fn precedes(&self, maybe_next: &Self) -> bool {
        self.output == maybe_next.input
    }
}

impl<F: LurkField, T: PartialEq + Debug + Copy, W> MultiFrame<'_, F, T, W> {
    pub fn precedes(&self, maybe_next: &Self) -> bool {
        self.output == maybe_next.input
    }
}

impl<F: LurkField, W: Copy> Provable<F> for MultiFrame<'_, F, IO<F>, W> {
    fn public_inputs(&self) -> Vec<F> {
        let mut inputs: Vec<_> = Vec::with_capacity(Self::public_input_size());

        if let Some(input) = &self.input {
            inputs.extend(input.to_inputs(self.get_store()));
        } else {
            panic!("public inputs for blank circuit");
        }
        if let Some(output) = &self.output {
            inputs.extend(output.to_inputs(self.get_store()));
        } else {
            panic!("public outputs for blank circuit");
        }

        inputs
    }

    fn public_input_size() -> usize {
        let input_output_size = IO::<F>::input_size();
        input_output_size * 2
    }

    fn chunk_frame_count(&self) -> usize {
        self.count
    }
}

type AllocatedIO<F> = (AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>);

impl<F: LurkField> CircuitFrame<'_, F, IO<F>, Witness<F>> {
    pub(crate) fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        i: usize,
        inputs: AllocatedIO<F>,
        g: &GlobalAllocations<F>,
    ) -> Result<AllocatedIO<F>, SynthesisError> {
        let (input_expr, input_env, input_cont) = inputs;
        let mut reduce = |store| {
            reduce_expression(
                &mut cs.namespace(|| format!("reduce expression {}", i)),
                &input_expr,
                &input_env,
                &input_cont,
                &self.witness,
                store,
                g,
            )
        };

        if let Some(store) = self.store {
            reduce(store)
        } else {
            let store = Default::default();
            reduce(&store)
        }
    }
}

impl<F: LurkField> Circuit<F> for MultiFrame<'_, F, IO<F>, Witness<F>> {
    fn synthesize<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        ////////////////////////////////////////////////////////////////////////////////
        // Bind public inputs.
        //
        // Initial input:

        let mut synth = |store,
                         frames: &[CircuitFrame<F, IO<F>, Witness<F>>],
                         input: Option<IO<F>>,
                         output: Option<IO<F>>| {
            let input_expr = AllocatedPtr::bind_input(
                &mut cs.namespace(|| "outer input expression"),
                input.as_ref().map(|input| &input.expr),
                store,
            )?;

            let input_env = AllocatedPtr::bind_input(
                &mut cs.namespace(|| "outer input env"),
                input.as_ref().map(|input| &input.env),
                store,
            )?;

            let input_cont = AllocatedContPtr::bind_input(
                &mut cs.namespace(|| "outer input cont"),
                input.as_ref().map(|input| &input.cont),
                store,
            )?;

            // Final output:
            let output_expr = AllocatedPtr::bind_input(
                &mut cs.namespace(|| "outer output expression"),
                output.as_ref().map(|output| &output.expr),
                store,
            )?;

            let output_env = AllocatedPtr::bind_input(
                &mut cs.namespace(|| "outer output env"),
                output.as_ref().map(|output| &output.env),
                store,
            )?;

            let output_cont = AllocatedContPtr::bind_input(
                &mut cs.namespace(|| "outer output cont"),
                output.as_ref().map(|output| &output.cont),
                store,
            )?;

            //
            // End public inputs.
            ////////////////////////////////////////////////////////////////////////////////
            let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), store)?;

            let acc = (input_expr, input_env, input_cont);

            let (_, (new_expr, new_env, new_cont)) =
                frames.iter().fold((0, acc), |(i, allocated_io), frame| {
                    (i + 1, frame.synthesize(cs, i, allocated_io, &g).unwrap())
                });

            // dbg!(
            //     (&new_expr, &output_expr),
            //     (&new_env, &output_env),
            //     (&new_cont, &output_cont)
            // );

            output_expr.enforce_equal(
                &mut cs.namespace(|| "outer output expr is correct"),
                &new_expr,
            );
            output_env.enforce_equal(
                &mut cs.namespace(|| "outer output env is correct"),
                &new_env,
            );
            output_cont.enforce_equal(
                &mut cs.namespace(|| "outer output cont is correct"),
                &new_cont,
            );

            Ok(())
        };

        let frames = match self.frames {
            Some(f) => f,
            None => vec![CircuitFrame::blank(); self.count],
        };

        match self.store {
            Some(s) => synth(s, &frames, self.input, self.output),
            None => {
                let store = Default::default();
                synth(&store, &frames, self.input, self.output)
            }
        }
    }
}

#[derive(Default)]
struct Results<'a, F: LurkField> {
    expr_tag_clauses: Vec<CaseClause<'a, F>>,
    expr_hash_clauses: Vec<CaseClause<'a, F>>,
    env_tag_clauses: Vec<CaseClause<'a, F>>,
    env_hash_clauses: Vec<CaseClause<'a, F>>,
    cont_tag_clauses: Vec<CaseClause<'a, F>>,
    cont_hash_clauses: Vec<CaseClause<'a, F>>,
    apply_continuation_clauses: Vec<CaseClause<'a, F>>,
    make_thunk_num_clauses: Vec<CaseClause<'a, F>>,
}

fn add_clause<'a, F: LurkField>(
    tag_clauses: &mut Vec<CaseClause<'a, F>>,
    hash_clauses: &mut Vec<CaseClause<'a, F>>,
    key: F,
    expr: &'a AllocatedPtr<F>,
) {
    add_clause_single(tag_clauses, key, expr.tag());
    add_clause_single(hash_clauses, key, expr.hash());
}

fn add_clause_cont<'a, F: LurkField>(
    tag_clauses: &mut Vec<CaseClause<'a, F>>,
    hash_clauses: &mut Vec<CaseClause<'a, F>>,
    key: F,
    cont: &'a AllocatedContPtr<F>,
) {
    add_clause_single(tag_clauses, key, cont.tag());
    add_clause_single(hash_clauses, key, cont.hash());
}

fn add_clause_single<'a, F: LurkField>(
    clauses: &mut Vec<CaseClause<'a, F>>,
    key: F,
    value: &'a AllocatedNum<F>,
) {
    clauses.push(CaseClause { key, value });
}

impl<'a, F: LurkField> Results<'a, F> {
    fn add_clauses_expr(
        &mut self,
        key: Tag,
        result_expr: &'a AllocatedPtr<F>,
        result_env: &'a AllocatedPtr<F>,
        result_cont: &'a AllocatedContPtr<F>,
        result_apply_continuation: &'a AllocatedNum<F>,
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
            &mut self.apply_continuation_clauses,
            key,
            result_apply_continuation,
        );
    }

    fn add_clauses_cons(
        &mut self,
        key: F,
        result_expr: &'a AllocatedPtr<F>,
        result_env: &'a AllocatedPtr<F>,
        result_cont: &'a AllocatedContPtr<F>,
        apply_cont: &'a AllocatedNum<F>,
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
        add_clause_single(&mut self.apply_continuation_clauses, key, apply_cont);
    }

    fn add_clauses_thunk(
        &mut self,
        key: ContTag,
        result_expr: &'a AllocatedPtr<F>,
        result_env: &'a AllocatedPtr<F>,
        result_cont: &'a AllocatedContPtr<F>,
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
        result_expr: &'a AllocatedPtr<F>,
        result_env: &'a AllocatedPtr<F>,
        result_cont: &'a AllocatedContPtr<F>,
        make_thunk_num: &'a AllocatedNum<F>,
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

#[derive(Default)]
struct HashInputResults<'a, F: LurkField> {
    tag_clauses: Vec<CaseClause<'a, F>>,
    components_clauses: [Vec<CaseClause<'a, F>>; 8],
}

impl<'a, F: LurkField> HashInputResults<'a, F> {
    fn add_hash_input_clauses(
        &mut self,
        key: F,
        tag: &'a AllocatedNum<F>,
        components: &'a [&dyn AsAllocatedHashComponents<F>; 4],
    ) {
        add_clause_single(&mut self.tag_clauses, key, tag);
        add_clause_single(
            &mut self.components_clauses[0],
            key,
            components[0].as_allocated_hash_components()[0],
        );
        add_clause_single(
            &mut self.components_clauses[1],
            key,
            components[0].as_allocated_hash_components()[1],
        );
        add_clause_single(
            &mut self.components_clauses[2],
            key,
            components[1].as_allocated_hash_components()[0],
        );
        add_clause_single(
            &mut self.components_clauses[3],
            key,
            components[1].as_allocated_hash_components()[1],
        );
        add_clause_single(
            &mut self.components_clauses[4],
            key,
            components[2].as_allocated_hash_components()[0],
        );
        add_clause_single(
            &mut self.components_clauses[5],
            key,
            components[2].as_allocated_hash_components()[1],
        );
        add_clause_single(
            &mut self.components_clauses[6],
            key,
            components[3].as_allocated_hash_components()[0],
        );
        add_clause_single(
            &mut self.components_clauses[7],
            key,
            components[3].as_allocated_hash_components()[1],
        );
    }
}

#[derive(Default)]
struct CompResults<'a, F: LurkField> {
    same_sign: Vec<CaseClause<'a, F>>,
    a_neg_and_b_not_neg: Vec<CaseClause<'a, F>>,
    a_not_neg_and_b_neg: Vec<CaseClause<'a, F>>,
}
impl<'a, F: LurkField> CompResults<'a, F> {
    fn add_clauses_comp(
        &mut self,
        key: F,
        result_same_sign: &'a AllocatedNum<F>,
        result_a_neg_and_b_not_neg: &'a AllocatedNum<F>,
        result_a_not_neg_and_b_neg: &'a AllocatedNum<F>,
    ) {
        add_clause_single(&mut self.same_sign, key, result_same_sign);
        add_clause_single(
            &mut self.a_neg_and_b_not_neg,
            key,
            result_a_neg_and_b_not_neg,
        );
        add_clause_single(
            &mut self.a_not_neg_and_b_neg,
            key,
            result_a_not_neg_and_b_neg,
        );
    }
}

fn reduce_expression<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    expr: &AllocatedPtr<F>,
    env: &AllocatedPtr<F>,
    cont: &AllocatedContPtr<F>,
    witness: &Option<Witness<F>>,
    store: &Store<F>,
    g: &GlobalAllocations<F>,
) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
    // dbg!("reduce_expression");
    // dbg!(&expr.fetch_and_write_str(store));
    // dbg!(&expr);
    // dbg!(&env.fetch_and_write_str(store));
    // dbg!(&cont.fetch_and_write_cont_str(store), &cont);
    let mut results = Results::default();
    {
        // Self-evaluating expressions
        results.add_clauses_expr(Tag::Nil, expr, env, cont, &g.true_num);
        results.add_clauses_expr(Tag::Num, expr, env, cont, &g.true_num);
        results.add_clauses_expr(Tag::Fun, expr, env, cont, &g.true_num);
        results.add_clauses_expr(Tag::Char, expr, env, cont, &g.true_num);
        results.add_clauses_expr(Tag::Str, expr, env, cont, &g.true_num);
        results.add_clauses_expr(Tag::Comm, expr, env, cont, &g.true_num);
    };

    let cont_is_terminal = alloc_equal(
        &mut cs.namespace(|| "cont_is_terminal"),
        cont.tag(),
        g.terminal_ptr.tag(),
    )?;

    // If expr is a thunk, this will allocate its components and hash, etc.
    // If not, these will be dummies.
    let (expr_thunk_hash, expr_thunk_value, expr_thunk_continuation) =
        expr.allocate_thunk_components(&mut cs.namespace(|| "allocate thunk components"), store)?;
    {
        // Enforce (expr.tag == thunk_tag) implies (expr_thunk_hash == expr.hash).
        let expr_is_a_thunk = constraints::alloc_equal(
            &mut cs.namespace(|| "expr.tag == thunk_tag"),
            expr.tag(),
            &g.thunk_tag,
        )?;
        let expr_is_the_thunk = constraints::alloc_equal(
            &mut cs.namespace(|| "expr_thunk_hash == expr.hash"),
            &expr_thunk_hash,
            expr.hash(),
        )?;

        enforce_implication(
            &mut cs.namespace(|| "(expr.tag == thunk_tag) implies (expr_thunk_hash == expr.hash)"),
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
    let reduce_sym_not_dummy = alloc_equal(
        &mut cs.namespace(|| "reduce_sym_not_dummy"),
        expr.tag(),
        &g.sym_tag,
    )?;
    let cont_is_not_terminal = Boolean::not(&cont_is_terminal);
    let reduce_sym_not_dummy = and!(cs, &reduce_sym_not_dummy, &cont_is_not_terminal)?;

    let (sym_result, sym_env, sym_cont, sym_apply_cont) = reduce_sym(
        &mut cs.namespace(|| "eval Sym"),
        expr,
        env,
        cont,
        &reduce_sym_not_dummy,
        witness,
        store,
        g,
    )?;

    results.add_clauses_expr(Tag::Sym, &sym_result, &sym_env, &sym_cont, &sym_apply_cont);
    // --

    // --
    let reduce_cons_not_dummy = alloc_equal(
        &mut cs.namespace(|| "reduce_cons_not_dummy"),
        expr.tag(),
        &g.cons_tag,
    )?;

    let (cons_result, cons_env, cons_cont, cons_apply_cont) = reduce_cons(
        &mut cs.namespace(|| "eval Cons"),
        expr,
        env,
        cont,
        &reduce_cons_not_dummy,
        witness,
        store,
        g,
    )?;

    results.add_clauses_expr(
        Tag::Cons,
        &cons_result,
        &cons_env,
        &cons_cont,
        &cons_apply_cont,
    );

    // --

    let all_clauses = [
        &results.expr_tag_clauses[..],
        &results.expr_hash_clauses[..],
        &results.env_tag_clauses[..],
        &results.env_hash_clauses[..],
        &results.cont_tag_clauses[..],
        &results.cont_hash_clauses[..],
        &results.apply_continuation_clauses[..],
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
        g,
    )?;

    let first_result_expr_0 = AllocatedPtr::by_index(0, &case_results);
    let first_result_expr = AllocatedPtr::pick(
        &mut cs.namespace(|| "first_result_expr"),
        &cont_is_terminal,
        &g.nil_ptr,
        &first_result_expr_0,
    )?;

    let first_result_env = AllocatedPtr::by_index(1, &case_results);
    let first_result_cont = AllocatedContPtr::by_index(2, &case_results);
    let first_result_apply_continuation: &AllocatedNum<F> = &case_results[6];

    let apply_continuation_boolean_0 = Boolean::not(&alloc_is_zero(
        &mut cs.namespace(|| "apply_continuation_boolean_0"),
        first_result_apply_continuation,
    )?);

    let apply_continuation_boolean = Boolean::and(
        &mut cs.namespace(|| "apply_continuation_boolean"),
        &apply_continuation_boolean_0,
        &Boolean::not(&cont_is_terminal),
    )?;

    let apply_continuation_results = apply_continuation(
        &mut cs.namespace(|| "apply_continuation-make_thunk"),
        &first_result_cont,
        &first_result_expr,
        &first_result_env,
        &apply_continuation_boolean,
        witness,
        store,
        g,
    )?;

    let apply_continuation_make_thunk: AllocatedNum<F> = apply_continuation_results.3;

    let result_expr0 = AllocatedPtr::pick(
        &mut cs.namespace(|| "pick maybe apply_continuation expr"),
        &apply_continuation_boolean,
        &apply_continuation_results.0,
        &first_result_expr,
    )?;

    let result_env0 = AllocatedPtr::pick(
        &mut cs.namespace(|| "pick maybe apply_continuation env"),
        &apply_continuation_boolean,
        &apply_continuation_results.1,
        &first_result_env,
    )?;

    let result_cont0 = AllocatedContPtr::pick(
        &mut cs.namespace(|| "pick maybe apply_continuation cont"),
        &apply_continuation_boolean,
        &apply_continuation_results.2,
        &first_result_cont,
    )?;

    let make_thunk_num = pick(
        &mut cs.namespace(|| "pick make_thunk_boolean"),
        &apply_continuation_boolean,
        &apply_continuation_make_thunk,
        &g.false_num,
    )?;

    // True if make_thunk is called.
    let make_thunk_boolean = Boolean::not(&alloc_is_zero(
        &mut cs.namespace(|| "apply_continuation_make_thunk is zero"),
        &make_thunk_num,
    )?);

    let thunk_results = make_thunk(
        &mut cs.namespace(|| "make_thunk"),
        &result_cont0,
        &result_expr0,
        &result_env0,
        &make_thunk_boolean,
        witness,
        store,
        g,
    )?;

    let result_expr_candidate = AllocatedPtr::pick(
        &mut cs.namespace(|| "pick maybe make_thunk expr"),
        &make_thunk_boolean,
        &thunk_results.0,
        &result_expr0,
    )?;

    let result_env_candidate = AllocatedPtr::pick(
        &mut cs.namespace(|| "pick maybe make_thunk env"),
        &make_thunk_boolean,
        &thunk_results.1,
        &result_env0,
    )?;

    let result_cont_candidate = AllocatedContPtr::pick(
        &mut cs.namespace(|| "pick maybe make_thunk cont"),
        &make_thunk_boolean,
        &thunk_results.2,
        &result_cont0,
    )?;

    // dbg!(&result_expr_candidate.fetch_and_write_str(store));
    // dbg!(&result_env_candidate.fetch_and_write_str(store));
    // dbg!(&result_cont_candidate.fetch_and_write_cont_str(store));
    // dbg!(expr, env, cont);

    let result_expr = AllocatedPtr::<F>::pick(
        &mut cs.namespace(|| "result_expr"),
        &cont_is_terminal,
        expr,
        &result_expr_candidate,
    )?;

    let result_env = AllocatedPtr::<F>::pick(
        &mut cs.namespace(|| "result_env"),
        &cont_is_terminal,
        env,
        &result_env_candidate,
    )?;

    let result_cont = AllocatedContPtr::<F>::pick(
        &mut cs.namespace(|| "result_cont"),
        &cont_is_terminal,
        cont,
        &result_cont_candidate,
    )?;

    // dbg!(&result_expr.fetch_and_write_str(store));
    // dbg!(&result_env.fetch_and_write_str(store));
    // dbg!(&result_cont.fetch_and_write_cont_str(store));
    // dbg!(expr, env, cont);

    Ok((result_expr, result_env, result_cont))
}

fn reduce_sym<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    expr: &AllocatedPtr<F>,
    env: &AllocatedPtr<F>,
    cont: &AllocatedContPtr<F>,
    not_dummy: &Boolean,
    witness: &Option<Witness<F>>,
    store: &Store<F>,
    g: &GlobalAllocations<F>,
) -> Result<
    (
        AllocatedPtr<F>,
        AllocatedPtr<F>,
        AllocatedContPtr<F>,
        AllocatedNum<F>,
    ),
    SynthesisError,
> {
    let output_expr = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "output_expr"), store, || {
        witness
            .as_ref()
            .map(|w| &w.prethunk_output_expr)
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    let output_env = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "output_env"), store, || {
        witness
            .as_ref()
            .map(|w| &w.prethunk_output_env)
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    let output_cont =
        AllocatedContPtr::alloc_cont_ptr(&mut cs.namespace(|| "output_cont"), store, || {
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
        car_cdr(&mut cs.namespace(|| "If unevaled_args cons"), g, env, store)?;

    let env_is_nil = env.alloc_equal(&mut cs.namespace(|| "env is nil"), &g.nil_ptr)?;
    let env_not_nil = Boolean::not(&env_is_nil);

    let otherwise = Boolean::and(
        &mut cs.namespace(|| "otherwise"),
        &sym_otherwise,
        &env_not_nil,
    )?;

    let binding_is_nil = binding.alloc_equal(&mut cs.namespace(|| "binding is nil"), &g.nil_ptr)?;
    let binding_not_nil = Boolean::not(&binding_is_nil);

    let otherwise_and_binding_is_nil = and!(cs, &otherwise, &binding_is_nil)?;
    let otherwise_and_binding_not_nil = and!(cs, &otherwise, &binding_not_nil)?;

    let (var_or_rec_binding, val_or_more_rec_env) =
        car_cdr(&mut cs.namespace(|| "car_cdr binding"), g, &binding, store)?;

    let var_or_rec_binding_is_sym_ = alloc_equal(
        &mut cs.namespace(|| "var_or_rec_binding_is_sym_"),
        var_or_rec_binding.tag(),
        &g.sym_tag,
    )?;
    let var_or_rec_binding_is_sym = Boolean::and(
        &mut cs.namespace(|| "var_or_rec_binding_is_sym"),
        &var_or_rec_binding_is_sym_,
        &otherwise_and_binding_not_nil,
    )?;

    let v = var_or_rec_binding.clone();
    let val = val_or_more_rec_env.clone();
    let v_is_expr1 = expr.alloc_equal(&mut cs.namespace(|| "v_is_expr1"), &v)?;
    let v_not_expr1 = Boolean::not(&v_is_expr1);

    let otherwise_and_sym = and!(cs, &v_not_expr1, &var_or_rec_binding_is_sym)?;
    let v_is_expr1_real = and!(cs, &v_is_expr1, &var_or_rec_binding_is_sym)?;

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
        store,
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

    let apply_cont_bool0 = or!(cs, &sym_is_self_evaluating, &v_is_expr1_real)?;
    let apply_cont_bool = or!(cs, &apply_cont_bool0, &v2_is_expr_real)?;

    let apply_cont_num = ifx!(cs, &apply_cont_bool, &g.true_num, &g.false_num)?;

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
        store,
        &g.lookup_cont_tag,
        // Mirrors Continuation::get_hash_components()
        &[
            env,
            cont,
            &[&g.default_num, &g.default_num],
            &[&g.default_num, &g.default_num],
        ],
    )?;

    let rec_env = binding;

    let (_fun_hash, fun_arg, fun_body, fun_closed_env) = Ptr::allocate_maybe_fun(
        &mut cs.namespace(|| "extend closure"),
        store,
        witness.as_ref().and_then(|w| w.extended_closure.as_ref()),
    )?;

    let extended_env = AllocatedPtr::construct_cons(
        &mut cs.namespace(|| "extended_env"),
        g,
        store,
        &rec_env,
        &fun_closed_env,
    )?;

    let extended_fun = AllocatedPtr::construct_fun(
        &mut cs.namespace(|| "extended_fun"),
        g,
        store,
        &fun_arg,
        &fun_body,
        &extended_env,
    )?;

    let val_to_use = AllocatedPtr::pick(
        &mut cs.namespace(|| "val_to_use"),
        &val2_is_fun,
        &extended_fun,
        &val2,
    )?;

    let smaller_rec_env = val_or_more_rec_env;
    let smaller_rec_env_is_nil =
        smaller_rec_env.alloc_equal(&mut cs.namespace(|| "smaller_rec_env_is_nil"), &g.nil_ptr)?;

    let with_smaller_rec_env = AllocatedPtr::construct_cons(
        &mut cs.namespace(|| "with_smaller_rec_env"),
        g,
        store,
        &smaller_rec_env,
        &smaller_env,
    )?;

    let env_to_use = ifx_t!(
        cs,
        &smaller_rec_env_is_nil,
        &smaller_env,
        &with_smaller_rec_env
    )?;

    // NOTE: The commented-out implies_equal lines in the rest of this function
    // indicate the natural structure of this translation from eval.rs.
    // In order to reduce constraints, duplicated results are factored out below,
    // but the original structure is left intact so it can be checked against
    // the manual optimization.

    let cs = &mut cs.namespace(|| "env_is_nil");
    let cond0_ = and!(cs, &env_is_nil, not_dummy)?;
    let cond0 = and!(cs, &cond0_, &sym_otherwise)?;
    {
        // implies_equal_t!(cs, &cond0, &output_expr, &expr);
        // implies_equal_t!(cs, &cond0, &output_env, &env);
        implies_equal_t!(cs, &cond0, output_cont, g.error_ptr);
    }

    let cs = &mut cs.namespace(|| "sym_is_self_evaluating");
    let cond1_ = and!(cs, &sym_is_self_evaluating, not_dummy)?;
    let cond1 = and!(cs, &cond1_, &env_not_nil)?;

    {
        // implies_equal_t!(cs, &cond1, &output_expr, &expr);
        // implies_equal_t!(cs, &cond1, &output_env, &env);
        // implies_equal_t!(cs, &cond1, &output_cont, &cont);

        implies_equal_t!(cs, &cond1, output_cont, cont);
    }

    let cs = &mut cs.namespace(|| "otherwise_and_binding_is_nil");
    let cond2 = and!(cs, &otherwise_and_binding_is_nil, not_dummy)?;
    {
        // let cond = and!(cs, &otherwise_and_binding_is_nil, not_dummy)?;

        // implies_equal_t!(cs, &cond2, &output_expr, &expr);
        // implies_equal_t!(cs, &cond2, &output_env, &env);
        implies_equal_t!(cs, &cond2, output_cont, g.error_ptr);
    }
    let cs = &mut cs.namespace(|| "v_is_expr1_real");

    let cond3 = and!(cs, &v_is_expr1_real, not_dummy)?;
    {
        implies_equal_t!(cs, &cond3, output_expr, val);
        // implies_equal_t!(cs, &cond3, &output_env, &env);
        // implies_equal_t!(cs, &cond3, &output_cont, &cont);
    }
    let cs = &mut cs.namespace(|| "cont_is_lookup_sym");
    let cond4 = and!(cs, &cont_is_lookup_sym, not_dummy)?;
    {
        // implies_equal_t!(cs, &cond4, &output_expr, &expr);
        implies_equal_t!(cs, &cond4, output_env, smaller_env);

        //implies_equal_t!(cs, &cond, &output_cont, &cont);
    }
    let cs = &mut cs.namespace(|| "cont_not_lookup_sym");
    let cond5_ = and!(cs, &cont_not_lookup_sym, not_dummy)?;
    let cond5 = and!(cs, &cond5_, &otherwise)?;

    {
        // implies_equal_t!(cs, &cond5, &output_expr, &expr);
        implies_equal_t!(cs, &cond5, output_env, smaller_env);
        implies_equal_t!(cs, &cond5, output_cont, lookup_continuation);
    }

    let cs = &mut cs.namespace(|| "v2_is_expr_real");
    let cond6 = and!(cs, &v2_is_expr_real, not_dummy)?;
    {
        implies_equal_t!(cs, &cond6, output_expr, val_to_use);
        // implies_equal_t!(cs, &cond6, &output_env, &env);
        // implies_equal_t!(cs, &cond6, &output_cont, &cont);
    }

    let cs = &mut cs.namespace(|| "otherwise_and_v2_not_expr");
    let cond7 = and!(cs, &otherwise_and_v2_not_expr, not_dummy)?;
    {
        // implies_equal_t!(cs, &cond7, &output_expr, &expr);
        implies_equal_t!(cs, &cond7, output_env, env_to_use);
    }

    let cs = &mut cs.namespace(|| "cont_is_lookup_cons");
    let cond8 = and!(cs, &cont_is_lookup_cons, not_dummy)?;
    // {
    //     // implies_equal_t!(cs, &cond8, &output_cont, &cont);
    // }

    let cs = &mut cs.namespace(|| "cont_not_lookup_cons");
    let cond9_ = and!(cs, &cont_not_lookup_cons, not_dummy)?;
    let cond9 = and!(cs, &cond9_, &otherwise)?;
    {
        implies_equal_t!(cs, &cond9, output_cont, lookup_continuation);
    }

    let cs = &mut cs.namespace(|| "otherwise_neither");
    let cond10 = and!(cs, &otherwise_neither, not_dummy)?;
    {
        // "Bad form"
        implies_equal_t!(cs, &cond10, output_cont, g.error_ptr);
    }

    let conda = or!(cs, &cond1, &cond2)?; // cond1, cond2
    let condb = or!(cs, &cond4, &cond6)?; // cond4, cond6
    let condc = or!(cs, &conda, &cond8)?; // cond1, cond2, cond8

    let condx_ = or!(cs, &cond4, &cond5)?; // cond4, cond5
    let condx = or!(cs, &cond0, &condx_)?; // cond0, con4, cond5
    let condy_ = or!(cs, &cond3, &cond6)?; // cond3, cond6
    let condy = or!(cs, &cond0, &condy_)?; // cond0, cond3, cond6

    // cond1, cond2, cond4, cond5 // cond_expr
    let cond_expr = or!(cs, &conda, &condx)?; // cond0, cond1, cond2, cond4, cond5
    implies_equal_t!(cs, &cond_expr, output_expr, expr);

    // cond1, cond2, cond3, cond6 // cond_env
    let cond_env = or!(cs, &conda, &condy)?; // cond0, cond1, cond2, cond3, cond6
    implies_equal_t!(cs, &cond_env, output_env, env);

    // cond1, cond3, cond4, cond6, cond // cond_cont
    let cond_cont = or!(cs, &condb, &condc)?; // cond1, cond2, cond4, cond6, cond8
    implies_equal_t!(cs, &cond_cont, output_cont, cont);

    Ok((output_expr, output_env, output_cont, apply_cont_num))
}

fn reduce_cons<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    expr: &AllocatedPtr<F>,
    env: &AllocatedPtr<F>,
    cont: &AllocatedContPtr<F>,
    _not_dummy: &Boolean,
    _witness: &Option<Witness<F>>,
    store: &Store<F>,
    g: &GlobalAllocations<F>,
) -> Result<
    (
        AllocatedPtr<F>,
        AllocatedPtr<F>,
        AllocatedContPtr<F>,
        AllocatedNum<F>,
    ),
    SynthesisError,
> {
    let mut hash_default_results = HashInputResults::<'_, F>::default();

    let lambda = g.lambda_ptr.clone();

    let hash_sym = |sym: &str| {
        store
            .get_sym(sym, true)
            .and_then(|s| store.get_hash_sym(s))
            .unwrap()
    };

    let lambda_hash = hash_sym("lambda");
    let quote_hash = hash_sym("quote");
    let let_sym = hash_sym("let");
    let let_t = AllocatedPtr::alloc_constant(&mut cs.namespace(|| "let"), let_sym)?;
    let let_hash = let_sym.value();
    let letrec = hash_sym("letrec");
    let letrec_t = AllocatedPtr::alloc_constant(&mut cs.namespace(|| "letrec"), letrec)?;
    let letrec_hash = letrec.value();
    let cons_hash = hash_sym("cons");
    let strcons_hash = hash_sym("strcons");
    let begin_hash = hash_sym("begin");
    let car_hash = hash_sym("car");
    let cdr_hash = hash_sym("cdr");
    let atom_hash = hash_sym("atom");
    let emit_hash = hash_sym("emit");
    let sum_hash = hash_sym("+");
    let diff_hash = hash_sym("-");
    let product_hash = hash_sym("*");
    let quotient_hash = hash_sym("/");
    let numequal_hash = hash_sym("=");
    let equal_hash = hash_sym("eq");
    let less_hash = hash_sym("<");
    let less_equal_hash = hash_sym("<=");
    let greater_hash = hash_sym(">");
    let greater_equal_hash = hash_sym(">=");
    let current_env_hash = hash_sym("current-env");
    let if_hash = hash_sym("if");
    let hide_hash = hash_sym("hide");
    let commit_hash = hash_sym("commit");
    let num_hash = hash_sym("num");
    let comm_hash = hash_sym("comm");
    let char_hash = hash_sym("char");
    let eval_hash = hash_sym("eval");
    let open_hash = hash_sym("open");
    let secret_hash = hash_sym("secret");

    let (head, rest) = car_cdr(&mut cs.namespace(|| "reduce_cons expr"), g, expr, store)?;

    let rest_is_nil = rest.alloc_equal(&mut cs.namespace(|| "rest_is_nil"), &g.nil_ptr)?;

    // let not_dummy = alloc_equal(&mut cs.namespace(|| "rest is cons"), &rest.tag, &g.cons_tag)?;

    let (arg1, more) = car_cdr(&mut cs.namespace(|| "car_cdr(rest)"), g, &rest, store)?;

    let (car_args, cdr_args) = car_cdr(&mut cs.namespace(|| "car_cdr(arg1)"), g, &arg1, store)?;

    let end_is_nil = more.alloc_equal(&mut cs.namespace(|| "end_is_nil"), &g.nil_ptr)?;

    let mut results = Results::default();

    // --
    let function = {
        // head == LAMBDA
        let (args, body) = (arg1.clone(), more.clone());
        let args_is_nil = args.alloc_equal(&mut cs.namespace(|| "args_is_nil"), &g.nil_ptr)?;

        let arg = AllocatedPtr::pick(
            &mut cs.namespace(|| "maybe dummy arg"),
            &args_is_nil,
            &g.dummy_arg_ptr,
            &car_args,
        )?;

        let inner = AllocatedPtr::construct_cons(
            &mut cs.namespace(|| "inner"),
            g,
            store,
            &cdr_args,
            &body,
        )?;
        let l = AllocatedPtr::construct_cons(&mut cs.namespace(|| "l"), g, store, &lambda, &inner)?;
        let cdr_args_is_nil =
            cdr_args.alloc_equal(&mut cs.namespace(|| "cdr_args_is_nil"), &g.nil_ptr)?;

        let list = AllocatedPtr::construct_list(&mut cs.namespace(|| "list"), g, store, &[&l])?;
        let inner_body = AllocatedPtr::pick(
            &mut cs.namespace(|| "inner_body"),
            &cdr_args_is_nil,
            &body,
            &list,
        )?;

        AllocatedPtr::construct_fun(
            &mut cs.namespace(|| "function"),
            g,
            store,
            &arg,
            &inner_body,
            env,
        )?
    };

    results.add_clauses_cons(*lambda_hash.value(), &function, env, cont, &g.true_num);

    // head == QUOTE
    let (arg1_or_expr, the_cont) = {
        let arg1_or_expr = AllocatedPtr::pick(
            &mut cs.namespace(|| "arg1 if end is nil, expr otherwise"),
            &end_is_nil,
            &arg1,
            expr,
        )?;

        let the_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "the cont if end is nil"),
            &end_is_nil,
            cont,
            &g.error_ptr_cont,
        )?;

        (arg1_or_expr, the_cont)
    };

    results.add_clauses_cons(
        *quote_hash.value(),
        &arg1_or_expr,
        env,
        &the_cont,
        &g.true_num,
    );

    /*
     * Returns the expression, which can be the value of the first binding
     * when it is found, or the body otherwise. It also returns 2 continuations,
     * one for let and one for letrec. The continuation is `cont` if no error
     * is found and bindings is nil. Otherwise the continuation is a new
     * pointer, created using the expanded env.
     * Errors:
     *  - rest_body_is_nil
     *  - end_is_nil rest (and not bindings_is_nil)
     */
    let (the_expr, var_let_letrec, expanded_let, expanded_letrec, bindings_is_nil, cond_error) = {
        // head == LET
        // or head == LETREC

        let mut cs_let_letrec = cs.namespace(|| "LET_LETREC");

        let (bindings, body) = (arg1.clone(), more.clone());
        let (body1, rest_body) = car_cdr(
            &mut cs_let_letrec.namespace(|| "car_cdr body"),
            g,
            &body,
            store,
        )?;
        let (binding1, rest_bindings) = (car_args, cdr_args);
        let (var_let_letrec, vals) = car_cdr(
            &mut cs_let_letrec.namespace(|| "car_cdr binding1"),
            g,
            &binding1,
            store,
        )?;
        let bindings_is_nil = bindings.alloc_equal(
            &mut cs_let_letrec.namespace(|| "bindings_is_nil"),
            &g.nil_ptr,
        )?;

        let rest_body_is_nil = rest_body.alloc_equal(
            &mut cs_let_letrec.namespace(|| "rest_body_is_nil"),
            &g.nil_ptr,
        )?;

        let (val, end) = car_cdr(
            &mut cs_let_letrec.namespace(|| "car_cdr vals"),
            g,
            &vals,
            store,
        )?;

        let end_is_nil =
            end.alloc_equal(&mut cs_let_letrec.namespace(|| "end_is_nil"), &g.nil_ptr)?;

        let body_is_nil =
            body.alloc_equal(&mut cs_let_letrec.namespace(|| "body_is_nil"), &g.nil_ptr)?;

        /*
         * We get the condition for error by using OR of each individual error.
         */
        let mut cond_error = constraints::or(
            &mut cs_let_letrec.namespace(|| "cond error1"),
            &Boolean::not(&rest_body_is_nil),
            &Boolean::not(&end_is_nil),
        )?;
        cond_error = constraints::or(
            &mut cs_let_letrec.namespace(|| "cond error2"),
            &body_is_nil,
            &cond_error,
        )?;

        let expanded1 = AllocatedPtr::construct_list(
            &mut cs_let_letrec.namespace(|| "expanded1"),
            g,
            store,
            &[&let_t, &rest_bindings, &body1],
        )?;

        let rest_bindings_is_nil = rest_bindings.alloc_equal(
            &mut cs_let_letrec.namespace(|| "rest_bindings_is_nil"),
            &g.nil_ptr,
        )?;

        let expanded = AllocatedPtr::pick(
            &mut cs_let_letrec.namespace(|| "expanded"),
            &rest_bindings_is_nil,
            &body1,
            &expanded1,
        )?;

        let expanded2 = AllocatedPtr::construct_list(
            &mut cs_let_letrec.namespace(|| "expanded2"),
            g,
            store,
            &[&letrec_t, &rest_bindings, &body1],
        )?;

        let expanded_ = AllocatedPtr::pick(
            &mut cs_let_letrec.namespace(|| "expanded_"),
            &rest_bindings_is_nil,
            &body1,
            &expanded2,
        )?;

        let output_expr = AllocatedPtr::pick(
            &mut cs_let_letrec.namespace(|| "pick body1 or val"),
            &bindings_is_nil,
            &body1,
            &val,
        )?;

        let the_expr = AllocatedPtr::pick(
            &mut cs_let_letrec.namespace(|| "the_expr_let"),
            &cond_error,
            expr,
            &output_expr,
        )?;

        (
            the_expr,
            var_let_letrec,
            expanded,
            expanded_,
            bindings_is_nil,
            cond_error,
        )
    };

    // head == EVAL preimage
    /////////////////////////////////////////////////////////////////////////////
    let (
        the_op,
        op1_or_op2,
        env_or_cont_tag,
        env_or_cont_hash,
        default_or_expr_tag,
        default_or_expr_hash,
        default_or_cont_tag,
        default_or_cont_hash,
    ) = {
        let the_op = pick(
            &mut cs.namespace(|| "eval op"),
            &end_is_nil,
            &g.unop_cont_tag,
            &g.binop_cont_tag,
        )?;
        let op1_or_op2 = pick(
            &mut cs.namespace(|| "op1 or op2"),
            &end_is_nil,
            &g.op1_eval_tag,
            &g.op2_eval_tag,
        )?;
        let env_or_cont_tag = pick(
            &mut cs.namespace(|| "env or cont tag"),
            &end_is_nil,
            env.tag(),
            cont.tag(),
        )?;
        let env_or_cont_hash = pick(
            &mut cs.namespace(|| "env or cont hash"),
            &end_is_nil,
            env.hash(),
            cont.hash(),
        )?;
        let default_or_expr_tag = pick(
            &mut cs.namespace(|| "default or expr tag"),
            &end_is_nil,
            &g.default_num,
            more.tag(),
        )?;
        let default_or_expr_hash = pick(
            &mut cs.namespace(|| "default or expr hash"),
            &end_is_nil,
            &g.default_num,
            more.hash(),
        )?;
        let default_or_cont_tag = pick(
            &mut cs.namespace(|| "default or cont tag"),
            &end_is_nil,
            &g.default_num,
            cont.tag(),
        )?;
        let default_or_cont_hash = pick(
            &mut cs.namespace(|| "default or cont hash"),
            &end_is_nil,
            &g.default_num,
            cont.hash(),
        )?;
        (
            the_op,
            op1_or_op2,
            env_or_cont_tag,
            env_or_cont_hash,
            default_or_expr_tag,
            default_or_expr_hash,
            default_or_cont_tag,
            default_or_cont_hash,
        )
    };

    let eval_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &[&op1_or_op2, &g.default_num],
        &[&env_or_cont_tag, &env_or_cont_hash],
        &[&default_or_expr_tag, &default_or_expr_hash],
        &[&default_or_cont_tag, &default_or_cont_hash],
    ];
    hash_default_results.add_hash_input_clauses(
        *eval_hash.value(),
        &the_op,
        eval_continuation_components,
    );

    // head == LET and LETREC preimage
    /////////////////////////////////////////////////////////////////////////////
    let let_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&var_let_letrec, &expanded_let, env, cont];
    hash_default_results.add_hash_input_clauses(
        *let_sym.value(),
        &g.let_cont_tag,
        let_continuation_components,
    );
    let letrec_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&var_let_letrec, &expanded_letrec, env, cont];
    hash_default_results.add_hash_input_clauses(
        *letrec.value(),
        &g.letrec_cont_tag,
        letrec_continuation_components,
    );

    // head == CONS preimage
    /////////////////////////////////////////////////////////////////////////////
    let cons_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_cons_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        *cons_hash.value(),
        &g.binop_cont_tag,
        cons_continuation_components,
    );

    // head == STRCONS preimage
    /////////////////////////////////////////////////////////////////////////////
    let strcons_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_strcons_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        *strcons_hash.value(),
        &g.binop_cont_tag,
        strcons_continuation_components,
    );

    // head == HIDE preimage
    /////////////////////////////////////////////////////////////////////////////
    let hide_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_hide_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        *hide_hash.value(),
        &g.binop_cont_tag,
        hide_continuation_components,
    );

    // head == COMMIT preimage
    /////////////////////////////////////////////////////////////////////////////
    let commit_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &[&g.op1_commit_tag, &g.default_num],
        &[cont.tag(), cont.hash()],
        &[&g.default_num, &g.default_num],
        &[&g.default_num, &g.default_num],
    ];
    hash_default_results.add_hash_input_clauses(
        *commit_hash.value(),
        &g.unop_cont_tag,
        commit_continuation_components,
    );

    // head == OPEN preimage
    /////////////////////////////////////////////////////////////////////////////
    let open_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &[&g.op1_open_tag, &g.default_num],
        &[cont.tag(), cont.hash()],
        &[&g.default_num, &g.default_num],
        &[&g.default_num, &g.default_num],
    ];
    hash_default_results.add_hash_input_clauses(
        *open_hash.value(),
        &g.unop_cont_tag,
        open_continuation_components,
    );

    // head == SECRET preimage
    /////////////////////////////////////////////////////////////////////////////
    let secret_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &[&g.op1_secret_tag, &g.default_num],
        &[cont.tag(), cont.hash()],
        &[&g.default_num, &g.default_num],
        &[&g.default_num, &g.default_num],
    ];
    hash_default_results.add_hash_input_clauses(
        *secret_hash.value(),
        &g.unop_cont_tag,
        secret_continuation_components,
    );

    // head == NUM preimage
    /////////////////////////////////////////////////////////////////////////////
    let num_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &[&g.op1_num_tag, &g.default_num],
        &[cont.tag(), cont.hash()],
        &[&g.default_num, &g.default_num],
        &[&g.default_num, &g.default_num],
    ];
    hash_default_results.add_hash_input_clauses(
        *num_hash.value(),
        &g.unop_cont_tag,
        num_continuation_components,
    );

    // head == COMM preimage
    /////////////////////////////////////////////////////////////////////////////
    let comm_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &[&g.op1_comm_tag, &g.default_num],
        &[cont.tag(), cont.hash()],
        &[&g.default_num, &g.default_num],
        &[&g.default_num, &g.default_num],
    ];
    hash_default_results.add_hash_input_clauses(
        *comm_hash.value(),
        &g.unop_cont_tag,
        comm_continuation_components,
    );

    // head == CHAR preimage
    /////////////////////////////////////////////////////////////////////////////
    let char_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &[&g.op1_char_tag, &g.default_num],
        &[cont.tag(), cont.hash()],
        &[&g.default_num, &g.default_num],
        &[&g.default_num, &g.default_num],
    ];
    hash_default_results.add_hash_input_clauses(
        *char_hash.value(),
        &g.unop_cont_tag,
        char_continuation_components,
    );

    // head == BEGIN preimage
    /////////////////////////////////////////////////////////////////////////////
    let begin_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_begin_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        *begin_hash.value(),
        &g.binop_cont_tag,
        begin_continuation_components,
    );

    // head == CAR preimage
    /////////////////////////////////////////////////////////////////////////////
    let car_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &[&g.op1_car_tag, &g.default_num],
        &[cont.tag(), cont.hash()],
        &[&g.default_num, &g.default_num],
        &[&g.default_num, &g.default_num],
    ];
    hash_default_results.add_hash_input_clauses(
        *car_hash.value(),
        &g.unop_cont_tag,
        car_continuation_components,
    );

    // head == CDR preimage
    /////////////////////////////////////////////////////////////////////////////
    let cdr_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &[&g.op1_cdr_tag, &g.default_num],
        &[cont.tag(), cont.hash()],
        &[&g.default_num, &g.default_num],
        &[&g.default_num, &g.default_num],
    ];
    hash_default_results.add_hash_input_clauses(
        *cdr_hash.value(),
        &g.unop_cont_tag,
        cdr_continuation_components,
    );

    // head == ATOM preimage
    /////////////////////////////////////////////////////////////////////////////
    let atom_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &[&g.op1_atom_tag, &g.default_num],
        &[cont.tag(), cont.hash()],
        &[&g.default_num, &g.default_num],
        &[&g.default_num, &g.default_num],
    ];
    hash_default_results.add_hash_input_clauses(
        *atom_hash.value(),
        &g.unop_cont_tag,
        atom_continuation_components,
    );

    // head == EMIT preimage
    /////////////////////////////////////////////////////////////////////////////
    let emit_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &[&g.op1_emit_tag, &g.default_num],
        &[cont.tag(), cont.hash()],
        &[&g.default_num, &g.default_num],
        &[&g.default_num, &g.default_num],
    ];
    hash_default_results.add_hash_input_clauses(
        *emit_hash.value(),
        &g.unop_cont_tag,
        emit_continuation_components,
    );

    // head == + preimage
    /////////////////////////////////////////////////////////////////////////////
    let sum_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_sum_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        *sum_hash.value(),
        &g.binop_cont_tag,
        sum_continuation_components,
    );

    // head == - preimage
    /////////////////////////////////////////////////////////////////////////////
    let diff_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_diff_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        *diff_hash.value(),
        &g.binop_cont_tag,
        diff_continuation_components,
    );

    // head == * preimage
    /////////////////////////////////////////////////////////////////////////////
    let product_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_product_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        *product_hash.value(),
        &g.binop_cont_tag,
        product_continuation_components,
    );

    // head == / preimage
    /////////////////////////////////////////////////////////////////////////////

    let quotient_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_quotient_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        *quotient_hash.value(),
        &g.binop_cont_tag,
        quotient_continuation_components,
    );

    // head == = preimage
    /////////////////////////////////////////////////////////////////////////////

    let numequal_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_numequal_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        *numequal_hash.value(),
        &g.binop_cont_tag,
        numequal_continuation_components,
    );

    // head == EQ preimage
    /////////////////////////////////////////////////////////////////////////////
    let equal_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_equal_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        *equal_hash.value(),
        &g.binop_cont_tag,
        equal_continuation_components,
    );

    // head == < preimage
    /////////////////////////////////////////////////////////////////////////////
    let less_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_less_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        *less_hash.value(),
        &g.binop_cont_tag,
        less_continuation_components,
    );

    // head == <= preimage
    /////////////////////////////////////////////////////////////////////////////
    let less_equal_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_less_equal_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        *less_equal_hash.value(),
        &g.binop_cont_tag,
        less_equal_continuation_components,
    );

    // head == > preimage
    /////////////////////////////////////////////////////////////////////////////
    let greater_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_greater_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        *greater_hash.value(),
        &g.binop_cont_tag,
        greater_continuation_components,
    );

    // head == >= preimage
    /////////////////////////////////////////////////////////////////////////////
    let greater_equal_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &[&g.op2_greater_equal_tag, &g.default_num],
        env,
        &more,
        cont,
    ];
    hash_default_results.add_hash_input_clauses(
        *greater_equal_hash.value(),
        &g.binop_cont_tag,
        greater_equal_continuation_components,
    );

    // head == IF preimage
    /////////////////////////////////////////////////////////////////////////////
    let if_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &more.clone(),
        cont,
        &[&g.default_num, &g.default_num],
        &[&g.default_num, &g.default_num],
    ];
    hash_default_results.add_hash_input_clauses(
        *if_hash.value(),
        &g.if_cont_tag,
        if_continuation_components,
    );

    // head == CURRENT-ENV
    let the_cont_if_rest_is_nil = AllocatedContPtr::pick(
        &mut cs.namespace(|| "the_cont_if_rest_is_nil"),
        &rest_is_nil,
        cont,
        &g.error_ptr_cont,
    )?;
    results.add_clauses_cons(
        *current_env_hash.value(),
        env,
        env,
        &the_cont_if_rest_is_nil,
        &g.true_num,
    );

    // head == fn . args preimage
    /////////////////////////////////////////////////////////////////////////////
    let (
        cont_tag,
        component0_tag,
        component0_hash,
        component1_tag,
        component1_hash,
        component2_tag,
        component2_hash,
    ) = {
        let cont_tag = pick(
            &mut cs.namespace(|| "pick cont_tag"),
            &rest_is_nil,
            &g.call0_cont_tag,
            &g.call_cont_tag,
        )?;
        let component1_tag = pick(
            &mut cs.namespace(|| "pick component1_tag"),
            &rest_is_nil,
            cont.tag(),
            arg1.tag(),
        )?;
        let component1_hash = pick(
            &mut cs.namespace(|| "pick component1_hash"),
            &rest_is_nil,
            cont.hash(),
            arg1.hash(),
        )?;
        let component2_tag = pick(
            &mut cs.namespace(|| "pick component2_tag"),
            &rest_is_nil,
            &g.default_num,
            cont.tag(),
        )?;
        let component2_hash = pick(
            &mut cs.namespace(|| "pick component2_hash"),
            &rest_is_nil,
            &g.default_num,
            cont.hash(),
        )?;

        (
            cont_tag,
            env.tag(),
            env.hash(),
            component1_tag,
            component1_hash,
            component2_tag,
            component2_hash,
        )
    };

    // default has the `fn args` preimage
    let defaults = [
        &cont_tag,
        component0_tag,
        component0_hash,
        &component1_tag,
        &component1_hash,
        &component2_tag,
        &component2_hash,
        &g.default_num,
        &g.default_num,
    ];

    /////////////////////////// multicase (hash preimage)
    let all_hash_input_clauses = [
        &hash_default_results.tag_clauses[..],
        &hash_default_results.components_clauses[0][..],
        &hash_default_results.components_clauses[1][..],
        &hash_default_results.components_clauses[2][..],
        &hash_default_results.components_clauses[3][..],
        &hash_default_results.components_clauses[4][..],
        &hash_default_results.components_clauses[5][..],
        &hash_default_results.components_clauses[6][..],
        &hash_default_results.components_clauses[7][..],
    ];

    let components_results = multi_case(
        &mut cs.namespace(|| "reduce cons hash preimage selection"),
        head.hash(),
        &all_hash_input_clauses,
        &defaults,
        g,
    )?;

    // construct newer continuation from multicase results
    let newer_cont = AllocatedContPtr::construct(
        &mut cs.namespace(|| "reduce cons newer_cont construction from hash components"),
        store,
        &components_results[0], // continuation tag
        &[
            &[&components_results[1], &components_results[2]] as &dyn AsAllocatedHashComponents<F>,
            &[&components_results[3], &components_results[4]] as &dyn AsAllocatedHashComponents<F>,
            &[&components_results[5], &components_results[6]] as &dyn AsAllocatedHashComponents<F>,
            &[&components_results[7], &components_results[8]] as &dyn AsAllocatedHashComponents<F>,
        ],
    )?;

    // head == LET and LETREC, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    let the_cont_letrec = {
        let output_cont_letrec = AllocatedContPtr::pick(
            &mut cs.namespace(|| "pick cont or newer let"),
            &bindings_is_nil,
            cont,
            &newer_cont,
        )?;

        let the_cont_let_letrec = AllocatedContPtr::pick(
            &mut cs.namespace(|| "the_cont_let_letrec"),
            &cond_error,
            &g.error_ptr_cont,
            &output_cont_letrec,
        )?;
        the_cont_let_letrec
    };
    results.add_clauses_cons(*let_hash, &the_expr, env, &the_cont_letrec, &g.false_num);
    results.add_clauses_cons(*letrec_hash, &the_expr, env, &the_cont_letrec, &g.false_num);

    // head == CONS, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    // Checking one-arg cons or strcons error
    let the_cont_cons_or_strcons = AllocatedContPtr::pick(
        &mut cs.namespace(|| "the_cont_cons_or_strcons"),
        &end_is_nil,
        &g.error_ptr_cont,
        &newer_cont,
    )?;
    results.add_clauses_cons(
        *cons_hash.value(),
        &arg1,
        env,
        &the_cont_cons_or_strcons,
        &g.false_num,
    );

    // head == STRCONS, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        *strcons_hash.value(),
        &arg1,
        env,
        &the_cont_cons_or_strcons,
        &g.false_num,
    );

    // head == BEGIN, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    let cont_begin = AllocatedContPtr::pick(
        &mut cs.namespace(|| "cont begin"),
        &end_is_nil,
        cont,
        &newer_cont,
    )?;
    results.add_clauses_cons(*begin_hash.value(), &arg1, env, &cont_begin, &g.false_num);

    // head == CAR, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    let newer_cont_if_end_is_nil = AllocatedContPtr::pick(
        &mut cs.namespace(|| "newer_cont_if_end_is_nil"),
        &end_is_nil,
        &newer_cont,
        &g.error_ptr_cont,
    )?;

    results.add_clauses_cons(
        *car_hash.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == CDR, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        *cdr_hash.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == HIDE, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    let the_cont_hide = AllocatedContPtr::pick(
        &mut cs.namespace(|| "the_cont_hide"),
        &end_is_nil,
        &g.error_ptr_cont,
        &newer_cont,
    )?;
    results.add_clauses_cons(*hide_hash.value(), &arg1, env, &the_cont_hide, &g.false_num);

    // head == COMMIT, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        *commit_hash.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == OPEN, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////

    let arg1_tag_is_num = alloc_equal(&mut cs.namespace(|| "tag_is_num"), arg1.tag(), &g.num_tag)?;

    let arg1_tag_is_comm =
        alloc_equal(&mut cs.namespace(|| "tag_is_comm"), arg1.tag(), &g.comm_tag)?;

    let arg1_tag_is_num_or_comm = constraints::or(
        &mut cs.namespace(|| "tag_is_num_or_comm"),
        &arg1_tag_is_num,
        &arg1_tag_is_comm,
    )?;

    let the_cont_open_or_secret = AllocatedContPtr::pick(
        &mut cs.namespace(|| "the_cont_open"),
        &arg1_tag_is_num_or_comm,
        &newer_cont_if_end_is_nil,
        &g.error_ptr_cont,
    )?;

    results.add_clauses_cons(
        *open_hash.value(),
        &arg1_or_expr,
        env,
        &the_cont_open_or_secret,
        &g.false_num,
    );

    // head == SECRET, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////

    results.add_clauses_cons(
        *secret_hash.value(),
        &arg1_or_expr,
        env,
        &the_cont_open_or_secret,
        &g.false_num,
    );

    // head == NUM, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        *num_hash.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == COMM, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        *comm_hash.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == CHAR, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        *char_hash.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == EVAL, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(*eval_hash.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == ATOM, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        *atom_hash.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == EMIT, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        *emit_hash.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == +, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(*sum_hash.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == -, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(*diff_hash.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == *, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(*product_hash.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == /, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        *quotient_hash.value(),
        &arg1,
        env,
        &newer_cont,
        &g.false_num,
    );

    // head == =, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        *numequal_hash.value(),
        &arg1,
        env,
        &newer_cont,
        &g.false_num,
    );

    // head == EQ, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(*equal_hash.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == <, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(*less_hash.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == <=, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        *less_equal_hash.value(),
        &arg1,
        env,
        &newer_cont,
        &g.false_num,
    );

    // head == >, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(*greater_hash.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == >=, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        *greater_equal_hash.value(),
        &arg1,
        env,
        &newer_cont,
        &g.false_num,
    );

    // head == IF, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(*if_hash.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == (FN . ARGS), newer_cont is allocated (deal with CALL and CALL0)
    /////////////////////////////////////////////////////////////////////////////
    let (res, continuation) = {
        let fun_form = &head;

        let expanded_inner = AllocatedPtr::construct_list(
            &mut cs.namespace(|| "expanded_inner"),
            g,
            store,
            &[fun_form, &arg1],
        )?;

        let expanded = AllocatedPtr::construct_cons(
            &mut cs.namespace(|| "expanded"),
            g,
            store,
            &expanded_inner,
            &more,
        )?;

        let arg1_is_nil = arg1.alloc_equal(&mut cs.namespace(|| "arg1_is_nil"), &g.nil_ptr)?;
        let more_args_is_nil =
            more.alloc_equal(&mut cs.namespace(|| "more_args_is_nil"), &g.nil_ptr)?;
        let args_is_nil_or_more_is_nil = constraints::or(
            &mut cs.namespace(|| "args is nil or more is nil"),
            &arg1_is_nil,
            &more_args_is_nil,
        )?;

        let res = AllocatedPtr::pick(
            &mut cs.namespace(|| "pick res"),
            &args_is_nil_or_more_is_nil,
            fun_form,
            &expanded,
        )?;

        let continuation = AllocatedContPtr::pick(
            &mut cs.namespace(|| "pick continuation"),
            &args_is_nil_or_more_is_nil,
            &newer_cont,
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
        &results.apply_continuation_clauses[..],
    ];

    let case_results = multi_case(
        &mut cs.namespace(|| "input expr hash case"),
        head.hash(),
        &all_clauses,
        &defaults,
        g,
    )?;

    let result_expr = AllocatedPtr::by_index(0, &case_results);
    let result_env = AllocatedPtr::by_index(1, &case_results);
    let result_cont = AllocatedContPtr::by_index(2, &case_results);
    let result_apply_cont: &AllocatedNum<F> = &case_results[6];

    Ok((
        result_expr,
        result_env,
        result_cont,
        result_apply_cont.clone(),
    ))
}

fn make_thunk<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    cont: &AllocatedContPtr<F>,
    result: &AllocatedPtr<F>,
    env: &AllocatedPtr<F>,
    not_dummy: &Boolean,
    _witness: &Option<Witness<F>>,
    store: &Store<F>,
    g: &GlobalAllocations<F>,
) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
    let mut results = Results::default();

    let (computed_cont_hash, cont_components) = ContPtr::allocate_maybe_dummy_components(
        &mut cs.namespace(|| "cont components"),
        cont.get_cont_ptr(store).as_ref(),
        store,
    )?;

    implies_equal!(cs, not_dummy, &computed_cont_hash, cont.hash());

    let (result_expr, saved_env) = {
        // Otherwise, these are the results.
        // Applies to Tail continuations only.
        let saved_env = AllocatedPtr::by_index(0, &cont_components);

        // Applies to Tail continuations
        let continuation = AllocatedContPtr::by_index(1, &cont_components);

        let result_expr = AllocatedPtr::construct_thunk(
            &mut cs.namespace(|| "tail thunk_hash"),
            g,
            store,
            result,
            &continuation,
        )?;

        (result_expr, saved_env)
    };

    results.add_clauses_thunk(ContTag::Tail, &result_expr, &saved_env, &g.dummy_ptr);
    results.add_clauses_thunk(ContTag::Outermost, result, env, &g.terminal_ptr);
    results.add_clauses_thunk(ContTag::Terminal, result, env, &g.terminal_ptr);
    results.add_clauses_thunk(ContTag::Error, result, env, &g.error_ptr_cont);

    let thunk_hash =
        Thunk::hash_components(&mut cs.namespace(|| "thunk_hash"), store, result, cont)?;
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
        g,
    )?;

    let result_expr = AllocatedPtr::by_index(0, &case_results);
    let result_env = AllocatedPtr::by_index(1, &case_results);
    let result_cont = AllocatedContPtr::by_index(2, &case_results);

    Ok((result_expr, result_env, result_cont))
}

fn apply_continuation<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    cont: &AllocatedContPtr<F>,
    result: &AllocatedPtr<F>,
    env: &AllocatedPtr<F>,
    not_dummy: &Boolean,
    witness: &Option<Witness<F>>,
    store: &Store<F>,
    g: &GlobalAllocations<F>,
) -> Result<
    (
        AllocatedPtr<F>,
        AllocatedPtr<F>,
        AllocatedContPtr<F>,
        AllocatedNum<F>,
    ),
    SynthesisError,
> {
    let mut hash_default_results = HashInputResults::default();
    let mut results = Results::default();

    results.add_clauses_cont(
        ContTag::Outermost,
        result,
        env,
        &g.terminal_ptr,
        &g.false_num,
    );
    results.add_clauses_cont(
        ContTag::Terminal,
        result,
        env,
        &g.terminal_ptr,
        &g.false_num,
    );
    results.add_clauses_cont(ContTag::Error, result, env, &g.error_ptr_cont, &g.false_num);

    let (_, continuation_components) = ContPtr::allocate_maybe_dummy_components(
        &mut cs.namespace(|| "allocate_continuation_components"),
        witness
            .as_ref()
            .and_then(|w| w.apply_continuation_cont.as_ref()),
        store,
    )?;

    let continuation = AllocatedContPtr::by_index(0, &continuation_components);

    results.add_clauses_cont(ContTag::Emit, result, env, &continuation, &g.true_num);

    let default_num_pair = &[&g.default_num, &g.default_num];

    let (commitment, commitment_secret, committed_expr) = {
        let operator = AllocatedPtr::by_index(0, &continuation_components);

        let is_op2_hide = constraints::alloc_equal(
            &mut cs.namespace(|| "operator tag == hide_tag"),
            operator.tag(),
            &g.op2_hide_tag,
        )?;

        let is_op1_open = constraints::alloc_equal(
            &mut cs.namespace(|| "operator tag == open_tag"),
            operator.tag(),
            &g.op1_open_tag,
        )?;

        let is_op1_secret = constraints::alloc_equal(
            &mut cs.namespace(|| "operator tag == secret_tag"),
            operator.tag(),
            &g.op1_secret_tag,
        )?;

        let is_op1_open_or_secret = constraints::or(
            &mut cs.namespace(|| "is_op1_open_or_secret"),
            &is_op1_open,
            &is_op1_secret,
        )?;

        // IF this is open, we need to know what we are opening.
        let digest = result.hash();

        let (open_secret_scalar, open_ptr) = match store
            .get_maybe_opaque(Tag::Comm, digest.get_value().unwrap_or_else(|| F::zero()))
        {
            Some(commit) => match store.open(commit) {
                Some((secret, opening)) => (secret, opening),
                None => (F::zero(), store.get_nil()), // nil is dummy
            },
            None => (F::zero(), store.get_nil()), // nil is dummy
        };

        let open_expr = AllocatedPtr::alloc(&mut cs.namespace(|| "open_expr"), || {
            Ok(store.hash_expr(&open_ptr).unwrap())
        })?;

        let open_secret = AllocatedNum::alloc(&mut cs.namespace(|| "open_secret"), || {
            Ok(open_secret_scalar)
        })?;

        let arg1 = AllocatedPtr::by_index(1, &continuation_components);

        let commit_secret = pick(
            &mut cs.namespace(|| "open secret"),
            &is_op2_hide,
            arg1.hash(),
            &g.default_num,
        )?;

        let secret = pick(
            &mut cs.namespace(|| "secret"),
            &is_op1_open_or_secret,
            &open_secret,
            &commit_secret,
        )?;

        let committed = AllocatedPtr::pick(
            &mut cs.namespace(|| "committed"),
            &is_op1_open,
            &open_expr,
            result,
        )?;
        (
            hide(&mut cs.namespace(|| "Hide"), g, &secret, &committed, store)?,
            secret,
            committed,
        )
    };

    // Next we add multicase clauses for each continuation that requires a newer
    // cont, which means it needs to constrain a new hash, which is expensive,
    // then we do it only once.
    /////////////////////////////////////////////////////////////////////////////

    // Continuation::Call0 preimage
    /////////////////////////////////////////////////////////////////////////////
    let (saved_env, continuation) = {
        (
            AllocatedPtr::by_index(0, &continuation_components),
            AllocatedContPtr::by_index(2, &continuation_components),
        )
    };
    let call0_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &saved_env,
        &continuation,
        default_num_pair,
        default_num_pair,
    ];
    hash_default_results.add_hash_input_clauses(
        ContTag::Call0.as_field(),
        &g.tail_cont_tag,
        call0_components,
    );

    // Continuation::Call preimage
    /////////////////////////////////////////////////////////////////////////////
    let (saved_env, continuation, function) = {
        (
            AllocatedPtr::by_index(0, &continuation_components),
            AllocatedContPtr::by_index(2, &continuation_components),
            result,
        )
    };
    let call_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&saved_env, function, &continuation, default_num_pair];
    hash_default_results.add_hash_input_clauses(
        ContTag::Call.as_field(),
        &g.call2_cont_tag,
        call_components,
    );

    // Continuation::Call2 preimage
    /////////////////////////////////////////////////////////////////////////////
    let (saved_env, continuation) = {
        (
            AllocatedPtr::by_index(0, &continuation_components),
            AllocatedContPtr::by_index(2, &continuation_components),
        )
    };
    let call2_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &saved_env,
        &continuation,
        default_num_pair,
        default_num_pair,
    ];
    hash_default_results.add_hash_input_clauses(
        ContTag::Call2.as_field(),
        &g.tail_cont_tag,
        call2_components,
    );

    // Continuation::Let preimage
    /////////////////////////////////////////////////////////////////////////////
    let (saved_env, let_cont) = {
        (
            AllocatedPtr::by_index(2, &continuation_components),
            AllocatedContPtr::by_index(3, &continuation_components),
        )
    };
    let let_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&saved_env, &let_cont, default_num_pair, default_num_pair];
    hash_default_results.add_hash_input_clauses(
        ContTag::Let.as_field(),
        &g.tail_cont_tag,
        let_components,
    );

    // Continuation::LetRec preimage
    /////////////////////////////////////////////////////////////////////////////
    let (saved_env, letrec_cont) = {
        (
            AllocatedPtr::by_index(2, &continuation_components),
            AllocatedContPtr::by_index(3, &continuation_components),
        )
    };
    let letrec_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&saved_env, &letrec_cont, default_num_pair, default_num_pair];
    hash_default_results.add_hash_input_clauses(
        ContTag::LetRec.as_field(),
        &g.tail_cont_tag,
        letrec_components,
    );

    // Continuation::Unop preimage
    /////////////////////////////////////////////////////////////////////////////
    let (unop_val, unop_continuation) = {
        let op1 = AllocatedPtr::by_index(0, &continuation_components);
        let unop_continuation = AllocatedContPtr::by_index(1, &continuation_components);

        let (allocated_car, allocated_cdr) =
            car_cdr(&mut cs.namespace(|| "Unop cons"), g, result, store)?;

        let result_is_cons = alloc_equal(
            &mut cs.namespace(|| "result_is_cons"),
            result.tag(),
            &g.cons_tag,
        )?;

        let atom_ptr = AllocatedPtr::pick(
            &mut cs.namespace(|| "atom val"),
            &result_is_cons,
            &g.nil_ptr,
            &g.t_ptr,
        )?;

        let num = num(&mut cs.namespace(|| "Unop num"), result, store)?;
        let comm = comm(&mut cs.namespace(|| "Unop comm"), result, store)?;
        let c = char_op(&mut cs.namespace(|| "Unop char"), result, store)?;

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
                    CaseClause {
                        key: Op1::Emit.as_field(),
                        value: result.tag(),
                    },
                    CaseClause {
                        key: Op1::Commit.as_field(),
                        value: commitment.tag(),
                    },
                    CaseClause {
                        key: Op1::Open.as_field(),
                        value: committed_expr.tag(),
                    },
                    CaseClause {
                        key: Op1::Secret.as_field(),
                        value: &g.num_tag,
                    },
                    CaseClause {
                        key: Op1::Num.as_field(),
                        value: num.tag(),
                    },
                    CaseClause {
                        key: Op1::Comm.as_field(),
                        value: comm.tag(),
                    },
                    CaseClause {
                        key: Op1::Char.as_field(),
                        value: c.tag(),
                    },
                    CaseClause {
                        key: Op1::Eval.as_field(),
                        value: result.tag(),
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
                    CaseClause {
                        key: Op1::Emit.as_field(),
                        value: result.hash(),
                    },
                    CaseClause {
                        key: Op1::Commit.as_field(),
                        value: commitment.hash(),
                    },
                    CaseClause {
                        key: Op1::Open.as_field(),
                        value: committed_expr.hash(),
                    },
                    CaseClause {
                        key: Op1::Secret.as_field(),
                        value: &commitment_secret,
                    },
                    CaseClause {
                        key: Op1::Num.as_field(),
                        value: num.hash(),
                    },
                    CaseClause {
                        key: Op1::Comm.as_field(),
                        value: comm.hash(),
                    },
                    CaseClause {
                        key: Op1::Char.as_field(),
                        value: c.hash(),
                    },
                    CaseClause {
                        key: Op1::Eval.as_field(),
                        value: result.hash(),
                    },
                ],
            ],
            &[&g.default_num, &g.default_num],
            g,
        )?;

        (AllocatedPtr::by_index(0, &res), unop_continuation)
    };

    let emit_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &unop_continuation,
        default_num_pair,
        default_num_pair,
        default_num_pair,
    ];
    hash_default_results.add_hash_input_clauses(
        ContTag::Unop.as_field(),
        &g.emit_cont_tag,
        emit_components,
    );

    // Continuation::Binop preimage
    /////////////////////////////////////////////////////////////////////////////
    let (op2, continuation) = {
        (
            &continuation_components[0],
            AllocatedContPtr::by_index(3, &continuation_components),
        )
    };
    let binop_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &[op2, &g.default_num],
        result,
        &continuation,
        default_num_pair,
    ];
    hash_default_results.add_hash_input_clauses(
        ContTag::Binop.as_field(),
        &g.binop2_cont_tag,
        binop_components,
    );

    let preimage_defaults = [
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.false_num,
    ];

    /////////////////////////// multicase (hash preimage)
    let all_hash_input_clauses = [
        &hash_default_results.tag_clauses[..],
        &hash_default_results.components_clauses[0][..],
        &hash_default_results.components_clauses[1][..],
        &hash_default_results.components_clauses[2][..],
        &hash_default_results.components_clauses[3][..],
        &hash_default_results.components_clauses[4][..],
        &hash_default_results.components_clauses[5][..],
        &hash_default_results.components_clauses[6][..],
        &hash_default_results.components_clauses[7][..],
    ];

    let components_results = multi_case(
        &mut cs.namespace(|| "hash preimage selection"),
        cont.tag(),
        &all_hash_input_clauses,
        &preimage_defaults,
        g,
    )?;

    // construct newer continuation from multicase results
    let newer_cont = AllocatedContPtr::construct(
        &mut cs.namespace(|| "construct newer_cont from hash components"),
        store,
        &components_results[0], // continuation tag
        &[
            &[&components_results[1], &components_results[2]] as &dyn AsAllocatedHashComponents<F>,
            &[&components_results[3], &components_results[4]] as &dyn AsAllocatedHashComponents<F>,
            &[&components_results[5], &components_results[6]] as &dyn AsAllocatedHashComponents<F>,
            &[&g.default_num, &g.default_num],
        ],
    )?;

    // Continuation::Call0
    /////////////////////////////////////////////////////////////////////////////
    let (the_expr, the_env, the_cont) = {
        let mut cs = cs.namespace(|| "Call0");
        let continuation = AllocatedContPtr::by_index(1, &continuation_components);
        let (_, arg_t, body_t, closed_env) = Ptr::allocate_maybe_fun(
            &mut cs.namespace(|| "allocate fun"),
            store,
            result.ptr(store).as_ref(),
        )?;

        let (body_form, _) = car_cdr(&mut cs.namespace(|| "body_form"), g, &body_t, store)?;

        let args_is_dummy =
            arg_t.alloc_equal(&mut cs.namespace(|| "args_is_dummy"), &g.dummy_arg_ptr)?;

        let result_is_fun =
            alloc_equal(cs.namespace(|| "result_is_fun"), function.tag(), &g.fun_tag)?;

        let continuation_is_tail = alloc_equal(
            &mut cs.namespace(|| "continuation is tail"),
            continuation.tag(),
            &g.tail_cont_tag,
        )?;

        let tail_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "the tail continuation"),
            &continuation_is_tail,
            &continuation,
            &newer_cont,
        );

        let next_expr = AllocatedPtr::pick(
            &mut cs.namespace(|| "pick next expr"),
            &args_is_dummy,
            &body_form,
            result,
        )?;
        let next_env = AllocatedPtr::pick(
            &mut cs.namespace(|| "pick next env"),
            &args_is_dummy,
            &closed_env,
            env,
        )?;
        let next_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "pick next cont"),
            &args_is_dummy,
            &tail_cont.unwrap(),
            &continuation,
        )?;

        let the_expr = AllocatedPtr::pick(
            &mut cs.namespace(|| "the_expr"),
            &result_is_fun,
            &next_expr,
            result,
        )?;
        let the_env = AllocatedPtr::pick(
            &mut cs.namespace(|| "the_env"),
            &result_is_fun,
            &next_env,
            env,
        )?;
        let the_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "the_cont"),
            &result_is_fun,
            &next_cont,
            &g.error_ptr_cont,
        )?;

        (the_expr, the_env, the_cont)
    };
    results.add_clauses_cont(ContTag::Call0, &the_expr, &the_env, &the_cont, &g.false_num);

    // Continuation::Call, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    let (next_expr, the_cont) = {
        let mut cs = cs.namespace(|| "Call");
        let next_expr = AllocatedPtr::by_index(1, &continuation_components);
        let result_is_fun =
            alloc_equal(cs.namespace(|| "result_is_fun"), result.tag(), &g.fun_tag)?;

        let next_expr = AllocatedPtr::pick(
            &mut cs.namespace(|| "next_expr"),
            &result_is_fun,
            &next_expr,
            result,
        )?;

        let the_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "the_cont"),
            &result_is_fun,
            &newer_cont,
            &g.error_ptr_cont,
        )?;
        (next_expr, the_cont)
    };
    results.add_clauses_cont(ContTag::Call, &next_expr, env, &the_cont, &g.false_num);

    // Continuation::Call2, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    let (the_expr, the_env, the_cont) = {
        let mut cs = cs.namespace(|| "Call2");
        let fun = AllocatedPtr::by_index(1, &continuation_components);
        let continuation = AllocatedContPtr::by_index(2, &continuation_components);

        {
            let (hash, arg_t, body_t, closed_env) = Ptr::allocate_maybe_fun(
                &mut cs.namespace(|| "allocate fun"),
                store,
                fun.ptr(store).as_ref(),
            )?;

            let (body_form, _) = car_cdr(&mut cs.namespace(|| "body_form"), g, &body_t, store)?;

            let fun_is_correct = constraints::alloc_equal(
                &mut cs.namespace(|| "fun hash is correct"),
                fun.hash(),
                &hash,
            )?;

            let cont_is_call2_precomp = constraints::alloc_equal(
                &mut cs.namespace(|| "branch taken"),
                cont.tag(),
                &g.call2_cont_tag,
            )?;

            let cont_is_call2_and_not_dummy = and!(cs, &cont_is_call2_precomp, not_dummy)?;

            enforce_implication(
                &mut cs.namespace(|| "implies non-dummy fun"),
                &cont_is_call2_and_not_dummy,
                &fun_is_correct,
            )?;

            let newer_env = extend(
                &mut cs.namespace(|| "extend env"),
                g,
                store,
                &closed_env,
                &arg_t,
                result,
            )?;

            let continuation_is_tail = alloc_equal(
                &mut cs.namespace(|| "continuation is tail"),
                continuation.tag(),
                &g.tail_cont_tag,
            )?;

            let tail_cont = AllocatedContPtr::pick(
                &mut cs.namespace(|| "the tail continuation"),
                &continuation_is_tail,
                &continuation,
                &newer_cont,
            );

            let result_is_fun =
                alloc_equal(cs.namespace(|| "result_is_fun"), result.tag(), &g.fun_tag)?;
            let args_is_dummy =
                arg_t.alloc_equal(&mut cs.namespace(|| "args_is_dummy"), &g.dummy_arg_ptr)?;
            let cond = or!(cs, &args_is_dummy.not(), &result_is_fun)?;

            let the_cont = AllocatedContPtr::pick(
                &mut cs.namespace(|| "the_cont"),
                &cond,
                &tail_cont.unwrap(),
                &g.error_ptr_cont,
            )?;

            let the_env =
                AllocatedPtr::pick(&mut cs.namespace(|| "the_env"), &cond, &newer_env, env)?;

            let the_expr =
                AllocatedPtr::pick(&mut cs.namespace(|| "the_expr"), &cond, &body_form, result)?;

            (the_expr, the_env, the_cont)
        }
    };
    results.add_clauses_cont(ContTag::Call2, &the_expr, &the_env, &the_cont, &g.false_num);

    // Continuation::Binop, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    let (the_expr, the_env, the_cont) = {
        let mut cs = cs.namespace(|| "Binop");
        let operator = AllocatedPtr::by_index(0, &continuation_components);
        let saved_env = AllocatedPtr::by_index(1, &continuation_components);
        let unevaled_args = AllocatedPtr::by_index(2, &continuation_components);

        let (allocated_arg2, allocated_rest) = car_cdr(
            &mut cs.namespace(|| "cons using newer continuation"),
            g,
            &unevaled_args,
            store,
        )?;

        let op_is_begin = alloc_equal(
            cs.namespace(|| "op_is_begin"),
            operator.tag(),
            &g.op2_begin_tag,
        )?;

        let rest_is_nil =
            allocated_rest.alloc_equal(&mut cs.namespace(|| "rest_is_nil"), &g.nil_ptr)?;

        let begin = store.get_begin();

        let allocated_begin =
            AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "begin"), store, || Ok(&begin))?;

        let begin_again = AllocatedPtr::construct_cons(
            &mut cs.namespace(|| "begin again"),
            g,
            store,
            &allocated_begin,
            &unevaled_args,
        )?;

        let the_expr_if_begin = AllocatedPtr::pick(
            &mut cs.namespace(|| "the_exp_if_begin"),
            &op_is_begin,
            &begin_again,
            result,
        )?;

        let otherwise = Boolean::not(&op_is_begin);

        let otherwise_and_rest_is_nil = Boolean::and(
            &mut cs.namespace(|| "otherwise_and_rest_is_nil"),
            &otherwise,
            &rest_is_nil,
        )?;

        let the_expr = AllocatedPtr::pick(
            &mut cs.namespace(|| "the_expr"),
            &rest_is_nil,
            &allocated_arg2,
            &the_expr_if_begin,
        )?;

        let the_env = AllocatedPtr::pick(
            &mut cs.namespace(|| "the_env"),
            &rest_is_nil,
            &saved_env,
            env,
        )?;

        let the_cont_otherwise = AllocatedContPtr::pick(
            &mut cs.namespace(|| "the_cont_otherwise"),
            &otherwise_and_rest_is_nil,
            &newer_cont,
            &g.error_ptr_cont,
        )?;

        let the_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "the_cont"),
            &otherwise,
            &the_cont_otherwise,
            &continuation,
        )?;

        (the_expr, the_env, the_cont)
    };
    results.add_clauses_cont(ContTag::Binop, &the_expr, &the_env, &the_cont, &g.false_num);

    // Continuation::Binop2
    /////////////////////////////////////////////////////////////////////////////
    let (the_expr, the_env, the_cont, make_thunk_num) = {
        let op2 = AllocatedPtr::by_index(0, &continuation_components);
        let arg1 = AllocatedPtr::by_index(1, &continuation_components);
        let continuation = AllocatedContPtr::by_index(2, &continuation_components);

        let arg2 = result;

        let arg1_is_num = alloc_equal(&mut cs.namespace(|| "arg1_is_num"), arg1.tag(), &g.num_tag)?;
        let arg2_is_num = alloc_equal(&mut cs.namespace(|| "arg2_is_num"), arg2.tag(), &g.num_tag)?;
        let both_args_are_nums = Boolean::and(
            &mut cs.namespace(|| "both_args_are_nums"),
            &arg1_is_num,
            &arg2_is_num,
        )?;

        let (a, b) = (arg1.hash(), arg2.hash()); // For Nums, the 'hash' is an immediate value.

        let tags_equal = alloc_equal(&mut cs.namespace(|| "tags equal"), arg1.tag(), arg2.tag())?;
        let vals_equal = alloc_equal(&mut cs.namespace(|| "vals equal"), arg1.hash(), arg2.hash())?;
        let args_equal =
            Boolean::and(&mut cs.namespace(|| "args equal"), &tags_equal, &vals_equal)?;

        let args_equal_ptr = AllocatedPtr::pick(
            &mut cs.namespace(|| "args_equal_ptr"),
            &args_equal,
            &g.t_ptr,
            &g.nil_ptr,
        )?;

        let not_dummy = alloc_equal(
            &mut cs.namespace(|| "Binop2 not dummy"),
            cont.tag(),
            &g.binop2_cont_tag,
        )?;

        let sum = constraints::add(&mut cs.namespace(|| "sum"), a, b)?;
        let diff = constraints::sub(&mut cs.namespace(|| "difference"), a, b)?;
        let product = constraints::mul(&mut cs.namespace(|| "product"), a, b)?;

        let op2_is_div = alloc_equal(
            cs.namespace(|| "op2_is_div"),
            op2.tag(),
            &g.op2_quotient_tag,
        )?;

        let b_is_zero = &alloc_is_zero(&mut cs.namespace(|| "b_is_zero"), b)?;

        let divisor = pick(
            &mut cs.namespace(|| "maybe-dummy divisor"),
            b_is_zero,
            &g.true_num,
            b,
        )?;

        let quotient = constraints::div(&mut cs.namespace(|| "quotient"), a, &divisor)?;

        let cons =
            AllocatedPtr::construct_cons(&mut cs.namespace(|| "cons"), g, store, &arg1, arg2)?;

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
                    key: Op2::Equal.as_field(),
                    value: args_equal_ptr.hash(),
                },
                CaseClause {
                    key: Op2::NumEqual.as_field(),
                    value: args_equal_ptr.hash(),
                },
                CaseClause {
                    key: Op2::Cons.as_field(),
                    value: cons.hash(),
                },
                CaseClause {
                    key: Op2::StrCons.as_field(),
                    value: cons.hash(),
                },
                CaseClause {
                    key: Op2::Hide.as_field(),
                    value: commitment.hash(),
                },
            ],
            &g.default_num,
            g,
        )?;

        let is_equal = alloc_equal(
            &mut cs.namespace(|| "Op2 is Equal"),
            op2.tag(),
            &g.op2_equal_tag,
        )?;

        let is_num_equal = alloc_equal(
            &mut cs.namespace(|| "Op2 is NumEqual"),
            op2.tag(),
            &g.op2_numequal_tag,
        )?;

        let is_equal_or_num_equal = constraints::or(
            &mut cs.namespace(|| "is_equal_or_num_equal"),
            &is_equal,
            &is_num_equal,
        )?;

        let is_cons = alloc_equal(
            &mut cs.namespace(|| "Op2 is Cons"),
            op2.tag(),
            &g.op2_cons_tag,
        )?;

        let is_strcons = alloc_equal(
            &mut cs.namespace(|| "Op2 is StrCons"),
            op2.tag(),
            &g.op2_strcons_tag,
        )?;

        let is_hide = alloc_equal(
            &mut cs.namespace(|| "Op2 is Hide"),
            op2.tag(),
            &g.op2_hide_tag,
        )?;

        let commitment_tag_is_comm = alloc_equal(
            &mut cs.namespace(|| "commitment tag is comm"),
            commitment.tag(),
            &g.comm_tag,
        )?;

        let commitment_tag_is_dummy = alloc_is_zero(
            &mut cs.namespace(|| "commitment tag is dummy"),
            commitment.tag(),
        )?;

        let commitment_tag_is_correct = constraints::or(
            &mut cs.namespace(|| "commitment tag is correct"),
            &commitment_tag_is_comm,
            &commitment_tag_is_dummy,
        )?;

        enforce_implication(
            &mut cs.namespace(|| "is hide implies commitment tag is correct"),
            &is_hide,
            &commitment_tag_is_correct,
        )?;

        let arg1_is_char = alloc_equal(
            &mut cs.namespace(|| "arg1_is_char"),
            arg1.tag(),
            &g.char_tag,
        )?;
        let arg2_is_str = alloc_equal(&mut cs.namespace(|| "arg2_is_str"), arg2.tag(), &g.str_tag)?;
        let args_are_char_str = Boolean::and(
            &mut cs.namespace(|| "args_are_char_str"),
            &arg1_is_char,
            &arg2_is_str,
        )?;

        let cons_tag = pick(
            &mut cs.namespace(|| "cons_tag"),
            &is_strcons,
            &g.str_tag,
            &g.cons_tag,
        )?;

        let comm_or_num_tag = pick(
            &mut cs.namespace(|| "Op2 tag is comm or num"),
            &is_hide,
            &g.comm_tag,
            &g.num_tag,
        )?;

        let is_cons_or_hide =
            constraints::or(&mut cs.namespace(|| "is cons or hide"), &is_cons, &is_hide)?;

        let is_cons_or_strcons = constraints::or(
            &mut cs.namespace(|| "is cons or strcons"),
            &is_cons,
            &is_strcons,
        )?;

        let is_cons_or_strcons_or_hide = constraints::or(
            &mut cs.namespace(|| "is cons or srtcons or hide"),
            &is_cons_or_hide,
            &is_strcons,
        )?;

        let is_cons_or_strcons_or_hide_or_equal = constraints::or(
            &mut cs.namespace(|| "is cons or srtcons or hide or equal"),
            &is_cons_or_strcons_or_hide,
            &is_equal,
        )?;

        let is_cons_or_strcons_or_hide_or_equal_or_num_equal = constraints::or(
            &mut cs.namespace(|| "is cons or srtcons or hide or equal or num_equal"),
            &is_cons_or_strcons_or_hide_or_equal,
            &is_num_equal,
        )?;

        let res_tag0 = pick(
            &mut cs.namespace(|| "Op2 result tag0"),
            &is_cons_or_strcons,
            &cons_tag,
            &comm_or_num_tag,
        )?;

        let res_tag = pick(
            &mut cs.namespace(|| "Op2 result tag"),
            &is_equal_or_num_equal,
            args_equal_ptr.tag(),
            &res_tag0,
        )?;

        let res = AllocatedPtr::from_parts(&res_tag, &val);

        // Next constraints are used for number comparisons: <, <=, >, >=
        ///////////////////////////////////////////////////////////////////////
        let double_a = constraints::add(&mut cs.namespace(|| "double a"), a, a)?;
        // Ideally we would compute the bit decomposition for a, not for 2a,
        // since it would be possible to use it for future purposes.
        let double_a_bits = double_a
            .to_bits_le_strict(&mut cs.namespace(|| "double a lsb"))
            .unwrap();
        let lsb_2a = double_a_bits.get(0);

        let double_b = constraints::add(&mut cs.namespace(|| "double b"), b, b)?;
        let double_b_bits = double_b
            .to_bits_le_strict(&mut cs.namespace(|| "double b lsb"))
            .unwrap();
        let lsb_2b = double_b_bits.get(0);

        let diff_is_zero = alloc_is_zero(&mut cs.namespace(|| "diff is zero"), &diff)?;
        let double_diff = constraints::add(&mut cs.namespace(|| "double diff"), &diff, &diff)?;
        let double_diff_bits = double_diff.to_bits_le_strict(&mut cs).unwrap();
        let lsb_2diff = double_diff_bits.get(0);

        // We have that a number is defined to be negative if the parity bit (the
        // least significant bit) is odd after doubling, meaning that the field element
        // (after doubling) is larger than the underlying prime p that defines the
        // field, then a modular reduction must have been carried out, changing the parity that
        // should be even (since we multiplied by 2) to odd. In other words, we define
        // negative numbers to be those field elements that are larger than p/2.
        let a_is_negative = lsb_2a.unwrap();
        let b_is_negative = lsb_2b.unwrap();
        let diff_is_negative = lsb_2diff.unwrap();

        let diff_is_not_positive = constraints::or(
            &mut cs.namespace(|| "diff is not positive"),
            diff_is_negative,
            &diff_is_zero,
        )?;

        let diff_is_positive = Boolean::and(
            &mut cs.namespace(|| "diff is positive"),
            &diff_is_negative.not(),
            &diff_is_zero.not(),
        )?;

        let diff_is_not_negative = diff_is_negative.not();

        let both_same_sign = Boolean::xor(
            &mut cs.namespace(|| "both same sign"),
            a_is_negative,
            b_is_negative,
        )?
        .not();

        let a_negative_and_b_not_negative = Boolean::and(
            &mut cs.namespace(|| "a negative and b not negative"),
            a_is_negative,
            &b_is_negative.not(),
        )?;

        let alloc_num_diff_is_negative = boolean_to_num(
            &mut cs.namespace(|| "Allocate num for diff_is_negative"),
            diff_is_negative,
        )?;

        let alloc_num_diff_is_not_positive = boolean_to_num(
            &mut cs.namespace(|| "Allocate num for diff_is_not_positive"),
            &diff_is_not_positive,
        )?;

        let alloc_num_diff_is_positive = boolean_to_num(
            &mut cs.namespace(|| "Allocate num for diff_is_positive"),
            &diff_is_positive,
        )?;

        let alloc_num_diff_is_not_negative = boolean_to_num(
            &mut cs.namespace(|| "Allocate num for diff_is_not_negative"),
            &diff_is_not_negative,
        )?;

        let mut comp_results = CompResults::default();
        comp_results.add_clauses_comp(
            Op2::Less.as_field(),
            &alloc_num_diff_is_negative,
            &g.true_num,
            &g.false_num,
        );
        comp_results.add_clauses_comp(
            Op2::LessEqual.as_field(),
            &alloc_num_diff_is_not_positive,
            &g.true_num,
            &g.false_num,
        );
        comp_results.add_clauses_comp(
            Op2::Greater.as_field(),
            &alloc_num_diff_is_positive,
            &g.false_num,
            &g.true_num,
        );
        comp_results.add_clauses_comp(
            Op2::GreaterEqual.as_field(),
            &alloc_num_diff_is_not_negative,
            &g.false_num,
            &g.true_num,
        );

        let comparison_defaults = [&g.default_num, &g.default_num, &g.default_num];

        let comp_clauses = [
            &comp_results.same_sign[..],
            &comp_results.a_neg_and_b_not_neg[..],
            &comp_results.a_not_neg_and_b_neg[..],
        ];

        let comparison_result = multi_case_aux(
            &mut cs.namespace(|| "comparison multicase results"),
            op2.tag(),
            &comp_clauses,
            &comparison_defaults,
            g,
        )?;

        let comp_val_same_sign_num = comparison_result.0[0].clone();
        let comp_val_a_neg_and_b_not_neg_num = comparison_result.0[1].clone();
        let comp_val_a_not_neg_and_b_neg_num = comparison_result.0[2].clone();
        let is_comparison_tag = comparison_result.1.not();

        let comp_val1 = pick(
            &mut cs.namespace(|| "comp_val1"),
            &a_negative_and_b_not_negative,
            &comp_val_a_neg_and_b_not_neg_num,
            &comp_val_a_not_neg_and_b_neg_num,
        )?;
        let comp_val2 = pick(
            &mut cs.namespace(|| "comp_val2"),
            &both_same_sign,
            &comp_val_same_sign_num,
            &comp_val1,
        )?;

        let comp_val_is_zero = alloc_is_zero(&mut cs.namespace(|| "comp_val_is_zero"), &comp_val2)?;

        let comp_val = AllocatedPtr::pick(
            &mut cs.namespace(|| "comp_val"),
            &comp_val_is_zero,
            &g.nil_ptr,
            &g.t_ptr,
        )?;

        ///////////////////////////////////////////////////////////////////////

        let final_res = AllocatedPtr::pick(
            &mut cs.namespace(|| "final res"),
            &is_comparison_tag,
            &comp_val,
            &res,
        )?;

        let valid_types = constraints::or(
            &mut cs.namespace(|| "Op2 called with valid types"),
            &is_cons_or_strcons_or_hide_or_equal,
            &both_args_are_nums,
        )?;

        let real_division = Boolean::and(
            &mut cs.namespace(|| "real_division"),
            &not_dummy,
            &op2_is_div,
        )?;

        let real_div_and_b_is_zero = Boolean::and(
            &mut cs.namespace(|| "real_div_and_b_is_zero"),
            &real_division,
            b_is_zero,
        )?;

        let valid_types_and_not_div_by_zero = Boolean::and(
            &mut cs.namespace(|| "Op2 called with no errors"),
            &valid_types,
            &Boolean::not(&real_div_and_b_is_zero),
        )?;

        let op2_not_both_num_and_not_cons_or_strcons_or_hide_or_equal_or_num_equal = Boolean::and(
            &mut cs
                .namespace(|| "not both num and not cons or strcons or hide or equal or num_equal"),
            &Boolean::not(&both_args_are_nums),
            &Boolean::not(&is_cons_or_strcons_or_hide_or_equal_or_num_equal),
        )?;

        let args_not_char_str = &Boolean::not(&args_are_char_str);
        let invalid_strcons_tag = Boolean::and(
            &mut cs.namespace(|| "invalid_strcons_tag"),
            args_not_char_str,
            &is_strcons,
        )?;

        let any_error1 = constraints::or(
            &mut cs.namespace(|| "first two errors"),
            &Boolean::not(&valid_types_and_not_div_by_zero),
            &op2_not_both_num_and_not_cons_or_strcons_or_hide_or_equal_or_num_equal,
        )?;

        let any_error = constraints::or(
            &mut cs.namespace(|| "some error happened"),
            &any_error1,
            &invalid_strcons_tag,
        )?;

        let op2_is_eval = alloc_equal(cs.namespace(|| "op2_is_eval"), op2.tag(), &g.op2_eval_tag)?;

        let the_cont_ = AllocatedContPtr::pick(
            &mut cs.namespace(|| "maybe type or div by zero error"),
            &any_error,
            &g.error_ptr_cont,
            &continuation,
        )?;

        let the_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "maybe eval cont"),
            &op2_is_eval,
            &continuation,
            &the_cont_,
        )?;

        let the_expr_ = AllocatedPtr::pick(
            &mut cs.namespace(|| "maybe expr error"),
            &any_error,
            result,
            &final_res,
        )?;

        let the_expr = AllocatedPtr::pick(
            &mut cs.namespace(|| "maybe eval expr"),
            &op2_is_eval,
            &arg1,
            &the_expr_,
        )?;

        let the_env = AllocatedPtr::pick(
            &mut cs.namespace(|| "maybe eval env"),
            &op2_is_eval,
            arg2,
            env,
        )?;

        let make_thunk_num = pick(
            &mut cs.namespace(|| "maybe eval make_thunk_num"),
            &op2_is_eval,
            &g.false_num,
            &g.true_num,
        )?;

        (the_expr, the_env, the_cont, make_thunk_num)
    };

    results.add_clauses_cont(
        ContTag::Binop2,
        &the_expr,
        &the_env,
        &the_cont,
        &make_thunk_num,
    );

    // Continuation::If
    /////////////////////////////////////////////////////////////////////////////
    let (res, the_cont) = {
        let mut cs = cs.namespace(|| "If");
        let unevaled_args = AllocatedPtr::by_index(0, &continuation_components);
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
            &mut cs.namespace(|| "unevaled_args cons"),
            g,
            &unevaled_args,
            store,
        )?;

        let condition_is_nil =
            condition.alloc_equal(&mut cs.namespace(|| "condition is nil"), &g.nil_ptr)?;

        let (arg2, end) = car_cdr(&mut cs.namespace(|| "more cons"), g, &more, store)?;

        let end_is_nil = end.alloc_equal(&mut cs.namespace(|| "args_is_nil"), &g.nil_ptr)?;

        let res = AllocatedPtr::pick(
            &mut cs.namespace(|| "pick arg1 or arg2"),
            &condition_is_nil,
            &arg2,
            &arg1,
        )?;

        let the_res = AllocatedPtr::pick(
            &mut cs.namespace(|| "end is nil pick res"),
            &end_is_nil,
            &res,
            &arg1,
        )?;

        let the_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "end is nil pick cont"),
            &end_is_nil,
            &continuation,
            &g.error_ptr_cont,
        )?;

        (the_res, the_cont)
    };

    results.add_clauses_cont(ContTag::If, &res, env, &the_cont, &g.false_num);

    // Continuation::Lookup
    /////////////////////////////////////////////////////////////////////////////
    let saved_env = AllocatedPtr::by_index(0, &continuation_components);
    let continuation = AllocatedContPtr::by_index(1, &continuation_components);
    results.add_clauses_cont(
        ContTag::Lookup,
        result,
        &saved_env,
        &continuation,
        &g.true_num,
    );

    // Continuation::Tail
    /////////////////////////////////////////////////////////////////////////////
    let saved_env = AllocatedPtr::by_index(0, &continuation_components);
    let continuation = AllocatedContPtr::by_index(1, &continuation_components);

    results.add_clauses_cont(
        ContTag::Tail,
        result,
        &saved_env,
        &continuation,
        &g.true_num,
    );

    // Continuation::Let, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    let (body, extended_env, tail_cont) = {
        let mut cs = cs.namespace(|| "Let");
        let var = AllocatedPtr::by_index(0, &continuation_components);
        let body = AllocatedPtr::by_index(1, &continuation_components);
        let let_cont = AllocatedContPtr::by_index(3, &continuation_components);

        let extended_env = extend(
            &mut cs.namespace(|| "extend env"),
            g,
            store,
            env,
            &var,
            result,
        )?;

        let continuation_is_tail = alloc_equal(
            &mut cs.namespace(|| "continuation is tail"),
            let_cont.tag(),
            &g.tail_cont_tag,
        )?;

        let tail_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "the tail continuation"),
            &continuation_is_tail,
            &let_cont,
            &newer_cont,
        );

        (body, extended_env, tail_cont)
    };
    let let_cont = match tail_cont {
        Ok(c) => c,
        Err(_) => g.dummy_ptr.clone(),
    };
    results.add_clauses_cont(ContTag::Let, &body, &extended_env, &let_cont, &g.false_num);

    // Continuation::LetRec, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    let (body, extended_env, return_cont) = {
        let mut cs = cs.namespace(|| "LetRec");
        let var = AllocatedPtr::by_index(0, &continuation_components);
        let body = AllocatedPtr::by_index(1, &continuation_components);
        let letrec_cont = AllocatedContPtr::by_index(3, &continuation_components);

        let extended_env = extend_rec(
            &mut cs.namespace(|| "extend_rec env"),
            g,
            env,
            &var,
            result,
            store,
        )?;

        let is_error = extended_env.alloc_equal(&mut cs.namespace(|| "is_error"), &g.error_ptr)?;

        let continuation_is_tail = alloc_equal(
            &mut cs.namespace(|| "continuation is tail"),
            letrec_cont.tag(),
            &g.tail_cont_tag,
        )?;

        let tail_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "the tail continuation"),
            &continuation_is_tail,
            &letrec_cont,
            &newer_cont,
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
        ContTag::LetRec,
        &body,
        &extended_env,
        &return_cont,
        &g.false_num,
    );

    // Continuation::Unop newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    let (the_expr, the_env, the_cont, make_thunk_num) = {
        let unop_op1 = AllocatedPtr::by_index(0, &continuation_components);
        let other_unop_continuation = AllocatedContPtr::by_index(1, &continuation_components);
        let op1_is_emit = alloc_equal(
            &mut cs.namespace(|| "op1_is_emit"),
            unop_op1.tag(),
            &g.op1_emit_tag,
        )?;
        let op1_is_eval = alloc_equal(
            &mut cs.namespace(|| "op1_is_eval"),
            unop_op1.tag(),
            &g.op1_eval_tag,
        )?;
        let unop_continuation = AllocatedContPtr::pick(
            &mut cs.namespace(|| "continuation"),
            &op1_is_emit,
            &newer_cont,
            &other_unop_continuation,
        )?;

        let result_has_cons_tag = alloc_equal(
            &mut cs.namespace(|| "result_has_cons_tag"),
            result.tag(),
            &g.cons_tag,
        )?;

        let result_has_str_tag = alloc_equal(
            &mut cs.namespace(|| "result_has_str_tag"),
            result.tag(),
            &g.str_tag,
        )?;

        let result_is_nil =
            result.alloc_equal(&mut cs.namespace(|| "result_is_nil"), &g.nil_ptr)?;

        let car_cdr_has_valid_tag_ = constraints::or(
            &mut cs.namespace(|| "car_cdr_has_valid_tag_"),
            &result_has_cons_tag,
            &result_has_str_tag,
        )?;

        let car_cdr_has_valid_tag = constraints::or(
            &mut cs.namespace(|| "car_cdr_has_valid_tag"),
            &car_cdr_has_valid_tag_,
            &result_is_nil,
        )?;

        let op1_is_car = alloc_equal(
            &mut cs.namespace(|| "op1_is_car"),
            unop_op1.tag(),
            &g.op1_car_tag,
        )?;

        let op1_is_cdr = alloc_equal(
            &mut cs.namespace(|| "op1_is_cdr"),
            unop_op1.tag(),
            &g.op1_cdr_tag,
        )?;

        let op1_is_car_or_cdr = constraints::or(
            &mut cs.namespace(|| "op1_is_car_or_cdr"),
            &op1_is_car,
            &op1_is_cdr,
        )?;

        let car_cdr_has_invalid_tag = Boolean::and(
            &mut cs.namespace(|| "car_cdr_has_invalid_tag"),
            &op1_is_car_or_cdr,
            &Boolean::not(&car_cdr_has_valid_tag),
        )?;

        let op1_is_comm = alloc_equal(
            &mut cs.namespace(|| "op1_is_comm"),
            unop_op1.tag(),
            &g.op1_comm_tag,
        )?;

        let op1_is_num = alloc_equal(
            &mut cs.namespace(|| "op1_is_num"),
            unop_op1.tag(),
            &g.op1_num_tag,
        )?;

        let op1_is_char = alloc_equal(
            &mut cs.namespace(|| "op1_is_char"),
            unop_op1.tag(),
            &g.op1_char_tag,
        )?;

        let tag_is_char = alloc_equal(
            &mut cs.namespace(|| "tag_is_char"),
            result.tag(),
            &g.char_tag,
        )?;

        let tag_is_num = alloc_equal(&mut cs.namespace(|| "tag_is_num"), result.tag(), &g.num_tag)?;

        let tag_is_comm = alloc_equal(
            &mut cs.namespace(|| "tag_is_comm"),
            result.tag(),
            &g.comm_tag,
        )?;

        let tag_is_num_or_comm = constraints::or(
            &mut cs.namespace(|| "tag_is_num_or_comm"),
            &tag_is_num,
            &tag_is_comm,
        )?;

        let tag_is_num_or_char = constraints::or(
            &mut cs.namespace(|| "tag_is_num_or_char"),
            &tag_is_num,
            &tag_is_char,
        )?;

        let tag_is_num_or_comm_or_char = constraints::or(
            &mut cs.namespace(|| "tag_is_num_or_comm_or_char"),
            &tag_is_num_or_comm,
            &tag_is_char,
        )?;

        let comm_invalid_tag_error = Boolean::and(
            &mut cs.namespace(|| "comm_invalid_tag_error"),
            &op1_is_comm,
            &Boolean::not(&tag_is_num_or_comm),
        )?;

        let num_invalid_tag_error = Boolean::and(
            &mut cs.namespace(|| "num_invalid_tag_error"),
            &op1_is_num,
            &Boolean::not(&tag_is_num_or_comm_or_char),
        )?;

        let char_invalid_tag_error = Boolean::and(
            &mut cs.namespace(|| "char_invalid_tag_error"),
            &op1_is_char,
            &Boolean::not(&tag_is_num_or_char),
        )?;

        // Any error? Compute the OR of individual errors
        let any_error1 = constraints::or(
            &mut cs.namespace(|| "any_error1"),
            &car_cdr_has_invalid_tag,
            &comm_invalid_tag_error,
        )?;

        let any_error2 = constraints::or(
            &mut cs.namespace(|| "any_erro2"),
            &any_error1,
            &num_invalid_tag_error,
        )?;

        let any_error = constraints::or(
            &mut cs.namespace(|| "any_error"),
            &any_error2,
            &char_invalid_tag_error,
        )?;

        let the_expr = AllocatedPtr::pick(
            &mut cs.namespace(|| "the_expr"),
            &any_error,
            result,
            &unop_val,
        )?;

        let the_env = AllocatedPtr::pick(
            &mut cs.namespace(|| "the_env"),
            &op1_is_eval,
            &g.nil_ptr,
            env,
        )?;

        let the_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "the_cont"),
            &any_error,
            &g.error_ptr_cont,
            &unop_continuation,
        )?;

        let make_thunk_num = pick(
            &mut cs.namespace(|| "pick make_thunk_num"),
            &op1_is_eval,
            &g.false_num,
            &g.true_num,
        )?;

        (the_expr, the_env, the_cont, make_thunk_num)
    };

    results.add_clauses_cont(
        ContTag::Unop,
        &the_expr,
        &the_env,
        &the_cont,
        &make_thunk_num,
    );

    // Main multi_case
    /////////////////////////////////////////////////////////////////////////////

    let all_clauses = [
        &results.expr_tag_clauses[..],
        &results.expr_hash_clauses[..],
        &results.env_tag_clauses[..],
        &results.env_hash_clauses[..],
        &results.cont_tag_clauses[..],
        &results.cont_hash_clauses[..],
        &results.make_thunk_num_clauses[..],
    ];

    let apply_cont_defaults = [
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.false_num,
    ];

    let case_results = multi_case(
        &mut cs.namespace(|| "apply_continuation multicase"),
        cont.tag(),
        &all_clauses,
        &apply_cont_defaults,
        g,
    )?;

    let result_expr = AllocatedPtr::by_index(0, &case_results);
    let result_env = AllocatedPtr::by_index(1, &case_results);
    let result_cont = AllocatedContPtr::by_index(2, &case_results);
    let make_thunk_num = case_results[6].clone();

    Ok((result_expr, result_env, result_cont, make_thunk_num))
}

fn hide<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    secret: &AllocatedNum<F>,
    maybe_payload: &AllocatedPtr<F>,
    store: &Store<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    AllocatedPtr::construct_commitment(
        &mut cs.namespace(|| "commitment hash"),
        g,
        store,
        secret,
        maybe_payload,
    )
}

fn num<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    maybe_num: &AllocatedPtr<F>,
    store: &Store<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let num_ptr = if let Some(ptr) = maybe_num.ptr(store).as_ref() {
        let scalar_ptr = store.get_expr_hash(ptr).expect("expr hash missing");
        match store.get_num(crate::Num::Scalar::<F>(*scalar_ptr.value())) {
            Some(n) => n,
            None => store.get_nil(),
        }
    } else {
        store.get_nil()
    };
    AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "num"), store, || Ok(&num_ptr))
}

fn comm<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    maybe_comm: &AllocatedPtr<F>,
    store: &Store<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let hash = match maybe_comm.hash().get_value() {
        Some(h) => h,
        None => F::zero(), // dummy value
    };
    let comm_ptr = match store.get_maybe_opaque(Tag::Comm, hash) {
        Some(c) => c,
        None => store.get_nil(),
    };
    AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "open"), store, || Ok(&comm_ptr))
}

fn char_op<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    maybe_char: &AllocatedPtr<F>,
    store: &Store<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let char_ptr = if let Some(ptr) = maybe_char.ptr(store).as_ref() {
        let scalar_ptr = store.get_expr_hash(ptr).expect("expr hash missing");
        match scalar_ptr.value().to_u32() {
            Some(n) => store.get_char(char::from_u32(n).unwrap()),
            None => store.get_nil(),
        }
    } else {
        store.get_nil()
    };
    AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "char_op"), store, || Ok(&char_ptr))
}

fn car_cdr<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    maybe_cons: &AllocatedPtr<F>,
    store: &Store<F>,
) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>), SynthesisError> {
    let maybe_cons_is_cons = alloc_equal(
        &mut cs.namespace(|| "maybe_cons_is_cons"),
        maybe_cons.tag(),
        &g.cons_tag,
    )?;

    let maybe_cons_is_str = alloc_equal(
        &mut cs.namespace(|| "maybe_cons_is_string"),
        maybe_cons.tag(),
        &g.str_tag,
    )?;

    let maybe_str_is_empty = alloc_is_zero(
        &mut cs.namespace(|| "maybe_string_is_empty"),
        maybe_cons.hash(),
    )?;

    let maybe_cons_is_non_empty_str = Boolean::and(
        &mut cs.namespace(|| "maybe_cons_is_non_empty_str"),
        &maybe_cons_is_str,
        &Boolean::not(&maybe_str_is_empty),
    );

    let is_cons = constraints::or(
        &mut cs.namespace(|| "is_cons"),
        &maybe_cons_is_cons,
        &maybe_cons_is_non_empty_str.unwrap(),
    )?;

    let (car, cdr) = if let Some(ptr) = maybe_cons.ptr(store).as_ref() {
        if maybe_cons_is_cons
            .get_value()
            .expect("maybe_cons_is_cons is missing")
            || maybe_cons_is_str
                .get_value()
                .expect("maybe_cons_is_str is missing")
        {
            store.car_cdr(ptr)
        } else {
            (store.get_nil(), store.get_nil())
        }
    } else {
        // Dummy
        (store.get_nil(), store.get_nil())
    };

    let allocated_car = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "car"), store, || Ok(&car))?;
    let allocated_cdr = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "cdr"), store, || Ok(&cdr))?;

    let constructed_cons = AllocatedPtr::construct_cons(
        &mut cs.namespace(|| "cons"),
        g,
        store,
        &allocated_car,
        &allocated_cdr,
    )?;

    let real_cons = alloc_equal(
        &mut cs.namespace(|| "cons is real"),
        maybe_cons.hash(),
        constructed_cons.hash(),
    )?;

    // If `maybe_cons` is not a cons, then it is dummy. No check is necessary.
    // If `maybe_cons` is an empty string, then the hash is zero.
    // Otherwise, we must enforce equality of hashes.
    enforce_implication(
        &mut cs.namespace(|| "is cons implies real cons"),
        &is_cons,
        &real_cons,
    )?;

    Ok((allocated_car, allocated_cdr))
}

fn extend<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    store: &Store<F>,
    env: &AllocatedPtr<F>,
    var: &AllocatedPtr<F>,
    val: &AllocatedPtr<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let new_binding =
        AllocatedPtr::construct_cons(&mut cs.namespace(|| "extend binding"), g, store, var, val)?;
    AllocatedPtr::construct_cons(cs, g, store, &new_binding, env)
}

fn extend_rec<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    env: &AllocatedPtr<F>,
    var: &AllocatedPtr<F>,
    val: &AllocatedPtr<F>,
    store: &Store<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let (binding_or_env, rest) = car_cdr(&mut cs.namespace(|| "car_cdr env"), g, env, store)?;
    let (var_or_binding, _val_or_more_bindings) = car_cdr(
        &mut cs.namespace(|| "car_cdr binding_or_env"),
        g,
        &binding_or_env,
        store,
    )?;

    let cons =
        AllocatedPtr::construct_cons(&mut cs.namespace(|| "cons var val"), g, store, var, val)?;
    let list = AllocatedPtr::construct_list(&mut cs.namespace(|| "list cons"), g, store, &[&cons])?;

    let new_env_if_sym_or_nil = AllocatedPtr::construct_cons(
        &mut cs.namespace(|| "new_env_if_sym_or_nil"),
        g,
        store,
        &list,
        env,
    )?;

    let cons2 = AllocatedPtr::construct_cons(
        &mut cs.namespace(|| "cons cons binding_or_env"),
        g,
        store,
        &cons,
        &binding_or_env,
    )?;

    let cons3 = AllocatedPtr::construct_cons(
        &mut cs.namespace(|| "cons cons2 rest"),
        g,
        store,
        &cons2,
        &rest,
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

    let new_env_if_cons = AllocatedPtr::pick(
        &mut cs.namespace(|| "new_env_if_cons"),
        &is_cons,
        &cons3,
        &g.error_ptr, // This is being used as a signal, since extend_rec is expected to return a valid env.
    )?;

    AllocatedPtr::pick(
        &mut cs.namespace(|| "extend_rec result"),
        &is_sym_or_nil,
        &new_env_if_sym_or_nil,
        &new_env_if_cons,
    )
}

/// Prints out the full CS for debugging purposes
#[allow(dead_code)]
pub(crate) fn print_cs<F: LurkField, C: Comparable<F>>(this: &C) -> String {
    let mut out = String::new();
    out += &format!("num_inputs: {}\n", this.num_inputs());
    out += &format!("num_constraints: {}\n", this.num_constraints());
    out += "\ninputs:\n";
    for (i, input) in this.inputs().iter().enumerate() {
        out += &format!("{}: {}\n", i, input);
    }
    out += "\nconstraints:\n";
    for (i, cs) in this.constraints().iter().enumerate() {
        out += &format!(
            "{}: {}:\n  {:?}\n  {:?}\n  {:?}\n",
            i,
            cs.3,
            cs.0.iter().collect::<Vec<_>>(),
            cs.1.iter().collect::<Vec<_>>(),
            cs.2.iter().collect::<Vec<_>>()
        );
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::{empty_sym_env, Evaluable, IO};
    use crate::proof::Provable;
    use crate::proof::{groth16::Groth16Prover, Prover};
    use crate::store::Store;
    use bellperson::groth16;
    use bellperson::util_cs::{
        metric_cs::MetricCS, test_cs::TestConstraintSystem, Comparable, Delta,
    };
    use blstrs::{Bls12, Scalar as Fr};
    use pairing_lib::Engine;

    const DEFAULT_CHUNK_FRAME_COUNT: usize = 1;

    #[test]
    fn num_self_evaluating() {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let num = store.num(123);

        let input = IO {
            expr: num,
            env,
            cont: store.intern_cont_outermost(),
        };

        let (_, witness) = input.reduce(&mut store).unwrap();

        let public_params = Groth16Prover::create_groth_params(DEFAULT_CHUNK_FRAME_COUNT).unwrap();
        let groth_prover = Groth16Prover::new(DEFAULT_CHUNK_FRAME_COUNT);
        let groth_params = &public_params.0;

        let vk = &groth_params.vk;
        let pvk = groth16::prepare_verifying_key(vk);

        let test_with_output = |output: IO<Fr>, expect_success: bool, store: &Store<Fr>| {
            let mut cs = TestConstraintSystem::new();

            let mut cs_blank = MetricCS::<Fr>::new();
            let blank_multiframe =
                MultiFrame::<<Bls12 as Engine>::Fr, _, _>::blank(DEFAULT_CHUNK_FRAME_COUNT);

            blank_multiframe
                .synthesize(&mut cs_blank)
                .expect("failed to synthesize");

            let multiframes = MultiFrame::from_frames(
                DEFAULT_CHUNK_FRAME_COUNT,
                &[Frame {
                    input,
                    output,
                    i: 0,
                    witness,
                }],
                store,
            );

            let multiframe = &multiframes[0];

            multiframe
                .clone()
                .synthesize(&mut cs)
                .expect("failed to synthesize");

            let delta = cs.delta(&cs_blank, false);
            assert!(delta == Delta::Equal);

            //println!("{}", print_cs(&cs));
            assert_eq!(20513, cs.num_constraints());
            assert_eq!(13, cs.num_inputs());
            assert_eq!(20368, cs.aux().len());

            let public_inputs = multiframe.public_inputs();
            let mut rng = rand::thread_rng();

            let proof = groth_prover
                .prove(multiframe.clone(), groth_params, &mut rng)
                .unwrap();
            let cs_verified = cs.is_satisfied() && cs.verify(&public_inputs);
            let verified = multiframe
                .clone()
                .verify_groth16_proof(&pvk, proof)
                .unwrap();

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
                expr: num,
                env,
                cont: store.intern_cont_terminal(),
            };

            test_with_output(output, true, &store);
        }

        // Failure
        {
            // Wrong type, so tag should differ.
            let bad_output_tag = IO {
                expr: store.sym("SYMBOL"),
                env,
                cont: store.intern_cont_terminal(),
            };

            test_with_output(bad_output_tag, false, &store);
        }

        {
            // Wrong value, so hash should differ.
            let bad_output_value = IO {
                expr: store.num(999),
                env,
                cont: store.intern_cont_terminal(),
            };

            test_with_output(bad_output_value, false, &store);
        }

        {
            // Wrong new env.
            let bad_output_tag = IO {
                expr: num,
                env: store.sym("not-an-env"),
                cont: store.intern_cont_terminal(),
            };

            test_with_output(bad_output_tag, false, &store);
        }
    }

    #[test]
    fn nil_self_evaluating() {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let nil = store.nil();

        let input = IO {
            expr: nil,
            env,
            cont: store.intern_cont_outermost(),
        };

        let (_, witness) = input.reduce(&mut store).unwrap();

        let test_with_output = |output: IO<Fr>, expect_success: bool, store: &Store<Fr>| {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let frame = Frame {
                input,
                output,
                i: 0,
                witness,
            };

            MultiFrame::<<Bls12 as Engine>::Fr, _, _>::from_frames(
                DEFAULT_CHUNK_FRAME_COUNT,
                &[frame],
                store,
            )[0]
            .clone()
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
                expr: nil,
                env,
                cont: store.intern_cont_terminal(),
            };

            test_with_output(output, true, &store);
        }

        // Failure
        {
            {
                // Wrong type, so tag should differ.
                let bad_output_tag = IO {
                    expr: store.sym("SYMBOL"),
                    env,
                    cont: store.intern_cont_terminal(),
                };

                test_with_output(bad_output_tag, false, &store);
            }
            {
                // Wrong value, so hash should differ.
                let bad_output_value = IO {
                    expr: store.num(999),
                    env,
                    cont: store.intern_cont_terminal(),
                };

                test_with_output(bad_output_value, false, &store);
            }
        }
    }

    #[test]
    #[allow(dead_code)]
    fn t_self_evaluating() {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let t = store.t();

        let input = IO {
            expr: t,
            env,
            cont: store.intern_cont_outermost(),
        };

        let (_, witness) = input.reduce(&mut store).unwrap();

        let test_with_output = |output: IO<Fr>, expect_success: bool, store: &Store<Fr>| {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let frame = Frame {
                input,
                output,
                i: 0,
                witness,
            };

            MultiFrame::<<Bls12 as Engine>::Fr, _, _>::from_frames(
                DEFAULT_CHUNK_FRAME_COUNT,
                &[frame],
                store,
            )[0]
            .clone()
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
                expr: t,
                env,
                cont: store.intern_cont_terminal(),
            };

            test_with_output(output, true, &store);
        }

        // Failure
        {
            {
                // Wrong type, so tag should differ.
                let bad_output_tag = IO {
                    expr: store.num(999),
                    env,
                    cont: store.intern_cont_terminal(),
                };

                test_with_output(bad_output_tag, false, &store);
            }
            {
                // Wrong symbol, so hash should differ.
                let bad_output_value = IO {
                    expr: store.sym("S"),
                    env,
                    cont: store.intern_cont_terminal(),
                };
                test_with_output(bad_output_value, false, &store);
            }
        }
    }

    #[test]
    fn fun_self_evaluating() {
        let mut store = Store::default();
        let env = empty_sym_env(&store);
        let var = store.sym("a");
        let body = store.intern_list(&[var]);
        let fun = store.intern_fun(var, body, env);

        let input = IO {
            expr: fun,
            env,
            cont: store.intern_cont_outermost(),
        };

        let (_, witness) = input.reduce(&mut store).unwrap();

        let test_with_output = |output: IO<Fr>, expect_success: bool, store: &Store<Fr>| {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let frame = Frame {
                input,
                output,
                i: 0,
                witness,
            };

            MultiFrame::<<Bls12 as Engine>::Fr, _, _>::from_frames(
                DEFAULT_CHUNK_FRAME_COUNT,
                &[frame],
                store,
            )[0]
            .clone()
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
                expr: fun,
                env,
                cont: store.intern_cont_terminal(),
            };

            test_with_output(output, true, &store);
        }

        // Failure
        {
            {
                // Wrong type, so tag should differ.
                let bad_output_tag = IO {
                    expr: store.sym("SYMBOL"),
                    env,
                    cont: store.intern_cont_terminal(),
                };

                test_with_output(bad_output_tag, false, &store);
            }
            {
                // Wrong value, so hash should differ.
                let bad_output_value = IO {
                    expr: store.num(999),
                    env,
                    cont: store.intern_cont_terminal(),
                };

                test_with_output(bad_output_value, false, &store);
            }
        }
    }

    #[test]
    #[allow(dead_code)]
    fn non_self_evaluating() {
        let mut store = Store::default();
        let env = empty_sym_env(&store);

        // Input is not self-evaluating.
        let expr = store.read("(+ 1 2)").unwrap();
        let input = IO {
            expr,
            env,
            cont: store.intern_cont_outermost(),
        };

        let (_, witness) = input.reduce(&mut store).unwrap();

        let test_with_output = |output, expect_success, store: &mut Store<Fr>| {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let frame = Frame {
                input,
                output,
                i: 0,
                witness,
            };

            MultiFrame::<<Bls12 as Engine>::Fr, _, _>::from_frames(
                DEFAULT_CHUNK_FRAME_COUNT,
                &[frame],
                store,
            )[0]
            .clone()
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
                // Output does not equal input.
                let output = IO {
                    expr,
                    env,
                    cont: store.intern_cont_terminal(),
                };

                test_with_output(output, false, &mut store);
            }
        }
    }
}
