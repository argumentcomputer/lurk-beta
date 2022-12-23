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
    hash_witness::{ConsName, ContName},
    store::{HashScalar, ScalarPointer},
};

use super::gadgets::constraints::{
    self, alloc_equal, alloc_is_zero, boolean_to_num, enforce_implication, or, pick,
};
use crate::circuit::{
    gadgets::hashes::{AllocatedConsWitness, AllocatedContWitness},
    ToInputs,
};
use crate::eval::{Frame, Witness, IO};
use crate::hash_witness::HashWitness;
use crate::proof::Provable;
use crate::store::{ContTag, Op1, Op2, Ptr, Store, Tag, Thunk};

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
            let cons_witness = match self.witness.map(|x| x.conses) {
                Some(hw) => hw,
                None => HashWitness::new_blank(),
            };
            let mut allocated_cons_witness = AllocatedConsWitness::from_cons_witness(
                &mut cs.namespace(|| format!("allocated_cons_witness {}", i)),
                store,
                &cons_witness,
            )?;

            let cont_witness = match self.witness.map(|x| x.conts) {
                Some(hw) => hw,
                None => HashWitness::new_blank(),
            };

            let mut allocated_cont_witness = AllocatedContWitness::from_cont_witness(
                &mut cs.namespace(|| format!("allocated_cont_witness {}", i)),
                store,
                &cont_witness,
            )?;

            reduce_expression(
                &mut cs.namespace(|| format!("reduce expression {}", i)),
                &input_expr,
                &input_env,
                &input_cont,
                &self.witness,
                &mut allocated_cons_witness,
                &mut allocated_cont_witness,
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
                    if let Some(next_input) = frame.input {
                        // Ensure all intermediate allocated I/O values match the provided executation trace.
                        assert_eq!(
                            allocated_io.0.hash().get_value(),
                            store.hash_expr(&next_input.expr).map(|x| *x.value()),
                            "expr mismatch"
                        );
                        assert_eq!(
                            allocated_io.1.hash().get_value(),
                            store.hash_expr(&next_input.env).map(|x| *x.value()),
                            "env mismatch"
                        );
                        assert_eq!(
                            allocated_io.2.hash().get_value(),
                            store.hash_cont(&next_input.cont).map(|x| *x.value()),
                            "cont mismatch"
                        );
                    };
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
    newer_cont2_not_dummy_clauses: Vec<CaseClause<'a, F>>,
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
        newer_cont2_not_dummy: &'a AllocatedNum<F>,
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
        add_clause_single(
            &mut self.newer_cont2_not_dummy_clauses,
            key,
            newer_cont2_not_dummy,
        );
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
    allocated_cons_witness: &mut AllocatedConsWitness<F>,
    allocated_cont_witness: &mut AllocatedContWitness<F>,
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
        results.add_clauses_expr(Tag::Key, expr, env, cont, &g.true_num);
    };

    let cont_is_terminal = alloc_equal(
        &mut cs.namespace(|| "cont_is_terminal"),
        cont.tag(),
        g.terminal_ptr.tag(),
    )?;
    let cont_is_error = alloc_equal(
        &mut cs.namespace(|| "cont_is_error"),
        cont.tag(),
        g.error_ptr.tag(),
    )?;

    // Enforce (expr.tag == thunk_tag) implies (expr_thunk_hash == expr.hash).
    let expr_is_thunk = constraints::alloc_equal(
        &mut cs.namespace(|| "expr.tag == thunk_tag"),
        expr.tag(),
        &g.thunk_tag,
    )?;

    // If expr is a thunk, this will allocate its components and hash, etc.
    // If not, these will be dummies.
    // NOTE: this allocation is unconstrained. See necessary constraint immediately below.
    let (expr_thunk_hash, expr_thunk_value, expr_thunk_continuation) = expr
        .allocate_thunk_components_unconstrained(
            &mut cs.namespace(|| "allocate thunk components"),
            store,
        )?;
    {
        // This constrains the thunk allocation.
        implies_equal!(cs, &expr_is_thunk, &expr_thunk_hash, expr.hash());

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
    let cont_is_not_error = Boolean::not(&cont_is_error);
    let reduce_sym_not_dummy = and!(cs, &reduce_sym_not_dummy, &cont_is_not_terminal)?;

    let (sym_result, sym_env, sym_cont, sym_apply_cont) = reduce_sym(
        &mut cs.namespace(|| "eval Sym"),
        expr,
        env,
        cont,
        &reduce_sym_not_dummy,
        witness,
        allocated_cons_witness,
        allocated_cont_witness,
        store,
        g,
    )?;

    results.add_clauses_expr(Tag::Sym, &sym_result, &sym_env, &sym_cont, &sym_apply_cont);
    // --

    // --
    let expr_is_cons = alloc_equal(
        &mut cs.namespace(|| "reduce_cons_not_dummy0"),
        expr.tag(),
        &g.cons_tag,
    )?;

    let reduce_cons_not_dummy = and!(cs, &expr_is_cons, &cont_is_not_error, &cont_is_not_terminal)?;

    let (cons_result, cons_env, cons_cont, cons_apply_cont) = reduce_cons(
        &mut cs.namespace(|| "eval Cons"),
        expr,
        env,
        cont,
        &reduce_cons_not_dummy,
        witness,
        allocated_cons_witness,
        allocated_cont_witness,
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
        allocated_cons_witness,
        allocated_cont_witness,
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
        allocated_cont_witness,
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

    allocated_cons_witness.assert_final_invariants();
    allocated_cont_witness.witness.all_names();
    allocated_cont_witness.assert_final_invariants();

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
    allocated_cons_witness: &mut AllocatedConsWitness<F>,
    allocated_cont_witness: &mut AllocatedContWitness<F>,
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
    let sym_otherwise = sym_is_self_evaluating.not();

    let env_not_dummy = and!(cs, &sym_otherwise, not_dummy)?;
    let (binding, smaller_env) = car_cdr_named(
        &mut cs.namespace(|| "If unevaled_args cons"),
        g,
        env,
        ConsName::Env,
        allocated_cons_witness,
        &env_not_dummy,
        store,
    )?;

    let env_is_nil = env.alloc_equal(&mut cs.namespace(|| "env is nil"), &g.nil_ptr)?;
    let env_not_nil = env_is_nil.not();

    let otherwise = and!(cs, &env_not_dummy, &env_not_nil)?;

    let binding_is_nil = binding.alloc_equal(&mut cs.namespace(|| "binding is nil"), &g.nil_ptr)?;
    let binding_not_nil = binding_is_nil.not();

    let binding_is_cons = alloc_equal(
        &mut cs.namespace(|| "binding_is_cons"),
        binding.tag(),
        &g.cons_tag,
    )?;
    let otherwise_and_binding_is_nil = and!(cs, &otherwise, &binding_is_nil)?;
    let otherwise_and_binding_not_nil = and!(cs, &otherwise, &binding_not_nil)?;

    let env_car_not_dummy = and!(cs, &otherwise, &binding_is_cons, not_dummy)?;
    let (var_or_rec_binding, val_or_more_rec_env) = car_cdr_named(
        &mut cs.namespace(|| "car_cdr binding"),
        g,
        &binding,
        ConsName::EnvCar,
        allocated_cons_witness,
        &env_car_not_dummy,
        store,
    )?;

    let var_or_rec_binding_is_sym_ = alloc_equal(
        &mut cs.namespace(|| "var_or_rec_binding_is_sym_"),
        var_or_rec_binding.tag(),
        &g.sym_tag,
    )?;
    let var_or_rec_binding_is_sym = and!(
        cs,
        &var_or_rec_binding_is_sym_,
        &otherwise_and_binding_not_nil
    )?;

    let v = var_or_rec_binding.clone();
    let val = val_or_more_rec_env.clone();
    let v_is_expr1 = expr.alloc_equal(&mut cs.namespace(|| "v_is_expr1"), &v)?;
    let v_not_expr1 = v_is_expr1.not();

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

    let envcaar_not_dummy = and!(cs, &otherwise_and_cons, not_dummy)?;
    let (v2, val2) = car_cdr_named(
        &mut cs.namespace(|| "car_cdr var_or_rec_binding"),
        g,
        &var_or_rec_binding,
        ConsName::EnvCaar,
        allocated_cons_witness,
        &envcaar_not_dummy,
        store,
    )?;

    let val2_is_fun = equal!(cs, val2.tag(), &g.fun_tag)?;
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

    let apply_cont_num = pick!(cs, &apply_cont_bool, &g.true_num, &g.false_num)?;

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

    let rec_env = binding;

    let extended_env_not_dummy = and!(cs, &val2_is_fun, not_dummy, &v2_is_expr_real)?;

    // NOTE: this allocation is unconstrained. See necessary constraint immediately below.
    let (fun_hash, fun_arg, fun_body, fun_closed_env) = Ptr::allocate_maybe_fun_unconstrained(
        &mut cs.namespace(|| "closure to extend"),
        store,
        witness.as_ref().and_then(|w| w.closure_to_extend.as_ref()),
    )?;

    // Without this, fun is unconstrained.
    implies_equal!(cs, &extended_env_not_dummy, &fun_hash, val2.hash());

    let extended_env = AllocatedPtr::construct_cons_named(
        &mut cs.namespace(|| "extended_env"),
        g,
        &rec_env,
        &fun_closed_env,
        ConsName::ExtendedClosureEnv,
        allocated_cons_witness,
        &extended_env_not_dummy,
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
    let smaller_rec_env_not_nil = Boolean::not(&smaller_rec_env_is_nil);

    let smaller_rec_env_not_dummy = and!(
        cs,
        &smaller_rec_env_not_nil,
        not_dummy,
        &otherwise_and_v2_not_expr
    )?;

    let with_smaller_rec_env = AllocatedPtr::construct_cons_named(
        &mut cs.namespace(|| "with_smaller_rec_env"),
        g,
        &smaller_rec_env,
        &smaller_env,
        ConsName::EnvToUse,
        allocated_cons_witness,
        &smaller_rec_env_not_dummy,
    )?;

    let env_to_use = pick_ptr!(
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
    let cond0 = and!(cs, &env_is_nil, &env_not_dummy)?;
    {
        // implies_equal_t!(cs, &cond0, &output_expr, &expr);
        // implies_equal_t!(cs, &cond0, &output_env, &env);
        implies_equal_t!(cs, &cond0, output_cont, g.error_ptr);
    }

    let cs = &mut cs.namespace(|| "sym_is_self_evaluating");
    let cond1 = and!(cs, &sym_is_self_evaluating, not_dummy, &env_not_nil)?;

    {
        // implies_equal_t!(cs, &cond1, &output_expr, &expr);
        // implies_equal_t!(cs, &cond1, &output_env, &env);
        // implies_equal_t!(cs, &cond1, &output_cont, &cont);
    }

    let cs = &mut cs.namespace(|| "otherwise_and_binding_is_nil");
    let cond2 = otherwise_and_binding_is_nil;
    {
        // let cond = and!(cs, &otherwise_and_binding_is_nil, not_dummy)?;

        // implies_equal_t!(cs, &cond2, &output_expr, &expr);
        // implies_equal_t!(cs, &cond2, &output_env, &env);
        implies_equal_t!(cs, &cond2, output_cont, g.error_ptr);
    }
    let cs = &mut cs.namespace(|| "v_is_expr1_real");

    let cond3 = v_is_expr1_real;
    {
        implies_equal_t!(cs, &cond3, output_expr, val);
        // implies_equal_t!(cs, &cond3, &output_env, &env);
        // implies_equal_t!(cs, &cond3, &output_cont, &cont);
    }
    let cs = &mut cs.namespace(|| "cont_is_lookup_sym");
    let cond4 = cont_is_lookup_sym;
    {
        // implies_equal_t!(cs, &cond4, &output_expr, &expr);
        implies_equal_t!(cs, &cond4, output_env, smaller_env);

        //implies_equal_t!(cs, &cond, &output_cont, &cont);
    }
    let cs = &mut cs.namespace(|| "cont_not_lookup_sym");
    let cond5 = and!(cs, &cont_not_lookup_sym, &otherwise)?;

    {
        // implies_equal_t!(cs, &cond5, &output_expr, &expr);
        implies_equal_t!(cs, &cond5, output_env, smaller_env);
        // implies_equal_t!(cs, &cond5, output_cont, lookup_continuation);
    }

    let cs = &mut cs.namespace(|| "v2_is_expr_real");
    let cond6 = v2_is_expr_real;
    {
        implies_equal_t!(cs, &cond6, output_expr, val_to_use);
        // implies_equal_t!(cs, &cond6, &output_env, &env);
        // implies_equal_t!(cs, &cond6, &output_cont, &cont);
    }

    let cs = &mut cs.namespace(|| "otherwise_and_v2_not_expr");
    let cond7 = otherwise_and_v2_not_expr;
    {
        // implies_equal_t!(cs, &cond7, &output_expr, &expr);
        implies_equal_t!(cs, &cond7, output_env, env_to_use);
    }

    let cs = &mut cs.namespace(|| "cont_is_lookup_cons");
    let cond8 = cont_is_lookup_cons;
    // {
    //     // implies_equal_t!(cs, &cond8, &output_cont, &cont);
    // }

    let cs = &mut cs.namespace(|| "cont_not_lookup_cons");
    let cond9 = and!(cs, &cont_not_lookup_cons, &otherwise)?;
    {
        // implies_equal_t!(cs, &cond9, output_cont, lookup_continuation);
    }

    let cs = &mut cs.namespace(|| "otherwise_neither");
    let cond10 = otherwise_neither;
    {
        // "Bad form"
        implies_equal_t!(cs, &cond10, output_cont, g.error_ptr);
    }

    let lookup_continuation_not_dummy = or!(cs, &cond5, &cond9)?;

    let lookup_continuation = AllocatedContPtr::construct_named(
        &mut cs.namespace(|| "lookup_continuation"),
        ContName::Lookup,
        &g.lookup_cont_tag,
        // Mirrors Continuation::get_hash_components()
        &[
            env,
            cont,
            &[&g.default_num, &g.default_num],
            &[&g.default_num, &g.default_num],
        ],
        allocated_cont_witness,
        &lookup_continuation_not_dummy,
    )?;

    implies_equal_t!(
        cs,
        &lookup_continuation_not_dummy,
        output_cont,
        lookup_continuation
    );

    let conda = or!(cs, &cond1, &sym_is_self_evaluating)?; // cond1, cond2, sym_is_self_evaluating,
    let condb = or!(cs, &cond4, &cond6)?; // cond4, cond6
    let condc = or!(cs, &conda, &cond8)?; // cond1, cond2, cond8, sym_is_self_evaluating

    let condw = or!(cs, &cond0, &cond2)?; // cond0, cond2
    let condx = or!(cs, &cond5, &cond4, &condw)?; // cond0, cond2, cond4, cond5
    let condy = or!(cs, &cond3, &cond6, &condw)?; // cond0, cond2, cond3, cond6

    // cond1, cond2, cond4, cond5 // cond_expr
    let cond_expr = or!(cs, &conda, &condx, &cond7, &cond10)?; // cond0, cond1, cond2, cond4, cond5, sym_is_self_evaluating
    implies_equal_t!(cs, &cond_expr, output_expr, expr);

    // cond1, cond2, cond3, cond6 // cond_env
    let cond_env = or!(cs, &conda, &condy)?; // cond0, cond1, cond2, cond3, cond6, sym_is_self_evaluating
    implies_equal_t!(cs, &cond_env, output_env, env);

    // cond1, cond3, cond4, cond6, cond // cond_cont
    let cond_cont = or!(cs, &condb, &condc, &cond3)?; // cond1, cond2, cond4, cond6, cond8, sym_is_self_evaluating
    implies_equal_t!(cs, &cond_cont, output_cont, cont);

    // Debugging
    //
    // let output_expr_is_constrained = or!(cs, &cond_expr, &cond3, &cond6, &not_dummy.not())?;
    // if !output_expr_is_constrained.get_value().unwrap_or(true) {
    //     panic!("output_expr is mistakenly unconstrained.");
    // }
    // let output_env_is_constrained = or!(cs, &cond_env, &cond4, &cond5, &cond7, &not_dummy.not())?;
    // if !output_env_is_constrained.get_value().unwrap_or(true) {
    //     panic!("output_env is mistakenly unconstrained.");
    // }
    // let output_cont_is_constrained = or!(
    //     cs,
    //     &cond_cont,
    //     &cond0,
    //     &cond1,
    //     &cond2,
    //     &cond10,
    //     &lookup_continuation_not_dummy,
    //     &not_dummy.not()
    // )?;
    // if !output_cont_is_constrained.get_value().unwrap_or(true) {
    //     panic!("output_cont is mistakenly unconstrained.");
    // }

    Ok((output_expr, output_env, output_cont, apply_cont_num))
}

fn reduce_cons<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    expr: &AllocatedPtr<F>,
    env: &AllocatedPtr<F>,
    cont: &AllocatedContPtr<F>,
    not_dummy: &Boolean,
    _witness: &Option<Witness<F>>,
    allocated_cons_witness: &mut AllocatedConsWitness<F>,
    allocated_cont_witness: &mut AllocatedContWitness<F>,
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

    let hash_sym = |name: &str| {
        store
            .get_lurk_sym(name, true)
            .and_then(|s| store.hash_sym(s, HashScalar::Get))
            .unwrap()
    };

    let lambda_hash = hash_sym("lambda");
    let quote_hash = hash_sym("quote");
    let let_sym = hash_sym("let");
    let let_hash = let_sym.value();
    let letrec = hash_sym("letrec");
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

    let (head, rest) = car_cdr_named(
        &mut cs.namespace(|| "reduce_cons expr"),
        g,
        expr,
        ConsName::Expr,
        allocated_cons_witness,
        not_dummy,
        store,
    )?;

    macro_rules! def_head_sym {
        ($var:ident, $field:ident) => {
            let $var = head.alloc_equal(&mut cs.namespace(|| stringify!($var)), &g.$field)?;
        };
    }

    // TODO: This currently incurs a lot of extra constraints:
    // - global constant allocation for each symbol
    // - the boolean equality allocation for each symbol checked against head
    // - one constraint for each member of the or!
    //
    // Possible optimizations:
    // - The variadic or! (and and!) can be optimized to a single constraint.
    // - We can optimize the alloc_equals to use the constant sym.
    // - We only need to check the tag once, so can just check value/hash equality.
    def_head_sym!(head_is_lambda, lambda_sym);
    def_head_sym!(head_is_let, let_sym);
    def_head_sym!(head_is_letrec, letrec_sym);
    def_head_sym!(head_is_eval, eval_sym);
    def_head_sym!(head_is_quote, quote_sym);

    def_head_sym!(head_is_cons, cons_sym);
    def_head_sym!(head_is_strcons, strcons_sym);
    def_head_sym!(head_is_hide, hide_sym);
    def_head_sym!(head_is_commit, commit_sym);
    def_head_sym!(head_is_open, open_sym);
    def_head_sym!(head_is_secret, secret_sym);
    def_head_sym!(head_is_num, num_sym);
    def_head_sym!(head_is_comm, comm_sym);
    def_head_sym!(head_is_char, char_sym);
    def_head_sym!(head_is_begin, begin_sym);
    def_head_sym!(head_is_car, car_sym);
    def_head_sym!(head_is_cdr, cdr_sym);
    def_head_sym!(head_is_atom, atom_sym);
    def_head_sym!(head_is_emit, emit_sym);
    def_head_sym!(head_is_plus, plus_sym);
    def_head_sym!(head_is_minus, minus_sym);
    def_head_sym!(head_is_times, times_sym);
    def_head_sym!(head_is_div, div_sym);
    def_head_sym!(head_is_equal, equal_sym);
    def_head_sym!(head_is_eq, eq_sym);
    def_head_sym!(head_is_less, less_sym);
    def_head_sym!(head_is_less_equal, less_equal_sym);
    def_head_sym!(head_is_greater, greater_sym);
    def_head_sym!(head_is_greater_equal, greater_equal_sym);
    def_head_sym!(head_is_if, if_sym);
    def_head_sym!(head_is_current_env, current_env_sym);

    let head_is_binop = or!(
        cs,
        &head_is_cons,
        &head_is_strcons,
        &head_is_hide,
        &head_is_begin,
        &head_is_plus,
        &head_is_minus,
        &head_is_times,
        &head_is_div,
        //&head_is_mod, // uncomment when supported
        &head_is_equal,
        &head_is_eq,
        &head_is_less,
        &head_is_less_equal,
        &head_is_greater,
        &head_is_greater_equal,
        &head_is_if,
        &head_is_eval
    )?;
    let head_is_unop = or!(
        cs,
        &head_is_car,
        &head_is_cdr,
        &head_is_commit,
        &head_is_num,
        //&head_is_u64, // uncomment when supported
        &head_is_comm,
        &head_is_char,
        &head_is_open,
        &head_is_secret,
        &head_is_atom,
        &head_is_emit,
        &head_is_eval
    )?;
    let head_is_let_or_letrec = or!(cs, &head_is_let, &head_is_letrec)?;

    let head_is_any = or!(
        cs,
        &head_is_quote,
        &head_is_lambda,
        &head_is_current_env,
        &head_is_let_or_letrec,
        &head_is_unop,
        &head_is_binop
    )?;

    let rest_is_nil = rest.alloc_equal(&mut cs.namespace(|| "rest_is_nil"), &g.nil_ptr)?;

    let expr_cdr_not_dummy = and!(
        cs,
        not_dummy,
        &Boolean::not(&rest_is_nil),
        &head_is_any,
        &Boolean::not(&head_is_current_env) // current-env is unary.
    )?;

    let (arg1, more) = car_cdr_named(
        &mut cs.namespace(|| "car_cdr(rest)"),
        g,
        &rest,
        ConsName::ExprCdr,
        allocated_cons_witness,
        &expr_cdr_not_dummy,
        store,
    )?;

    let more_is_nil = more.alloc_equal(&mut cs.namespace(|| "more_is_nil"), &g.nil_ptr)?;

    let arg1_is_cons = alloc_equal(
        &mut cs.namespace(|| "arg1_is_cons"),
        arg1.tag(),
        &g.cons_tag,
    )?;
    let arg1_is_str = alloc_equal(&mut cs.namespace(|| "arg1_is_str"), arg1.tag(), &g.str_tag)?;

    let arg1_is_nil = arg1.alloc_equal(&mut cs.namespace(|| "arg1_is_nil"), &g.nil_ptr)?;
    let expr_cadr_not_dummy0 = or!(cs, &arg1_is_cons, &arg1_is_nil, &arg1_is_str)?;
    let expr_cadr_not_dummy = and!(
        cs,
        &expr_cdr_not_dummy,
        &expr_cadr_not_dummy0,
        &head_is_lambda
    )?;

    let (car_args, cdr_args) = car_cdr_named(
        &mut cs.namespace(|| "car_cdr(arg1)"),
        g,
        &arg1,
        ConsName::ExprCadr,
        allocated_cons_witness,
        &expr_cadr_not_dummy,
        store,
    )?;

    let end_is_nil = more.alloc_equal(&mut cs.namespace(|| "end_is_nil"), &g.nil_ptr)?;

    let mut results = Results::default();

    // --
    let function = {
        // head == LAMBDA
        // body == more == (cdr expr)
        let (args, body) = (arg1.clone(), more.clone());
        let args_is_nil = args.alloc_equal(&mut cs.namespace(|| "args_is_nil"), &g.nil_ptr)?;

        let cdr_args_is_nil =
            cdr_args.alloc_equal(&mut cs.namespace(|| "cdr_args_is_nil"), &g.nil_ptr)?;

        let cdr_args_not_nil = Boolean::not(&cdr_args_is_nil);

        let lambda_not_dummy = and!(cs, &head_is_lambda, not_dummy, &cdr_args_not_nil)?;

        let arg = AllocatedPtr::pick(
            &mut cs.namespace(|| "maybe dummy arg"),
            &args_is_nil,
            &g.dummy_arg_ptr,
            &car_args,
        )?;

        let inner = AllocatedPtr::construct_cons_named(
            &mut cs.namespace(|| "inner"),
            g,
            &cdr_args,
            &body,
            ConsName::InnerLambda,
            allocated_cons_witness,
            &lambda_not_dummy,
        )?;

        let l = AllocatedPtr::construct_cons_named(
            &mut cs.namespace(|| "l"),
            g,
            &g.lambda_sym,
            &inner,
            ConsName::Lambda,
            allocated_cons_witness,
            &lambda_not_dummy,
        )?;

        let list = AllocatedPtr::construct_cons_named(
            &mut cs.namespace(|| "list"),
            g,
            &l,
            &g.nil_ptr,
            ConsName::InnerBody,
            allocated_cons_witness,
            &lambda_not_dummy,
        )?;
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

    ////////////////////////////////////////////////////////////////////////////////

    let let_letrec_not_dummy = Boolean::and(
        &mut cs.namespace(|| "let_letrec_not_dummy"),
        not_dummy,
        &head_is_let_or_letrec,
    )?;

    let (bindings, body) = (arg1.clone(), more.clone());
    let (body1, rest_body) = car_cdr_named(
        &mut cs.namespace(|| "car_cdr body"),
        g,
        &body,
        ConsName::ExprCddr,
        allocated_cons_witness,
        &let_letrec_not_dummy,
        store,
    )?;
    let bindings_is_nil =
        bindings.alloc_equal(&mut cs.namespace(|| "bindings_is_nil"), &g.nil_ptr)?;

    let bindings_is_cons = alloc_equal(
        &mut cs.namespace(|| "bindings_is_cons"),
        bindings.tag(),
        &g.cons_tag,
    )?;

    let body_is_nil = body.alloc_equal(&mut cs.namespace(|| "body_is_nil"), &g.nil_ptr)?;

    let rest_body_is_nil =
        rest_body.alloc_equal(&mut cs.namespace(|| "rest_body_is_nil"), &g.nil_ptr)?;

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

        let mut cs = cs.namespace(|| "LET_LETREC");

        let expr_caadr_not_dummy = and!(
            cs,
            &rest_body_is_nil,
            &body_is_nil.not(),
            &bindings_is_cons,
            &bindings_is_nil.not(),
            &let_letrec_not_dummy
        )?;

        let (binding1, rest_bindings) = (car_args, cdr_args);

        let (var_let_letrec, vals) = car_cdr_named(
            &mut cs.namespace(|| "car_cdr binding1"),
            g,
            &binding1,
            ConsName::ExprCaadr,
            allocated_cons_witness,
            &expr_caadr_not_dummy,
            store,
        )?;

        let (val, end) = car_cdr_named(
            &mut cs.namespace(|| "car_cdr vals"),
            g,
            &vals,
            ConsName::ExprCaaadr,
            allocated_cons_witness,
            &expr_caadr_not_dummy,
            store,
        )?;

        let end_is_nil = end.alloc_equal(&mut cs.namespace(|| "end_is_nil"), &g.nil_ptr)?;

        /*
         * We get the condition for error by using OR of each individual error.
         */
        let mut cond_error = constraints::or(
            &mut cs.namespace(|| "cond error1"),
            &Boolean::not(&rest_body_is_nil),
            &Boolean::not(&end_is_nil),
        )?;

        cond_error = constraints::or(
            &mut cs.namespace(|| "cond error2"),
            &body_is_nil,
            &cond_error,
        )?;

        let rest_bindings_is_nil =
            rest_bindings.alloc_equal(&mut cs.namespace(|| "rest_bindings_is_nil"), &g.nil_ptr)?;

        let expanded_inner_not_dummy0 =
            and!(cs, &Boolean::not(&rest_bindings_is_nil), &end_is_nil)?;

        let expanded_inner_not_dummy = and!(
            cs,
            &expanded_inner_not_dummy0,
            &let_letrec_not_dummy,
            &Boolean::not(&body_is_nil),
            &rest_body_is_nil
        )?;

        let expanded0 = AllocatedPtr::construct_cons_named(
            &mut cs.namespace(|| "expanded0"),
            g,
            &rest_bindings,
            &body,
            ConsName::ExpandedInner,
            allocated_cons_witness,
            &expanded_inner_not_dummy,
        )?;

        let expanded1 = AllocatedPtr::construct_cons_named(
            &mut cs.namespace(|| "expanded1"),
            g,
            &head,
            &expanded0,
            ConsName::Expanded,
            allocated_cons_witness,
            &expanded_inner_not_dummy,
        )?;

        let expanded = AllocatedPtr::pick(
            &mut cs.namespace(|| "expanded"),
            &rest_bindings_is_nil,
            &body1,
            &expanded1,
        )?;

        let output_expr = AllocatedPtr::pick(
            &mut cs.namespace(|| "pick body1 or val"),
            &bindings_is_nil,
            &body1,
            &val,
        )?;

        let the_expr = AllocatedPtr::pick(
            &mut cs.namespace(|| "the_expr_let"),
            &cond_error,
            expr,
            &output_expr,
        )?;

        (
            the_expr,
            var_let_letrec,
            expanded.clone(),
            expanded,
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
        // The following series of pick operations construct a preimage depending on whether one or more arguments were
        // provided to eval.
        //
        // If end_is_nil, then only one argument was provided, and the preimage is:
        // [unop_cont_tag, op1_eval_tag, cont.tag(), cont.hash(), g.default_num, g.default_num, g.default_num, g.default_num]
        //
        // Otherwise, more than one argument was provided (FIXME: error-checking to ensure exactly two were provided?):
        // [binop_cont_tag, g.op2_eval_tag, env.tag(), env.hash(), more.tag(), more.hash(), cont.tag(), cont.hash()]

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
        let cont_or_env_tag = pick(
            &mut cs.namespace(|| "env or cont tag"),
            &end_is_nil,
            cont.tag(),
            env.tag(),
        )?;
        let cont_or_env_hash = pick(
            &mut cs.namespace(|| "env or cont hash"),
            &end_is_nil,
            cont.hash(),
            env.hash(),
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
            cont_or_env_tag,
            cont_or_env_hash,
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

    let unop_condition = and!(cs, &rest_is_nil.not(), &end_is_nil)?;
    let binop_condition = and!(cs, &end_is_nil.not(), &more_is_nil.not())?;

    let newer_cont_unop = and!(cs, &head_is_unop, &unop_condition)?;
    let newer_cont_binop = and!(cs, &head_is_binop, &binop_condition)?;

    let newer_cont_let_letrec = and!(
        cs,
        &head_is_let_or_letrec,
        &rest_body_is_nil,
        &body_is_nil.not(),
        &bindings_is_nil.not(),
        &end_is_nil
    )?;

    let newer_cont_not_dummy0 = or!(
        cs,
        &newer_cont_binop,
        &newer_cont_unop,
        &newer_cont_let_letrec
    )?;
    let newer_cont_not_dummy = and!(cs, &newer_cont_not_dummy0, not_dummy)?;

    let newer_cont = AllocatedContPtr::construct_named(
        &mut cs.namespace(|| "reduce cons newer_cont construction from hash components"),
        ContName::NewerCont,
        &components_results[0], // continuation tag
        &[
            &[&components_results[1], &components_results[2]] as &dyn AsAllocatedHashComponents<F>,
            &[&components_results[3], &components_results[4]] as &dyn AsAllocatedHashComponents<F>,
            &[&components_results[5], &components_results[6]] as &dyn AsAllocatedHashComponents<F>,
            &[&components_results[7], &components_results[8]] as &dyn AsAllocatedHashComponents<F>,
        ],
        allocated_cont_witness,
        &newer_cont_not_dummy,
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
    let the_cont_open_or_secret = &newer_cont_if_end_is_nil;

    results.add_clauses_cons(
        *open_hash.value(),
        &arg1_or_expr,
        env,
        the_cont_open_or_secret,
        &g.false_num,
    );

    // head == SECRET, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////

    results.add_clauses_cons(
        *secret_hash.value(),
        &arg1_or_expr,
        env,
        the_cont_open_or_secret,
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

        let more_args_is_nil =
            more.alloc_equal(&mut cs.namespace(|| "more_args_is_nil"), &g.nil_ptr)?;
        let args_is_nil_or_more_is_nil = constraints::or(
            &mut cs.namespace(|| "args is nil or more is nil"),
            &rest_is_nil,
            &more_args_is_nil,
        )?;

        // NOTE: not_dummy was moved last to avoid namespace conflicts. Until automatic-namespacing of and! and or! get
        // smarter, put shared elements last and unique ones first.
        let fn_not_dummy = and!(
            cs,
            &Boolean::not(&args_is_nil_or_more_is_nil),
            &Boolean::not(&head_is_any),
            not_dummy
        )?;

        let expanded_inner0 = AllocatedPtr::construct_cons_named(
            &mut cs.namespace(|| "expanded_inner0"),
            g,
            &arg1,
            &g.nil_ptr,
            ConsName::ExpandedInner0,
            allocated_cons_witness,
            &fn_not_dummy,
        )?;

        let expanded_inner = AllocatedPtr::construct_cons_named(
            &mut cs.namespace(|| "expanded_inner"),
            g,
            fun_form,
            &expanded_inner0,
            ConsName::ExpandedInner,
            allocated_cons_witness,
            &fn_not_dummy,
        )?;

        let expanded = AllocatedPtr::construct_cons_named(
            &mut cs.namespace(|| "expanded"),
            g,
            &expanded_inner,
            &more,
            ConsName::FunExpanded,
            allocated_cons_witness,
            &fn_not_dummy,
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
    allocated_cont_witness: &mut AllocatedContWitness<F>,
    store: &Store<F>,
    g: &GlobalAllocations<F>,
) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
    let mut results = Results::default();

    let cont_is_tail = alloc_equal(
        &mut cs.namespace(|| "cont_is_tail"),
        cont.tag(),
        &g.tail_cont_tag,
    )?;

    let make_thunk_cont_not_dummy = and!(cs, &cont_is_tail, not_dummy)?;

    let (_, cont_components) = get_named_components(
        &mut cs.namespace(|| "cont components"),
        cont,
        ContName::MakeThunk,
        allocated_cont_witness,
        &make_thunk_cont_not_dummy,
        store,
    )?;

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
    allocated_cons_witness: &mut AllocatedConsWitness<F>,
    allocated_cont_witness: &mut AllocatedContWitness<F>,
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
        &g.false_num,
    );
    results.add_clauses_cont(
        ContTag::Terminal,
        result,
        env,
        &g.terminal_ptr,
        &g.false_num,
        &g.false_num,
    );
    results.add_clauses_cont(
        ContTag::Error,
        result,
        env,
        &g.error_ptr_cont,
        &g.false_num,
        &g.false_num,
    );

    let cont_is_terminal = equal!(cs, cont.tag(), g.terminal_ptr.tag())?;
    let cont_is_dummy = equal!(cs, cont.tag(), g.dummy_ptr.tag())?;
    let cont_is_error = equal!(cs, cont.tag(), g.error_ptr.tag())?;
    let cont_is_outermost = equal!(cs, cont.tag(), g.outermost_ptr.tag())?;
    let cont_is_trivial = or!(
        cs,
        &cont_is_terminal,
        &cont_is_dummy,
        &cont_is_error,
        &cont_is_outermost
    )?;

    let apply_continuation_components_not_dummy = and!(cs, &cont_is_trivial.not(), not_dummy)?;
    let (_continuation_tag, continuation_components) = get_named_components(
        &mut cs.namespace(|| "allocate_continuation_components"),
        cont,
        ContName::ApplyContinuation,
        allocated_cont_witness,
        &apply_continuation_components_not_dummy,
        store,
    )?;

    let continuation = AllocatedContPtr::by_index(0, &continuation_components);

    results.add_clauses_cont(
        ContTag::Emit,
        result,
        env,
        &continuation,
        &g.true_num,
        &g.false_num,
    );

    let default_num_pair = &[&g.default_num, &g.default_num];

    // Next we add multicase clauses for each continuation that requires a newer
    // cont, which means it needs to constrain a new hash, which is expensive,
    // then we do it only once.
    /////////////////////////////////////////////////////////////////////////////

    // Continuation::Call0 preimage
    /////////////////////////////////////////////////////////////////////////////
    let (saved_env, continuation) = {
        (
            AllocatedPtr::by_index(0, &continuation_components),
            AllocatedContPtr::by_index(1, &continuation_components),
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

    // Commitment values used in Unop but also outside, so can't be in Unop scope.
    let (commitment, commitment_secret, committed_expr) = {
        let operator = AllocatedPtr::by_index(0, &continuation_components);

        let is_op2_hide = equal!(cs, &g.op2_hide_tag, operator.tag())?;

        let is_op1_open = equal!(cs, &g.op1_open_tag, operator.tag())?;
        let is_op1_secret = equal!(cs, &g.op1_secret_tag, operator.tag())?;
        let is_op1_open_or_secret = or!(cs, &is_op1_open, &is_op1_secret)?;

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

        let commit_secret = pick!(cs, &is_op2_hide, arg1.hash(), &g.default_num)?;
        let secret = pick!(cs, &is_op1_open_or_secret, &open_secret, &commit_secret)?;
        let committed = pick_ptr!(cs, &is_op1_open, &open_expr, result)?;

        (
            hide(&mut cs.namespace(|| "Hide"), g, &secret, &committed, store)?,
            secret,
            committed,
        )
    };

    // Continuation::Unop preimage
    /////////////////////////////////////////////////////////////////////////////
    let (unop_val, unop_continuation) = {
        let op1 = AllocatedPtr::by_index(0, &continuation_components);
        let unop_continuation = AllocatedContPtr::by_index(1, &continuation_components);

        let cont_is_unop = equal!(cs, cont.tag(), &g.unop_cont_tag)?;

        let unop_op_is_car = equal!(cs, op1.tag(), &g.op1_car_tag)?;
        let unop_op_is_cdr = equal!(cs, op1.tag(), &g.op1_cdr_tag)?;
        let unop_op_is_car_or_cdr = or!(cs, &unop_op_is_car, &unop_op_is_cdr)?;

        let result_is_cons = alloc_equal(
            &mut cs.namespace(|| "result_is_cons"),
            result.tag(),
            &g.cons_tag,
        )?;
        let result_is_str = alloc_equal(
            &mut cs.namespace(|| "result_is_str"),
            result.tag(),
            &g.str_tag,
        )?;

        let result_is_empty_str = result.alloc_equal(
            &mut cs.namespace(|| "result_is_empty_str"),
            &g.empty_str_ptr,
        )?;
        let result_is_cons_like = or!(cs, &result_is_cons, &result_is_str)?;

        let unop_cons_not_dummy = and!(
            cs,
            &cont_is_unop,
            &unop_op_is_car_or_cdr,
            &result_is_cons_like,
            &Boolean::not(&result_is_empty_str)
        )?;

        let (allocated_car, allocated_cdr) = car_cdr_named(
            &mut cs.namespace(|| "Unop cons"),
            g,
            result,
            ConsName::UnopConsLike,
            allocated_cons_witness,
            &unop_cons_not_dummy,
            store,
        )?;

        let res_car = pick_ptr!(cs, &result_is_empty_str, &g.nil_ptr, &allocated_car)?;
        let res_cdr = pick_ptr!(cs, &result_is_empty_str, &g.empty_str_ptr, &allocated_cdr)?;

        let atom_ptr = AllocatedPtr::pick(
            &mut cs.namespace(|| "atom val"),
            &result_is_cons,
            &g.nil_ptr,
            &g.t_ptr,
        )?;

        let num = to_num(result, g);
        let comm = to_comm(result, g);
        let c = to_char(result, g);

        let res = multi_case(
            &mut cs.namespace(|| "Unop case"),
            op1.tag(),
            &[
                &[
                    CaseClause {
                        key: Op1::Car.as_field(),
                        value: res_car.tag(),
                    },
                    CaseClause {
                        key: Op1::Cdr.as_field(),
                        value: res_cdr.tag(),
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
    let (newer_cont2, newer_cont2_not_dummy_num) = AllocatedContPtr::construct_named_and_not_dummy(
        &mut cs.namespace(|| "construct newer_cont2 from hash components"),
        ContName::NewerCont2,
        &components_results[0], // continuation tag
        &[
            &[&components_results[1], &components_results[2]] as &dyn AsAllocatedHashComponents<F>,
            &[&components_results[3], &components_results[4]] as &dyn AsAllocatedHashComponents<F>,
            &[&components_results[5], &components_results[6]] as &dyn AsAllocatedHashComponents<F>,
            &[&g.default_num, &g.default_num],
        ],
        allocated_cont_witness,
    )?;

    // Continuation::Call0
    /////////////////////////////////////////////////////////////////////////////
    let (the_expr, the_env, the_cont, newer_cont2_not_dummy) = {
        let mut cs = cs.namespace(|| "Call0");
        let continuation = AllocatedContPtr::by_index(1, &continuation_components);

        let cont_is_call0 = equal!(cs, cont.tag(), &g.call0_cont_tag)?;
        let result_is_fun = equal!(cs, function.tag(), &g.fun_tag)?;
        let call0_not_dummy = and!(cs, &cont_is_call0, &result_is_fun, not_dummy)?;

        // NOTE: this allocation is unconstrained. See necessary constraint immediately below.
        let (fun_hash, arg_t, body_t, closed_env) = Ptr::allocate_maybe_fun_unconstrained(
            &mut cs.namespace(|| "allocate fun"),
            store,
            result.ptr(store).as_ref(),
        )?;

        // Without this, fun is unconstrained.
        implies_equal!(cs, &call0_not_dummy, &fun_hash, result.hash());

        let args_is_dummy =
            arg_t.alloc_equal(&mut cs.namespace(|| "args_is_dummy"), &g.dummy_arg_ptr)?;

        let body_t_is_cons = alloc_equal(
            &mut cs.namespace(|| "body_t_is_cons0"),
            body_t.tag(),
            &g.cons_tag,
        )?;

        let zero_arg_call_not_dummy = and!(cs, &call0_not_dummy, &body_t_is_cons, &args_is_dummy)?;

        let (body_form, _) = car_cdr_named(
            &mut cs.namespace(|| "body_form"),
            g,
            &body_t,
            ConsName::FunBody,
            allocated_cons_witness,
            &zero_arg_call_not_dummy,
            store,
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
            &newer_cont2,
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

        let newer_cont2_not_dummy0 = and!(
            cs,
            &continuation_is_tail.not(),
            &args_is_dummy,
            &result_is_fun
        )?;
        let newer_cont2_not_dummy = boolean_num!(cs, &newer_cont2_not_dummy0)?;

        (the_expr, the_env, the_cont, newer_cont2_not_dummy)
    };

    results.add_clauses_cont(
        ContTag::Call0,
        &the_expr,
        &the_env,
        &the_cont,
        &g.false_num,
        &newer_cont2_not_dummy,
    );

    // Continuation::Call, newer_cont2 is allocated
    /////////////////////////////////////////////////////////////////////////////
    let (next_expr, the_cont, newer_cont2_not_dummy) = {
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
            &newer_cont2,
            &g.error_ptr_cont,
        )?;

        let newer_cont2_not_dummy = boolean_num!(cs, &result_is_fun)?;

        (next_expr, the_cont, newer_cont2_not_dummy)
    };
    results.add_clauses_cont(
        ContTag::Call,
        &next_expr,
        env,
        &the_cont,
        &g.false_num,
        &newer_cont2_not_dummy,
    );

    // Continuation::Call2, newer_cont2 is allocated
    /////////////////////////////////////////////////////////////////////////////
    let (the_expr, the_env, the_cont, newer_cont2_not_dummy) = {
        let mut cs = cs.namespace(|| "Call2");
        let fun = AllocatedPtr::by_index(1, &continuation_components);
        let continuation = AllocatedContPtr::by_index(2, &continuation_components);

        {
            let cont_is_call2_precomp = equal!(cs, cont.tag(), &g.call2_cont_tag)?;
            let cont_is_call2_and_not_dummy = and!(cs, &cont_is_call2_precomp, not_dummy)?;

            // NOTE: this allocation is unconstrained. See necessary constraint immediately below.
            let (hash, arg_t, body_t, closed_env) = Ptr::allocate_maybe_fun_unconstrained(
                &mut cs.namespace(|| "allocate fun"),
                store,
                fun.ptr(store).as_ref(),
            )?;

            // Without this, fun is unconstrained.
            implies_equal!(cs, &cont_is_call2_and_not_dummy, fun.hash(), &hash);

            let args_is_dummy = arg_t.alloc_equal(
                &mut cs.namespace(|| "cont2 args_is_dummy"),
                &g.dummy_arg_ptr,
            )?;
            let args_is_not_dummy = Boolean::not(&args_is_dummy);

            let cont_is_call2_and_not_dummy_and_not_dummy_args =
                and!(cs, &cont_is_call2_and_not_dummy, &args_is_not_dummy)?;

            let (body_form, _) = car_cdr_named(
                &mut cs.namespace(|| "body_form"),
                g,
                &body_t,
                ConsName::FunBody,
                allocated_cons_witness,
                &cont_is_call2_and_not_dummy_and_not_dummy_args,
                store,
            )?;

            let args_is_dummy =
                arg_t.alloc_equal(&mut cs.namespace(|| "args_is_dummy"), &g.dummy_arg_ptr)?;

            let extend_not_dummy = and!(
                cs,
                &cont_is_call2_and_not_dummy,
                &Boolean::not(&args_is_dummy)
            )?;

            let newer_env = extend_named(
                &mut cs.namespace(|| "extend env"),
                g,
                &closed_env,
                &arg_t,
                result,
                ConsName::ClosedEnv,
                allocated_cons_witness,
                &extend_not_dummy,
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
                &newer_cont2,
            );

            let result_is_fun =
                alloc_equal(cs.namespace(|| "result_is_fun"), result.tag(), &g.fun_tag)?;
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

            let newer_cont2_not_dummy0 = and!(cs, &continuation_is_tail.not(), &cond)?;
            let newer_cont2_not_dummy = boolean_num!(cs, &newer_cont2_not_dummy0)?;

            (the_expr, the_env, the_cont, newer_cont2_not_dummy)
        }
    };
    results.add_clauses_cont(
        ContTag::Call2,
        &the_expr,
        &the_env,
        &the_cont,
        &g.false_num,
        &newer_cont2_not_dummy,
    );

    // Continuation::Binop, newer_cont2 is allocated
    /////////////////////////////////////////////////////////////////////////////
    let (the_expr, the_env, the_cont, newer_cont2_not_dummy) = {
        let mut cs = cs.namespace(|| "Binop");
        let operator = AllocatedPtr::by_index(0, &continuation_components);
        let saved_env = AllocatedPtr::by_index(1, &continuation_components);
        let unevaled_args = AllocatedPtr::by_index(2, &continuation_components);

        let cont_is_binop = alloc_equal(
            &mut cs.namespace(|| "cont_is_binop"),
            cont.tag(),
            &g.binop_cont_tag,
        )?;

        let binop_not_dummy = Boolean::and(
            &mut cs.namespace(|| "binop_not_dummy"),
            &cont_is_binop,
            not_dummy,
        )?;

        let (allocated_arg2, allocated_rest) = car_cdr_named(
            &mut cs.namespace(|| "cons using newer continuation"),
            g,
            &unevaled_args,
            ConsName::UnevaledArgs,
            allocated_cons_witness,
            &binop_not_dummy,
            store,
        )?;

        let op_is_begin = alloc_equal(
            cs.namespace(|| "op_is_begin"),
            operator.tag(),
            &g.op2_begin_tag,
        )?;

        let rest_is_nil =
            allocated_rest.alloc_equal(&mut cs.namespace(|| "rest_is_nil"), &g.nil_ptr)?;
        let rest_not_nil = Boolean::not(&rest_is_nil);

        let begin = store.get_begin();

        let allocated_begin =
            AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "begin"), store, || Ok(&begin))?;

        let begin_not_dummy = and!(cs, &op_is_begin, &binop_not_dummy, &rest_not_nil)?;
        let begin_again = AllocatedPtr::construct_cons_named(
            &mut cs.namespace(|| "begin again"),
            g,
            &allocated_begin,
            &unevaled_args,
            ConsName::Begin,
            allocated_cons_witness,
            &begin_not_dummy,
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
            &newer_cont2,
            &g.error_ptr_cont,
        )?;

        let the_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "the_cont"),
            &otherwise,
            &the_cont_otherwise,
            &continuation,
        )?;

        let newer_cont2_not_dummy = boolean_num!(cs, &otherwise_and_rest_is_nil)?;

        (the_expr, the_env, the_cont, newer_cont2_not_dummy)
    };
    results.add_clauses_cont(
        ContTag::Binop,
        &the_expr,
        &the_env,
        &the_cont,
        &g.false_num,
        &newer_cont2_not_dummy,
    );

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

        let is_cons_or_strcons = constraints::or(
            &mut cs.namespace(|| "is cons or strcons"),
            &is_cons,
            &is_strcons,
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

        let args_not_char_str = &Boolean::not(&args_are_char_str);
        let invalid_strcons_tag = Boolean::and(
            &mut cs.namespace(|| "invalid_strcons_tag"),
            args_not_char_str,
            &is_strcons,
        )?;

        let cons_not_dummy = and!(
            cs,
            &is_cons_or_strcons,
            &not_dummy,
            &Boolean::not(&invalid_strcons_tag)
        )?;

        let cons = AllocatedPtr::construct_cons_named(
            &mut cs.namespace(|| "cons"),
            g,
            &arg1,
            arg2,
            ConsName::TheCons,
            allocated_cons_witness,
            &cons_not_dummy,
        )?;

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

        let op2_is_hide = alloc_equal(
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
            &op2_is_hide,
            &commitment_tag_is_correct,
        )?;

        let cons_tag = pick(
            &mut cs.namespace(|| "cons_tag"),
            &is_strcons,
            &g.str_tag,
            &g.cons_tag,
        )?;

        let comm_or_num_tag = pick(
            &mut cs.namespace(|| "Op2 tag is comm or num"),
            &op2_is_hide,
            &g.comm_tag,
            &g.num_tag,
        )?;

        let is_cons_or_hide = or!(cs, &is_cons, &op2_is_hide)?;

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

        let op2_not_both_num_and_not_cons_or_strcons_or_hide_or_equal_or_num_equal = and!(
            cs,
            &Boolean::not(&both_args_are_nums),
            &Boolean::not(&is_cons_or_strcons_or_hide_or_equal_or_num_equal)
        )?;

        let op2_is_hide_and_arg1_is_not_num = and!(cs, &op2_is_hide, &arg1_is_num.not())?;

        let any_error = or!(
            cs,
            &Boolean::not(&valid_types_and_not_div_by_zero),
            &op2_not_both_num_and_not_cons_or_strcons_or_hide_or_equal_or_num_equal,
            &invalid_strcons_tag,
            &op2_is_hide_and_arg1_is_not_num
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
        &g.false_num,
    );

    // Continuation::If
    /////////////////////////////////////////////////////////////////////////////
    let (res, the_cont) = {
        let mut cs = cs.namespace(|| "If");
        let unevaled_args = AllocatedPtr::by_index(0, &continuation_components);
        let continuation = AllocatedContPtr::by_index(1, &continuation_components);

        let condition = result;

        let cont_is_if = alloc_equal(
            &mut cs.namespace(|| "cont_is_if"),
            cont.tag(),
            &g.if_cont_tag,
        )?;

        let if_not_dummy = and!(cs, &cont_is_if, not_dummy)?;

        let (arg1, more) = car_cdr_named(
            &mut cs.namespace(|| "unevaled_args cons"),
            g,
            &unevaled_args,
            ConsName::UnevaledArgs,
            allocated_cons_witness,
            &if_not_dummy,
            store,
        )?;

        let condition_is_nil =
            condition.alloc_equal(&mut cs.namespace(|| "condition is nil"), &g.nil_ptr)?;

        let (arg2, end) = car_cdr_named(
            &mut cs.namespace(|| "more cons"),
            g,
            &more,
            ConsName::UnevaledArgsCdr,
            allocated_cons_witness,
            &if_not_dummy,
            store,
        )?;

        let end_is_nil = end.alloc_equal(&mut cs.namespace(|| "end_is_nil"), &g.nil_ptr)?;

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

    results.add_clauses_cont(
        ContTag::If,
        &res,
        env,
        &the_cont,
        &g.false_num,
        &g.false_num,
    );

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
        &g.false_num,
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
        &g.false_num,
    );

    // Continuation::Let, newer_cont2 is allocated
    /////////////////////////////////////////////////////////////////////////////
    let (body, extended_env, tail_cont, newer_cont2_not_dummy) = {
        let mut cs = cs.namespace(|| "Let");
        let var = AllocatedPtr::by_index(0, &continuation_components);
        let body = AllocatedPtr::by_index(1, &continuation_components);
        let let_cont = AllocatedContPtr::by_index(3, &continuation_components);

        let cont_is_let = alloc_equal(
            &mut cs.namespace(|| "cont_is_let"),
            cont.tag(),
            &g.let_cont_tag,
        )?;
        let let_cont_is_let = alloc_equal(
            &mut cs.namespace(|| "let_cont_is_let"),
            let_cont.tag(),
            &g.let_cont_tag,
        )?;

        let extended_env_not_dummy0 = and!(cs, &let_cont_is_let, not_dummy)?;
        let extended_env_not_dummy = and!(cs, &extended_env_not_dummy0, &cont_is_let)?;

        let extended_env = extend_named(
            &mut cs.namespace(|| "extend env"),
            g,
            env,
            &var,
            result,
            ConsName::Env,
            allocated_cons_witness,
            &extended_env_not_dummy,
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
            &newer_cont2,
        );
        let newer_cont2_not_dummy = boolean_num!(cs, &continuation_is_tail.not())?;

        (body, extended_env, tail_cont, newer_cont2_not_dummy)
    };
    let let_cont = match tail_cont {
        Ok(c) => c,
        Err(_) => g.dummy_ptr.clone(),
    };
    results.add_clauses_cont(
        ContTag::Let,
        &body,
        &extended_env,
        &let_cont,
        &g.false_num,
        &newer_cont2_not_dummy,
    );

    // Continuation::LetRec, newer_cont2 is allocated
    /////////////////////////////////////////////////////////////////////////////
    let (body, extended_env, return_cont, newer_cont2_not_dummy) = {
        let mut cs = cs.namespace(|| "LetRec");
        let var = AllocatedPtr::by_index(0, &continuation_components);
        let body = AllocatedPtr::by_index(1, &continuation_components);
        let letrec_cont = AllocatedContPtr::by_index(3, &continuation_components);

        let letrec_cont_is_letrec_cont = alloc_equal(
            &mut cs.namespace(|| "letrec_cont_is_letrec_cont"),
            letrec_cont.tag(),
            &g.letrec_cont_tag,
        )?;

        let extend_rec_not_dummy = and!(cs, &letrec_cont_is_letrec_cont, not_dummy)?;

        let extended_env = extend_rec(
            &mut cs.namespace(|| "extend_rec env"),
            g,
            env,
            &var,
            result,
            allocated_cons_witness,
            &extend_rec_not_dummy,
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
            &newer_cont2,
        )?;

        let return_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "return_cont"),
            &is_error,
            &g.error_ptr_cont,
            &tail_cont,
        )?;

        let newer_cont2_not_dummy = boolean_num!(cs, &continuation_is_tail.not())?;
        (body, extended_env, return_cont, newer_cont2_not_dummy)
    };
    results.add_clauses_cont(
        ContTag::LetRec,
        &body,
        &extended_env,
        &return_cont,
        &g.false_num,
        &newer_cont2_not_dummy,
    );

    // Continuation::Unop newer_cont2 is allocated
    /////////////////////////////////////////////////////////////////////////////
    let (the_expr, the_env, the_cont, make_thunk_num, newer_cont2_not_dummy) = {
        let unop_op1 = AllocatedPtr::by_index(0, &continuation_components);
        let other_unop_continuation = AllocatedContPtr::by_index(1, &continuation_components);

        let op1_is_emit = equal!(cs, &g.op1_emit_tag, unop_op1.tag())?;
        let op1_is_eval = equal!(cs, &g.op1_eval_tag, unop_op1.tag())?;

        let unop_continuation0 = AllocatedContPtr::pick(
            &mut cs.namespace(|| "unop_continuation0"),
            &op1_is_emit,
            &newer_cont2,
            &other_unop_continuation,
        )?;

        let unop_continuation = AllocatedContPtr::pick(
            &mut cs.namespace(|| "unop_continuation"),
            &op1_is_eval,
            &continuation,
            &unop_continuation0,
        )?;

        let result_has_cons_tag = equal!(cs, &g.cons_tag, result.tag())?;
        let result_has_str_tag = equal!(cs, &g.str_tag, result.tag())?;

        let result_is_nil =
            result.alloc_equal(&mut cs.namespace(|| "result_is_nil"), &g.nil_ptr)?;

        let car_cdr_has_valid_tag = or!(
            cs,
            &result_has_cons_tag,
            &result_has_str_tag,
            &result_is_nil
        )?;

        let op1_is_car = equal!(cs, &g.op1_car_tag, unop_op1.tag())?;
        let op1_is_cdr = equal!(cs, &g.op1_cdr_tag, unop_op1.tag())?;
        let op1_is_car_or_cdr = or!(cs, &op1_is_car, &op1_is_cdr)?;
        let car_cdr_has_invalid_tag = and!(cs, &op1_is_car_or_cdr, &car_cdr_has_valid_tag.not())?;

        let op1_is_comm = equal!(cs, &g.op1_comm_tag, unop_op1.tag())?;
        let op1_is_num = equal!(cs, &g.op1_num_tag, unop_op1.tag())?;
        let op1_is_char = equal!(cs, &g.op1_char_tag, unop_op1.tag())?;
        let op1_is_open = equal!(cs, &g.op1_open_tag, unop_op1.tag())?;
        let op1_is_secret = equal!(cs, &g.op1_secret_tag, unop_op1.tag())?;

        let tag_is_char = equal!(cs, &g.char_tag, result.tag())?;
        let tag_is_num = equal!(cs, &g.num_tag, result.tag())?;
        let tag_is_comm = equal!(cs, &g.comm_tag, result.tag())?;

        let tag_is_num_or_comm = or!(cs, &tag_is_num, &tag_is_comm)?;
        let tag_is_num_or_char = or!(cs, &tag_is_num, &tag_is_char)?;
        let tag_is_num_or_comm_or_char = or!(cs, &tag_is_num_or_comm, &tag_is_char)?;

        let comm_invalid_tag_error = and!(cs, &tag_is_num_or_comm.not(), &op1_is_comm)?;
        let num_invalid_tag_error = and!(cs, &tag_is_num_or_comm_or_char.not(), &op1_is_num)?;
        let char_invalid_tag_error = and!(cs, &tag_is_num_or_char.not(), &op1_is_char)?;
        let open_invalid_tag_error = and!(cs, &tag_is_num_or_comm.not(), &op1_is_open)?;
        let secret_invalid_tag_error = and!(cs, &tag_is_num_or_comm.not(), &op1_is_secret)?;

        let any_error = or!(
            cs,
            &car_cdr_has_invalid_tag,
            &comm_invalid_tag_error,
            &num_invalid_tag_error,
            &num_invalid_tag_error,
            &char_invalid_tag_error,
            &open_invalid_tag_error,
            &secret_invalid_tag_error
        )?;

        let the_expr = pick_ptr!(cs, &any_error, result, &unop_val)?;

        let the_env = pick_ptr!(cs, &op1_is_eval, &g.nil_ptr, env)?;

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

        let newer_cont2_not_dummy0 = and!(cs, &op1_is_emit, &any_error.not())?;
        let newer_cont2_not_dummy = boolean_num!(cs, &newer_cont2_not_dummy0)?;

        (
            the_expr,
            the_env,
            the_cont,
            make_thunk_num,
            newer_cont2_not_dummy,
        )
    };

    results.add_clauses_cont(
        ContTag::Unop,
        &the_expr,
        &the_env,
        &the_cont,
        &make_thunk_num,
        &newer_cont2_not_dummy,
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
        &results.newer_cont2_not_dummy_clauses,
    ];

    let apply_cont_defaults = [
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.default_num,
        &g.false_num,
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

    // This is all clunky because we can't currently return AllocatedBit from case expressions.
    let newer_cont2_not_dummy_result_num = case_results[7].clone();
    let newer_cont2_not_dummy_ = equal!(cs, &newer_cont2_not_dummy_result_num, &g.true_num)?;
    let newer_cont2_not_dummy = and!(cs, &newer_cont2_not_dummy_, not_dummy)?;

    implies_equal!(
        cs,
        &newer_cont2_not_dummy,
        &g.true_num,
        &newer_cont2_not_dummy_num
    );

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

// Return an AllocatedPtr representing a Num whose value is the same as x's.
fn to_num<F: LurkField>(x: &AllocatedPtr<F>, g: &GlobalAllocations<F>) -> AllocatedPtr<F> {
    AllocatedPtr::from_parts(&g.num_tag, x.hash())
}

// Return an AllocatedPtr representing a Comm whose value is the same as x's.
fn to_comm<F: LurkField>(x: &AllocatedPtr<F>, g: &GlobalAllocations<F>) -> AllocatedPtr<F> {
    AllocatedPtr::from_parts(&g.comm_tag, x.hash())
}

// Return an AllocatedPtr representing a Char whose value is the same as x's.
//
// FIXME: no range-checking is performed, so the result could be an invalid Char. lurk-rs won't actually create such
// proofs because the out-of-range input will lead to an error when evaluating, but malicious input could still lead to
// such a proof. This would violate the principle that Lurk programs over valid input data should always return valid
// output data.
fn to_char<F: LurkField>(x: &AllocatedPtr<F>, g: &GlobalAllocations<F>) -> AllocatedPtr<F> {
    AllocatedPtr::from_parts(&g.char_tag, x.hash())
}

fn get_named_components<'a, F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    cont_ptr: &AllocatedContPtr<F>,
    name: ContName,
    allocated_cont_witness: &'a mut AllocatedContWitness<F>,
    not_dummy: &Boolean,
    _store: &Store<F>,
) -> Result<(AllocatedNum<F>, Vec<AllocatedNum<F>>), SynthesisError> {
    let expect_dummy = !not_dummy.get_value().unwrap_or(false);

    let (allocated_cont_components, allocated_cont_hash) =
        allocated_cont_witness.get_components(name, expect_dummy);

    implies_equal!(cs, not_dummy, cont_ptr.hash(), &allocated_cont_hash);

    Ok((allocated_cont_hash, allocated_cont_components))
}

fn car_cdr_named<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    maybe_cons: &AllocatedPtr<F>,
    name: ConsName,
    allocated_cons_witness: &mut AllocatedConsWitness<F>,
    not_dummy: &Boolean,
    _store: &Store<F>,
) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>), SynthesisError> {
    let maybe_cons_is_nil =
        maybe_cons.alloc_equal(&mut cs.namespace(|| "maybe_cons_is_nil"), &g.nil_ptr)?;

    let cons_not_dummy = and!(cs, &maybe_cons_is_nil.not(), not_dummy)?;

    let expect_dummy = !(cons_not_dummy.get_value().unwrap_or(false));

    let (allocated_car, allocated_cdr, allocated_digest) =
        allocated_cons_witness.get_cons(name, expect_dummy);

    let real_cons = alloc_equal(
        &mut cs.namespace(|| "cons is real"),
        maybe_cons.hash(),
        allocated_digest,
    )?;

    if cons_not_dummy.get_value().unwrap_or(false) && !real_cons.get_value().unwrap_or(true) {
        dbg!(maybe_cons.hash().get_value(), &allocated_digest.get_value());
        panic!(
            "tried to take car_cdr of a non-dummy cons ({:?}) but supplied wrong value",
            name
        );
    }

    implies!(cs, &cons_not_dummy, &real_cons);

    let res_car = pick_ptr!(cs, &maybe_cons_is_nil, &g.nil_ptr, &allocated_car)?;
    let res_cdr = pick_ptr!(cs, &maybe_cons_is_nil, &g.nil_ptr, &allocated_cdr)?;

    Ok((res_car, res_cdr))
}

fn extend_named<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    env: &AllocatedPtr<F>,
    var: &AllocatedPtr<F>,
    val: &AllocatedPtr<F>,
    name: ConsName,
    allocated_cons_witness: &mut AllocatedConsWitness<F>,
    not_dummy: &Boolean,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let new_binding = AllocatedPtr::construct_cons_named(
        &mut cs.namespace(|| "extend binding"),
        g,
        var,
        val,
        ConsName::Binding,
        allocated_cons_witness,
        not_dummy,
    )?;
    AllocatedPtr::construct_cons_named(
        cs,
        g,
        &new_binding,
        env,
        name,
        allocated_cons_witness,
        not_dummy,
    )
}

fn extend_rec<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    env: &AllocatedPtr<F>,
    var: &AllocatedPtr<F>,
    val: &AllocatedPtr<F>,
    allocated_cons_witness: &mut AllocatedConsWitness<F>,
    not_dummy: &Boolean,
    store: &Store<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let (binding_or_env, rest) = car_cdr_named(
        &mut cs.namespace(|| "car_cdr env"),
        g,
        env,
        ConsName::Env,
        allocated_cons_witness,
        not_dummy,
        store,
    )?;
    let (var_or_binding, _val_or_more_bindings) = car_cdr_named(
        &mut cs.namespace(|| "car_cdr binding_or_env"),
        g,
        &binding_or_env,
        ConsName::EnvCar,
        allocated_cons_witness,
        not_dummy,
        store,
    )?;

    let var_or_binding_is_cons = alloc_equal(
        &mut cs.namespace(|| "var_or_binding_is_cons"),
        var_or_binding.tag(),
        &g.cons_tag,
    )?;

    let cons = AllocatedPtr::construct_cons_named(
        &mut cs.namespace(|| "cons var val"),
        g,
        var,
        val,
        ConsName::NewRecCadr,
        allocated_cons_witness,
        not_dummy,
    )?;

    let list = AllocatedPtr::construct_cons_named(
        &mut cs.namespace(|| "list cons"),
        g,
        &cons,
        &g.nil_ptr,
        ConsName::NewRec,
        allocated_cons_witness,
        not_dummy,
    )?;

    let new_env_if_sym_or_nil = AllocatedPtr::construct_cons_named(
        &mut cs.namespace(|| "new_env_if_sym_or_nil"),
        g,
        &list,
        env,
        ConsName::ExtendedRec,
        allocated_cons_witness,
        not_dummy,
    )?;

    let cons_branch_not_dummy = and!(cs, &var_or_binding_is_cons, not_dummy)?;

    let cons2 = AllocatedPtr::construct_cons_named(
        &mut cs.namespace(|| "cons cons binding_or_env"),
        g,
        &cons,
        &binding_or_env,
        ConsName::NewRec,
        allocated_cons_witness,
        &cons_branch_not_dummy,
    )?;

    let cons3 = AllocatedPtr::construct_cons_named(
        &mut cs.namespace(|| "cons cons2 rest"),
        g,
        &cons2,
        &rest,
        ConsName::ExtendedRec,
        allocated_cons_witness,
        &cons_branch_not_dummy,
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
            assert_eq!(11569, cs.num_constraints());
            assert_eq!(13, cs.num_inputs());
            assert_eq!(11187, cs.aux().len());

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
