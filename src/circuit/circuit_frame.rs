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
    store::NamedConstants,
    tag::Tag,
};

use super::gadgets::constraints::{
    self, alloc_equal, alloc_equal_const, alloc_is_zero, and_v, div, enforce_implication, or, or_v,
    pick, pick_const, sub,
};
use crate::circuit::circuit_frame::constraints::{
    add, allocate_is_negative, boolean_to_num, enforce_pack, linear, mul,
};
use crate::circuit::gadgets::hashes::{AllocatedConsWitness, AllocatedContWitness};
use crate::circuit::ToInputs;
use crate::eval::{Frame, Witness, IO};
use crate::hash_witness::HashWitness;
use crate::proof::Provable;
use crate::store::{Ptr, Store, Thunk};
use crate::tag::{ContTag, ExprTag, Op1, Op2};
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::FromPrimitive;

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

    pub fn synthesize_frames<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &Store<F>,
        input_expr: AllocatedPtr<F>,
        input_env: AllocatedPtr<F>,
        input_cont: AllocatedContPtr<F>,
        frames: &[CircuitFrame<F, IO<F>, Witness<F>>],
        g: &GlobalAllocations<F>,
    ) -> (AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>) {
        let acc = (input_expr, input_env, input_cont);

        let (_, (new_expr, new_env, new_cont)) =
            frames.iter().fold((0, acc), |(i, allocated_io), frame| {
                if let Some(next_input) = frame.input {
                    // Ensure all intermediate allocated I/O values match the provided executation trace.
                    assert_eq!(
                        allocated_io.0.tag().get_value(),
                        store.hash_expr(&next_input.expr).map(|x| x.tag_field()),
                        "expr tag mismatch"
                    );
                    assert_eq!(
                        allocated_io.0.hash().get_value(),
                        store.hash_expr(&next_input.expr).map(|x| *x.value()),
                        "expr mismatch"
                    );
                    assert_eq!(
                        allocated_io.1.tag().get_value(),
                        store.hash_expr(&next_input.env).map(|x| x.tag_field()),
                        "env tag mismatch"
                    );
                    assert_eq!(
                        allocated_io.1.hash().get_value(),
                        store.hash_expr(&next_input.env).map(|x| *x.value()),
                        "env mismatch"
                    );
                    assert_eq!(
                        allocated_io.2.tag().get_value(),
                        store.hash_cont(&next_input.cont).map(|x| x.tag_field()),
                        "cont tag mismatch"
                    );
                    assert_eq!(
                        allocated_io.2.hash().get_value(),
                        store.hash_cont(&next_input.cont).map(|x| *x.value()),
                        "cont mismatch"
                    );
                };
                (i + 1, frame.synthesize(cs, i, allocated_io, g).unwrap())
            });

        (new_expr, new_env, new_cont)
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

    fn reduction_count(&self) -> usize {
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
                &mut cs.namespace(|| format!("allocated_cons_witness {i}")),
                store,
                &cons_witness,
            )?;

            let cont_witness = match self.witness.map(|x| x.conts) {
                Some(hw) => hw,
                None => HashWitness::new_blank(),
            };

            let mut allocated_cont_witness = AllocatedContWitness::from_cont_witness(
                &mut cs.namespace(|| format!("allocated_cont_witness {i}")),
                store,
                &cont_witness,
            )?;

            reduce_expression(
                &mut cs.namespace(|| format!("reduce expression {i}")),
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
            let mut store: Store<F> = Default::default();
            store.hydrate_scalar_cache();
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

            let (new_expr, new_env, new_cont) =
                self.synthesize_frames(cs, store, input_expr, input_env, input_cont, frames, &g);

            // dbg!(
            //     (&new_expr, &output_expr),
            //     new_expr.fetch_and_write_str(store),
            //     output_expr.fetch_and_write_str(store),
            //     (&new_env, &output_env),
            //     (&new_cont, &output_cont),
            //     new_cont.fetch_and_write_cont_str(store),
            //     output_cont.fetch_and_write_cont_str(store),
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

        match self.store {
            Some(s) => {
                let frames = self.frames.clone().unwrap();
                synth(s, &frames, self.input, self.output)
            }
            None => {
                let store = Default::default();
                assert!(self.frames.is_none());
                let frames = vec![CircuitFrame::blank(); self.count];
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
        key: ExprTag,
        result_expr: &'a AllocatedPtr<F>,
        result_env: &'a AllocatedPtr<F>,
        result_cont: &'a AllocatedContPtr<F>,
        result_apply_continuation: &'a AllocatedNum<F>,
    ) {
        let key = key.to_field();
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
        let key = key.to_field();
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
        let key = key.to_field();
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
        results.add_clauses_expr(ExprTag::Nil, expr, env, cont, &g.true_num);
        results.add_clauses_expr(ExprTag::Num, expr, env, cont, &g.true_num);
        results.add_clauses_expr(ExprTag::Fun, expr, env, cont, &g.true_num);
        results.add_clauses_expr(ExprTag::Char, expr, env, cont, &g.true_num);
        results.add_clauses_expr(ExprTag::Str, expr, env, cont, &g.true_num);
        results.add_clauses_expr(ExprTag::Comm, expr, env, cont, &g.true_num);
        results.add_clauses_expr(ExprTag::Key, expr, env, cont, &g.true_num);
        results.add_clauses_expr(ExprTag::U64, expr, env, cont, &g.true_num);
    };

    let cont_is_terminal = cont.alloc_tag_equal(
        &mut cs.namespace(|| "cont_is_terminal"),
        ContTag::Terminal.to_field(),
    )?;
    let cont_is_error = cont.alloc_tag_equal(
        &mut cs.namespace(|| "cont_is_error"),
        ContTag::Error.to_field(),
    )?;

    // Enforce (expr.tag == thunk_tag) implies (expr_thunk_hash == expr.hash).
    let expr_is_thunk = expr.is_thunk(&mut cs.namespace(|| "expr_is_thunk"))?;

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
            ExprTag::Thunk,
            &expr_thunk_value,
            env,
            &expr_thunk_continuation,
            &g.true_num,
        );
    }

    // --
    let reduce_sym_not_dummy = expr.is_sym(&mut cs.namespace(|| "reduce_sym_not_dummy"))?;
    let cont_is_terminal_or_error = or!(cs, &cont_is_terminal, &cont_is_error)?;
    let cont_is_not_terminal_or_error = cont_is_terminal_or_error.not();
    let reduce_sym_not_dummy = and!(cs, &reduce_sym_not_dummy, &cont_is_not_terminal_or_error)?;

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

    results.add_clauses_expr(
        ExprTag::Sym,
        &sym_result,
        &sym_env,
        &sym_cont,
        &sym_apply_cont,
    );
    // --

    // --
    let expr_is_cons = expr.is_cons(&mut cs.namespace(|| "reduce_cons_not_dummy0"))?;

    let reduce_cons_not_dummy = and!(cs, &expr_is_cons, &cont_is_not_terminal_or_error)?;

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
        ExprTag::Cons,
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
        &cont_is_terminal_or_error,
        &g.nil_ptr,
        &first_result_expr_0,
    )?;

    let first_result_env = AllocatedPtr::by_index(1, &case_results);
    let first_result_cont = AllocatedContPtr::by_index(2, &case_results);
    let first_result_apply_continuation: &AllocatedNum<F> = &case_results[6];

    let apply_continuation_boolean_0 = (alloc_is_zero(
        &mut cs.namespace(|| "apply_continuation_boolean_0"),
        first_result_apply_continuation,
    )?)
    .not();

    let apply_continuation_boolean = Boolean::and(
        &mut cs.namespace(|| "apply_continuation_boolean"),
        &apply_continuation_boolean_0,
        &cont_is_not_terminal_or_error,
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
    let make_thunk_boolean = &alloc_is_zero(
        &mut cs.namespace(|| "apply_continuation_make_thunk is zero"),
        &make_thunk_num,
    )?
    .not();

    let thunk_results = make_thunk(
        &mut cs.namespace(|| "make_thunk"),
        &result_cont0,
        &result_expr0,
        &result_env0,
        make_thunk_boolean,
        allocated_cont_witness,
        store,
        g,
    )?;

    let result_expr_candidate = AllocatedPtr::pick(
        &mut cs.namespace(|| "pick maybe make_thunk expr"),
        make_thunk_boolean,
        &thunk_results.0,
        &result_expr0,
    )?;

    let result_env_candidate = AllocatedPtr::pick(
        &mut cs.namespace(|| "pick maybe make_thunk env"),
        make_thunk_boolean,
        &thunk_results.1,
        &result_env0,
    )?;

    let result_cont_candidate = AllocatedContPtr::pick(
        &mut cs.namespace(|| "pick maybe make_thunk cont"),
        make_thunk_boolean,
        &thunk_results.2,
        &result_cont0,
    )?;

    let result_expr = AllocatedPtr::<F>::pick(
        &mut cs.namespace(|| "result_expr"),
        &cont_is_terminal_or_error,
        expr,
        &result_expr_candidate,
    )?;

    let result_env = AllocatedPtr::<F>::pick(
        &mut cs.namespace(|| "result_env"),
        &cont_is_terminal_or_error,
        env,
        &result_env_candidate,
    )?;

    let result_cont = AllocatedContPtr::<F>::pick(
        &mut cs.namespace(|| "result_cont"),
        &cont_is_terminal_or_error,
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

    let sym_is_t = expr.alloc_equal(&mut cs.namespace(|| "sym is t"), &g.t_ptr)?;
    let sym_is_nil = expr.is_nil(&mut cs.namespace(|| "sym is nil"), g)?;

    let sym_is_nil_or_t = or!(cs, &sym_is_nil, &sym_is_t)?;
    let sym_is_self_evaluating = and!(cs, &sym_is_nil_or_t, not_dummy)?;

    let sym_otherwise = and!(cs, &sym_is_self_evaluating.not(), not_dummy)?;

    let env_is_nil = env.is_nil(&mut cs.namespace(|| "env is nil"), g)?;
    let env_not_nil = env_is_nil.not();

    let env_not_dummy = &sym_otherwise;
    let (binding, smaller_env) = car_cdr_named(
        &mut cs.namespace(|| "If unevaled_args cons"),
        g,
        env,
        ConsName::Env,
        allocated_cons_witness,
        env_not_dummy,
        store,
    )?;

    let main = and!(cs, &sym_otherwise, &env_not_nil)?;

    let binding_is_nil = binding.is_nil(&mut cs.namespace(|| "binding is nil"), g)?;
    let binding_not_nil = binding_is_nil.not();
    let binding_is_cons = binding.is_cons(&mut cs.namespace(|| "binding_is_cons"))?;

    let env_car_not_dummy = and!(cs, &main, &binding_is_cons)?;
    let (var_or_rec_binding, val_or_more_rec_env) = car_cdr_named(
        &mut cs.namespace(|| "car_cdr binding"),
        g,
        &binding,
        ConsName::EnvCar,
        allocated_cons_witness,
        &env_car_not_dummy,
        store,
    )?;

    let var_or_rec_binding_is_sym =
        var_or_rec_binding.is_sym(&mut cs.namespace(|| "var_or_rec_binding_is_sym"))?;
    let var_or_rec_binding_is_cons =
        var_or_rec_binding.is_cons(&mut cs.namespace(|| "var_or_rec_binding_is_cons"))?;
    let var_or_rec_binding_is_sym_or_cons =
        or!(cs, &var_or_rec_binding_is_sym, &var_or_rec_binding_is_cons)?;

    let with_binding = and!(cs, &main, &binding_not_nil)?;
    let with_sym_binding = and!(cs, &with_binding, &var_or_rec_binding_is_sym)?;
    let with_cons_binding = and!(cs, &with_binding, &var_or_rec_binding_is_cons)?;
    let with_other_binding = and!(cs, &with_binding, &var_or_rec_binding_is_sym_or_cons.not())?;

    let v = var_or_rec_binding.clone();
    let val = val_or_more_rec_env.clone();
    let v_is_expr1 = expr.alloc_equal(&mut cs.namespace(|| "v_is_expr1"), &v)?;

    let envcaar_not_dummy = &with_cons_binding;
    let (v2, val2) = car_cdr_named(
        &mut cs.namespace(|| "car_cdr var_or_rec_binding"),
        g,
        &var_or_rec_binding,
        ConsName::EnvCaar,
        allocated_cons_witness,
        envcaar_not_dummy,
        store,
    )?;

    let val2_is_fun = val2.is_fun(&mut cs.namespace(|| "val2_is_fun"))?;
    let v2_is_expr = v2.alloc_equal(&mut cs.namespace(|| "v2_is_expr"), expr)?;
    let v2_is_expr_real = and!(cs, &v2_is_expr, envcaar_not_dummy)?;

    let extended_env_not_dummy = and!(cs, &val2_is_fun, &v2_is_expr_real)?;

    // NOTE: this allocation is unconstrained. See necessary constraint immediately below.
    let (fun_hash, fun_arg, fun_body, fun_closed_env) = Ptr::allocate_maybe_fun_unconstrained(
        &mut cs.namespace(|| "closure to extend"),
        store,
        witness.as_ref().and_then(|w| w.closure_to_extend.as_ref()),
    )?;

    // Without this, fun is unconstrained.
    implies_equal!(cs, &extended_env_not_dummy, &fun_hash, val2.hash());

    let rec_env = binding;

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

    let smaller_rec_env = &val_or_more_rec_env;
    let smaller_rec_env_is_nil =
        smaller_rec_env.is_nil(&mut cs.namespace(|| "smaller_rec_env_is_nil"), g)?;
    let smaller_rec_env_not_nil = smaller_rec_env_is_nil.not();

    let v2_not_expr = v2_is_expr.not();
    let otherwise_and_v2_not_expr = and!(cs, &v2_not_expr, &with_cons_binding)?;

    let smaller_rec_env_not_dummy = and!(cs, &smaller_rec_env_not_nil, &otherwise_and_v2_not_expr)?;

    let rec_extended_env = AllocatedPtr::construct_cons_named(
        &mut cs.namespace(|| "with_smaller_rec_env"),
        g,
        smaller_rec_env,
        &smaller_env,
        ConsName::EnvToUse,
        allocated_cons_witness,
        &smaller_rec_env_not_dummy,
    )?;

    let env_to_use = pick_ptr!(cs, &smaller_rec_env_is_nil, &smaller_env, &rec_extended_env)?;

    let cont_is_lookup = cont.alloc_tag_equal(
        &mut cs.namespace(|| "cons_is_lookup"),
        ContTag::Lookup.to_field(),
    )?;

    let needed_env_missing = and!(cs, &sym_otherwise, &env_is_nil)?;
    let needed_binding_missing = and!(cs, &main, &binding_is_nil)?;

    let with_sym_binding_matched = and!(cs, &with_sym_binding, &v_is_expr1)?;
    let with_sym_binding_unmatched = and!(cs, &with_sym_binding, &v_is_expr1.not())?;
    let with_sym_binding_unmatched_old_lookup =
        and!(cs, &with_sym_binding_unmatched, &cont_is_lookup)?;
    let with_sym_binding_unmatched_new_lookup =
        and!(cs, &with_sym_binding_unmatched, &cont_is_lookup.not())?;
    let with_cons_binding_matched = and!(cs, &with_cons_binding, &v2_is_expr)?;
    let with_cons_binding_unmatched = and!(cs, &with_cons_binding, &v2_is_expr.not())?;
    let with_cons_binding_unmatched_old_lookup =
        and!(cs, &with_cons_binding_unmatched, &cont_is_lookup)?;
    let with_cons_binding_unmatched_new_lookup =
        and!(cs, &with_cons_binding_unmatched, &cont_is_lookup.not())?;

    let lookup_continuation_not_dummy = or!(
        cs,
        &with_sym_binding_unmatched_new_lookup,
        &with_cons_binding_unmatched_new_lookup
    )?;
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

    let output_expr_is_expr = equal_t!(cs, &output_expr, expr)?;
    let output_env_is_env = equal_t!(cs, &output_env, env)?;
    let output_cont_is_cont = equal_t!(cs, &output_cont, cont)?;
    let output_cont_is_error = equal_t!(cs, &output_cont, &g.error_ptr)?;

    let output_expr_is_val = equal_t!(cs, &output_expr, &val)?;
    let output_env_is_smaller_env = equal_t!(cs, &output_env, &smaller_env)?;
    let output_cont_is_lookup = equal_t!(cs, &output_cont, &lookup_continuation)?;

    let output_expr_is_val_to_use = equal_t!(cs, &output_expr, &val_to_use)?;
    let output_env_is_env_to_use = equal_t!(cs, &output_env, &env_to_use)?;

    ////////////////////////////////////////////////////////////////////////////////
    // The way it should be.

    // expr
    let output_expr_should_be_expr = or!(
        cs,
        &needed_env_missing,
        &sym_is_self_evaluating,
        &needed_binding_missing,
        &with_sym_binding_unmatched,
        &with_cons_binding_unmatched
    )?;

    let output_expr_should_be_val = with_sym_binding_matched.clone();
    let output_expr_should_be_val_to_use = with_cons_binding_matched.clone();

    // env
    let output_env_should_be_env = or!(
        cs,
        &needed_binding_missing,
        &needed_env_missing,
        &sym_is_self_evaluating,
        &with_sym_binding_matched,
        &with_cons_binding_matched
    )?;

    let output_env_should_be_smaller_env = with_sym_binding_unmatched;
    let output_env_should_be_env_to_use = with_cons_binding_unmatched_new_lookup;

    // cont
    let output_cont_should_be_cont = or!(
        cs,
        &sym_is_self_evaluating,
        &with_sym_binding_matched,
        &with_sym_binding_unmatched_old_lookup,
        &with_cons_binding_matched,
        &with_cons_binding_unmatched_old_lookup
    )?;

    let output_cont_should_be_error = or!(
        cs,
        &with_other_binding,
        &needed_env_missing,
        &needed_binding_missing
    )?;

    ////////////////////////////////////////////////////////////////////////////////
    // "Because of the implication(s)."

    // expr
    implies!(cs, &output_expr_should_be_expr, &output_expr_is_expr);
    implies!(cs, &output_expr_should_be_val, &output_expr_is_val);
    implies!(
        cs,
        &output_expr_should_be_val_to_use,
        &output_expr_is_val_to_use
    );
    implies!(cs, &output_cont_should_be_error, &output_expr_is_expr);

    // env
    implies!(cs, &output_env_should_be_env, &output_env_is_env);
    implies!(
        cs,
        &output_env_should_be_smaller_env,
        &output_env_is_smaller_env
    );
    implies!(
        cs,
        &output_env_should_be_env_to_use,
        &output_env_is_env_to_use
    );
    implies!(cs, &output_cont_should_be_error, &output_env_is_env);

    // cont
    implies!(cs, &output_cont_should_be_cont, &output_cont_is_cont);
    implies!(cs, &output_cont_should_be_error, &output_cont_is_error);
    implies!(cs, &lookup_continuation_not_dummy, &output_cont_is_lookup);

    ////////////////////////////////////////////////////////////////////////////////
    // Are we proving Control::ApplyContinuation?
    let apply_cont_bool = or!(
        cs,
        &with_cons_binding_matched,
        &with_sym_binding_matched,
        &sym_is_self_evaluating
    )?;

    let apply_cont_num = boolean_num!(cs, &apply_cont_bool)?;
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

    let (head, rest) = car_cdr_named(
        &mut cs.namespace(|| "reduce_cons expr"),
        g,
        expr,
        ConsName::Expr,
        allocated_cons_witness,
        not_dummy,
        store,
    )?;

    macro_rules! def_head_val {
        ($var:ident, $name:expr) => {
            let $var =
                head.alloc_hash_equal(&mut cs.namespace(|| stringify!($var)), $name.value())?;
        };
    }
    let c = store.get_constants();
    // SOUNDNESS: All symbols with their own case clause must be represented in this list
    def_head_val!(head_is_lambda0, c.lambda);
    def_head_val!(head_is_let, c.let_);
    def_head_val!(head_is_letrec, c.letrec);
    def_head_val!(head_is_eval, c.eval);
    def_head_val!(head_is_quote0, c.quote);
    def_head_val!(head_is_cons, c.cons);
    def_head_val!(head_is_strcons, c.strcons);
    def_head_val!(head_is_hide, c.hide);
    def_head_val!(head_is_commit, c.commit);
    def_head_val!(head_is_open, c.open);
    def_head_val!(head_is_secret, c.secret);
    def_head_val!(head_is_num, c.num);
    def_head_val!(head_is_u64, c.u64);
    def_head_val!(head_is_comm, c.comm);
    def_head_val!(head_is_char, c.char);
    def_head_val!(head_is_begin, c.begin);
    def_head_val!(head_is_car, c.car);
    def_head_val!(head_is_cdr, c.cdr);
    def_head_val!(head_is_atom, c.atom);
    def_head_val!(head_is_emit, c.emit);
    def_head_val!(head_is_plus, c.sum);
    def_head_val!(head_is_minus, c.diff);
    def_head_val!(head_is_times, c.product);
    def_head_val!(head_is_div, c.quotient);
    def_head_val!(head_is_mod, c.modulo);
    def_head_val!(head_is_num_equal, c.num_equal);
    def_head_val!(head_is_eq, c.equal);
    def_head_val!(head_is_less, c.less);
    def_head_val!(head_is_less_equal, c.less_equal);
    def_head_val!(head_is_greater, c.greater);
    def_head_val!(head_is_greater_equal, c.greater_equal);
    def_head_val!(head_is_if0, c.if_);
    def_head_val!(head_is_current_env0, c.current_env);

    let head_is_a_sym = head.is_sym(&mut cs.namespace(|| "head_is_a_sym"))?;
    let head_is_a_cons = head.is_cons(&mut cs.namespace(|| "head_is_a_cons"))?;
    let head_is_fun = head.is_fun(&mut cs.namespace(|| "head_is_fun"))?;

    // SOUNDNESS: All head symbols corresponding to a binop *must* be included here.
    let head_is_binop0 = or!(
        cs,
        &head_is_cons,
        &head_is_strcons,
        &head_is_hide,
        &head_is_begin,
        &head_is_plus,
        &head_is_minus,
        &head_is_times,
        &head_is_div,
        &head_is_mod,
        &head_is_num_equal,
        &head_is_eq,
        &head_is_less,
        &head_is_less_equal,
        &head_is_greater,
        &head_is_greater_equal,
        &head_is_eval
    )?;

    let head_is_binop = and!(cs, &head_is_binop0, &head_is_a_sym)?;

    // SOUNDNESS: All head symbols corresponding to a unop *must* be included here.
    let head_is_unop0 = or!(
        cs,
        &head_is_car,
        &head_is_cdr,
        &head_is_commit,
        &head_is_num,
        &head_is_u64,
        &head_is_comm,
        &head_is_char,
        &head_is_open,
        &head_is_secret,
        &head_is_atom,
        &head_is_emit,
        &head_is_eval
    )?;

    let head_is_unop = and!(cs, &head_is_unop0, &head_is_a_sym)?;

    let head_is_let_or_letrec0 = or!(cs, &head_is_let, &head_is_letrec)?;
    let head_is_let_or_letrec = and!(cs, &head_is_let_or_letrec0, &head_is_a_sym)?;

    let head_is_lambda = and!(cs, &head_is_lambda0, &head_is_a_sym)?;
    let head_is_quote = and!(cs, &head_is_quote0, &head_is_a_sym)?;
    let head_is_current_env = and!(cs, &head_is_current_env0, &head_is_a_sym)?;
    let head_is_if = and!(cs, &head_is_if0, &head_is_a_sym)?;

    // This should enumerate all symbols, and it's important that each of these groups (some of which cover only one
    // symbol) also enforce that `head_is_a_sym`. Otherwise, expressions mimicking the symbol value can wreak havoc. See
    // `test_prove_head_with_sym_mimicking_value` in nova.rs and ensure it remains in sync with this code.
    let head_is_any = or!(
        cs,
        &head_is_quote,
        &head_is_if,
        &head_is_lambda,
        &head_is_current_env,
        &head_is_let_or_letrec,
        &head_is_unop,
        &head_is_binop
    )?;

    let head_potentially_fun_type = or!(cs, &head_is_a_sym, &head_is_a_cons, &head_is_fun)?;
    let head_potentially_fun = and!(cs, &head_potentially_fun_type, &head_is_any.not())?;

    let rest_is_nil = rest.is_nil(&mut cs.namespace(|| "rest_is_nil"), g)?;
    let rest_is_cons = rest.is_cons(&mut cs.namespace(|| "rest_is_cons"))?;

    let expr_cdr_not_dummy = and!(
        cs,
        not_dummy,
        &rest_is_nil.not(),
        &rest_is_cons,
        &head_is_any,
        &head_is_current_env.not() // current-env takes zero args
    )?;

    let is_dotted_error = and!(
        cs,
        &rest_is_nil.not(),
        &rest_is_cons.not(),
        &expr_cdr_not_dummy.not()
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

    let more_is_nil = more.is_nil(&mut cs.namespace(|| "more_is_nil"), g)?;

    let is_binop_missing_arg_error = and!(
        cs,
        &head_is_binop,
        &more_is_nil,
        &head_is_begin.not(),
        &head_is_eval.not()
    )?;

    let arg1_is_cons = arg1.is_cons(&mut cs.namespace(|| "arg1_is_cons"))?;
    let arg1_is_str = arg1.is_str(&mut cs.namespace(|| "arg1_is_str"))?;

    let arg1_is_nil = arg1.is_nil(&mut cs.namespace(|| "arg1_is_nil"), g)?;
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

    let end_is_nil = more.is_nil(&mut cs.namespace(|| "end_is_nil"), g)?;

    let mut results = Results::default();

    // --
    let (lambda_expr, lambda_env, lambda_cont) = {
        // head == LAMBDA
        // body == more == (cdr expr)
        let (args, body) = (arg1.clone(), more.clone());
        let args_is_nil = args.is_nil(&mut cs.namespace(|| "args_is_nil"), g)?;
        let cdr_args_is_nil = cdr_args.is_nil(&mut cs.namespace(|| "cdr_args_is_nil"), g)?;

        let arg = AllocatedPtr::pick(
            &mut cs.namespace(|| "maybe dummy arg"),
            &args_is_nil,
            &g.dummy_arg_ptr,
            &car_args,
        )?;

        let arg_is_sym = arg.is_sym(&mut cs.namespace(|| "arg_is_sym"))?;
        let lambda_not_dummy = and!(cs, &head_is_lambda, not_dummy, &more_is_nil.not())?;
        let inner_not_dummy = and!(cs, &lambda_not_dummy, &cdr_args_is_nil.not())?;

        let inner = AllocatedPtr::construct_cons_named(
            &mut cs.namespace(|| "inner"),
            g,
            &cdr_args,
            &body,
            ConsName::InnerLambda,
            allocated_cons_witness,
            &inner_not_dummy,
        )?;

        let l = AllocatedPtr::construct_cons_named(
            &mut cs.namespace(|| "l"),
            g,
            &g.lambda_sym,
            &inner,
            ConsName::Lambda,
            allocated_cons_witness,
            &inner_not_dummy,
        )?;

        let list = AllocatedPtr::construct_cons_named(
            &mut cs.namespace(|| "list"),
            g,
            &l,
            &g.nil_ptr,
            ConsName::InnerBody,
            allocated_cons_witness,
            &inner_not_dummy,
        )?;
        let inner_body = AllocatedPtr::pick(
            &mut cs.namespace(|| "inner_body"),
            &cdr_args_is_nil,
            &body,
            &list,
        )?;

        let function = AllocatedPtr::construct_fun(
            &mut cs.namespace(|| "function"),
            g,
            store,
            &arg,
            &inner_body,
            env,
        )?;
        let lambda_arg_error = and!(cs, &arg_is_sym.not(), &lambda_not_dummy)?;

        let lambda_expr = AllocatedPtr::pick(
            &mut cs.namespace(|| "lambda_expr"),
            &lambda_arg_error,
            expr,
            &function,
        )?;
        let lambda_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "lambda_cont"),
            &lambda_arg_error,
            &g.error_ptr_cont,
            cont,
        )?;

        (lambda_expr, env, lambda_cont)
    };

    results.add_clauses_cons(
        c.lambda.value(),
        &lambda_expr,
        lambda_env,
        &lambda_cont,
        &g.true_num,
    );

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

    results.add_clauses_cons(c.quote.value(), &arg1_or_expr, env, &the_cont, &g.true_num);

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
    let bindings_is_nil = bindings.is_nil(&mut cs.namespace(|| "bindings_is_nil"), g)?;
    let bindings_is_cons = bindings.is_cons(&mut cs.namespace(|| "bindings_is_cons"))?;
    let body_is_nil = body.is_nil(&mut cs.namespace(|| "body_is_nil"), g)?;
    let rest_body_is_nil = rest_body.is_nil(&mut cs.namespace(|| "rest_body_is_nil"), g)?;

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

        let (binding1, rest_bindings) = (car_args, cdr_args);

        let expr_caadr_not_dummy = and!(
            cs,
            &rest_body_is_nil,
            &body_is_nil.not(),
            &bindings_is_cons,
            &bindings_is_nil.not(),
            &let_letrec_not_dummy
        )?;

        let (var_let_letrec, vals) = car_cdr_named(
            &mut cs.namespace(|| "car_cdr binding1"),
            g,
            &binding1,
            ConsName::ExprCaadr,
            allocated_cons_witness,
            &expr_caadr_not_dummy,
            store,
        )?;

        let var_let_letrec_is_sym =
            var_let_letrec.is_sym(&mut cs.namespace(|| "var_let_letrec_is_sym"))?;
        let var_let_letrec_is_nil =
            var_let_letrec.is_nil(&mut cs.namespace(|| "var_let_letrec_is_nil"), g)?;
        let var_let_letrec_is_list = or!(cs, &var_let_letrec_is_sym, &var_let_letrec_is_nil)?;

        let expr_caaadr_not_dummy = and!(cs, &expr_caadr_not_dummy, &var_let_letrec_is_list)?;

        let (val, end) = car_cdr_named(
            &mut cs.namespace(|| "car_cdr vals"),
            g,
            &vals,
            ConsName::ExprCaaadr,
            allocated_cons_witness,
            &expr_caaadr_not_dummy,
            store,
        )?;

        let end_is_nil = end.is_nil(&mut cs.namespace(|| "end_is_nil"), g)?;

        /*
         * We get the condition for error by using OR of each individual error.
         */
        let cond_error = or!(
            cs,
            &rest_body_is_nil.not(),
            &end_is_nil.not(),
            &body_is_nil, // NOTE: end_is_nil is incidentally true by default in this case, but this should still be here.
            &var_let_letrec_is_list.not()
        )?;

        let rest_bindings_is_nil =
            rest_bindings.is_nil(&mut cs.namespace(|| "rest_bindings_is_nil"), g)?;

        let expanded_inner_not_dummy = and!(
            cs,
            &rest_bindings_is_nil.not(),
            &end_is_nil,
            &let_letrec_not_dummy,
            &body_is_nil.not(),
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
        // Otherwise, more than one argument was provided.
        // [binop_cont_tag, g.op2_eval_tag, env.tag(), env.hash(), more.tag(), more.hash(), cont.tag(), cont.hash()]

        let the_op = pick_const(
            &mut cs.namespace(|| "eval op"),
            &end_is_nil,
            ContTag::Unop.to_field(),
            ContTag::Binop.to_field(),
        )?;
        let op1_or_op2 = pick_const(
            &mut cs.namespace(|| "op1 or op2"),
            &end_is_nil,
            Op1::Eval.to_field(),
            Op2::Eval.to_field(),
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
        c.eval.value(),
        &the_op,
        eval_continuation_components,
    );

    // head == LET and LETREC preimage
    /////////////////////////////////////////////////////////////////////////////
    let let_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&var_let_letrec, &expanded_let, env, cont];
    hash_default_results.add_hash_input_clauses(
        c.let_.value(),
        &g.let_cont_tag,
        let_continuation_components,
    );
    let letrec_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&var_let_letrec, &expanded_letrec, env, cont];
    hash_default_results.add_hash_input_clauses(
        c.letrec.value(),
        &g.letrec_cont_tag,
        letrec_continuation_components,
    );

    // head == CONS preimage
    /////////////////////////////////////////////////////////////////////////////
    let cons_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_cons_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        c.cons.value(),
        &g.binop_cont_tag,
        cons_continuation_components,
    );

    // head == STRCONS preimage
    /////////////////////////////////////////////////////////////////////////////
    let strcons_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_strcons_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        c.strcons.value(),
        &g.binop_cont_tag,
        strcons_continuation_components,
    );

    // head == HIDE preimage
    /////////////////////////////////////////////////////////////////////////////
    let hide_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_hide_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        c.hide.value(),
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
        c.commit.value(),
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
        c.open.value(),
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
        c.secret.value(),
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
        c.num.value(),
        &g.unop_cont_tag,
        num_continuation_components,
    );

    // head == U64 preimage
    /////////////////////////////////////////////////////////////////////////////
    let u64_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] = &[
        &[&g.op1_u64_tag, &g.default_num],
        &[cont.tag(), cont.hash()],
        &[&g.default_num, &g.default_num],
        &[&g.default_num, &g.default_num],
    ];
    hash_default_results.add_hash_input_clauses(
        c.u64.value(),
        &g.unop_cont_tag,
        u64_continuation_components,
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
        c.comm.value(),
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
        c.char.value(),
        &g.unop_cont_tag,
        char_continuation_components,
    );

    // head == BEGIN preimage
    /////////////////////////////////////////////////////////////////////////////
    let begin_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_begin_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        c.begin.value(),
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
        c.car.value(),
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
        c.cdr.value(),
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
        c.atom.value(),
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
        c.emit.value(),
        &g.unop_cont_tag,
        emit_continuation_components,
    );

    // head == + preimage
    /////////////////////////////////////////////////////////////////////////////
    let sum_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_sum_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        c.sum.value(),
        &g.binop_cont_tag,
        sum_continuation_components,
    );

    // head == - preimage
    /////////////////////////////////////////////////////////////////////////////
    let diff_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_diff_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        c.diff.value(),
        &g.binop_cont_tag,
        diff_continuation_components,
    );

    // head == * preimage
    /////////////////////////////////////////////////////////////////////////////
    let product_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_product_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        c.product.value(),
        &g.binop_cont_tag,
        product_continuation_components,
    );

    // head == / preimage
    /////////////////////////////////////////////////////////////////////////////
    let quotient_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_quotient_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        c.quotient.value(),
        &g.binop_cont_tag,
        quotient_continuation_components,
    );

    // head == % preimage
    /////////////////////////////////////////////////////////////////////////////
    let modulo_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_modulo_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        c.modulo.value(),
        &g.binop_cont_tag,
        modulo_continuation_components,
    );

    // head == = preimage
    /////////////////////////////////////////////////////////////////////////////

    let numequal_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_numequal_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        c.num_equal.value(),
        &g.binop_cont_tag,
        numequal_continuation_components,
    );

    // head == EQ preimage
    /////////////////////////////////////////////////////////////////////////////
    let equal_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_equal_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        c.equal.value(),
        &g.binop_cont_tag,
        equal_continuation_components,
    );

    // head == < preimage
    /////////////////////////////////////////////////////////////////////////////
    let less_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_less_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        c.less.value(),
        &g.binop_cont_tag,
        less_continuation_components,
    );

    // head == <= preimage
    /////////////////////////////////////////////////////////////////////////////
    let less_equal_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_less_equal_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        c.less_equal.value(),
        &g.binop_cont_tag,
        less_equal_continuation_components,
    );

    // head == > preimage
    /////////////////////////////////////////////////////////////////////////////
    let greater_continuation_components: &[&dyn AsAllocatedHashComponents<F>; 4] =
        &[&[&g.op2_greater_tag, &g.default_num], env, &more, cont];
    hash_default_results.add_hash_input_clauses(
        c.greater.value(),
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
        c.greater_equal.value(),
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
        c.if_.value(),
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
        c.current_env.value(),
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
    // NOTE: It is critical for soundness that any code path which reliews on `newer_cont` also has
    // `newer_cont_not_dummy` true. This means that `newer_cont_unop` and `newer_cont_binop` must be accurate. This in
    // turn means that `head_is_unop` and `head_is_binop` *must* account for all head values (symbols) which have their
    // own case clause. See comments at `head_is_unop` and `head_is_binop`.
    let newer_cont_not_dummy = and!(
        cs,
        &newer_cont_not_dummy0,
        not_dummy,
        &is_dotted_error.not()
    )?;

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

        AllocatedContPtr::pick(
            &mut cs.namespace(|| "the_cont_let_letrec"),
            &cond_error,
            &g.error_ptr_cont,
            &output_cont_letrec,
        )?
    };
    results.add_clauses_cons(
        c.let_.value(),
        &the_expr,
        env,
        &the_cont_letrec,
        &g.false_num,
    );
    results.add_clauses_cons(
        c.letrec.value(),
        &the_expr,
        env,
        &the_cont_letrec,
        &g.false_num,
    );

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
        c.cons.value(),
        &arg1,
        env,
        &the_cont_cons_or_strcons,
        &g.false_num,
    );

    // head == STRCONS, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        c.strcons.value(),
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
    results.add_clauses_cons(c.begin.value(), &arg1, env, &cont_begin, &g.false_num);

    // head == CAR, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    let newer_cont_if_end_is_nil = AllocatedContPtr::pick(
        &mut cs.namespace(|| "newer_cont_if_end_is_nil"),
        &end_is_nil,
        &newer_cont,
        &g.error_ptr_cont,
    )?;

    results.add_clauses_cons(
        c.car.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == CDR, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        c.cdr.value(),
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
    results.add_clauses_cons(c.hide.value(), &arg1, env, &the_cont_hide, &g.false_num);

    // head == COMMIT, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        c.commit.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == OPEN, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    let the_cont_open_or_secret = &newer_cont_if_end_is_nil;

    results.add_clauses_cons(
        c.open.value(),
        &arg1_or_expr,
        env,
        the_cont_open_or_secret,
        &g.false_num,
    );

    // head == SECRET, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////

    results.add_clauses_cons(
        c.secret.value(),
        &arg1_or_expr,
        env,
        the_cont_open_or_secret,
        &g.false_num,
    );

    // head == NUM, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        c.num.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == U64, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        c.u64.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == COMM, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        c.comm.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == CHAR, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        c.char.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == EVAL, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(c.eval.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == ATOM, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        c.atom.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == EMIT, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        c.emit.value(),
        &arg1_or_expr,
        env,
        &newer_cont_if_end_is_nil,
        &g.false_num,
    );

    // head == +, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(c.sum.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == -, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(c.diff.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == *, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(c.product.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == /, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(c.quotient.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == %, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(c.modulo.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == =, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(c.num_equal.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == EQ, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(c.equal.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == <, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(c.less.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == <=, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(c.less_equal.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == >, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(c.greater.value(), &arg1, env, &newer_cont, &g.false_num);

    // head == >=, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(
        c.greater_equal.value(),
        &arg1,
        env,
        &newer_cont,
        &g.false_num,
    );

    // head == IF, newer_cont is allocated
    /////////////////////////////////////////////////////////////////////////////
    results.add_clauses_cons(c.if_.value(), &arg1, env, &newer_cont, &g.false_num);

    let is_zero_arg_call = rest_is_nil;

    // head == (FN . ARGS), newer_cont is allocated (deal with CALL and CALL0)
    /////////////////////////////////////////////////////////////////////////////
    let (res, continuation) = {
        let fun_form = &head;

        let more_args_is_nil = more.is_nil(&mut cs.namespace(|| "more_args_is_nil"), g)?;
        let args_is_nil_or_more_is_nil = or(
            &mut cs.namespace(|| "args is nil or more is nil"),
            &is_zero_arg_call,
            &more_args_is_nil,
        )?;

        // NOTE: not_dummy was moved last to avoid namespace conflicts. Until automatic-namespacing of and! and or! get
        // smarter, put shared elements last and unique ones first.
        let fn_not_dummy = and!(
            cs,
            &args_is_nil_or_more_is_nil.not(),
            &head_is_any.not(),
            &head_is_fun,
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

    let is_missing_first_arg_error = and!(
        cs,
        &expr_cdr_not_dummy.not(),
        &head_is_begin.not(),
        &head_is_current_env.not(),
        &head_potentially_fun.not()
    )?;
    let zero_arg_built_in_too_many_args_error =
        and!(cs, &head_is_current_env, &is_zero_arg_call.not())?;
    let is_error = or!(
        cs,
        &is_dotted_error,
        &is_binop_missing_arg_error,
        &is_missing_first_arg_error,
        &zero_arg_built_in_too_many_args_error
    )?;

    let result_expr = AllocatedPtr::pick(
        &mut cs.namespace(|| "result_expr"),
        &is_error,
        expr,
        &result_expr,
    )?;

    let result_env = AllocatedPtr::pick(
        &mut cs.namespace(|| "result_env"),
        &is_error,
        env,
        &result_env,
    )?;

    let result_cont = AllocatedContPtr::pick(
        &mut cs.namespace(|| "result_cont"),
        &is_error,
        &g.error_ptr_cont,
        &result_cont,
    )?;

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

    let cont_is_tail = cont.alloc_tag_equal(
        &mut cs.namespace(|| "cont_is_tail"),
        ContTag::Tail.to_field(),
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
    let c = store.get_constants();
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

    let cont_is_terminal = cont.alloc_tag_equal(
        &mut cs.namespace(|| "cont_is_terminal"),
        ContTag::Terminal.to_field(),
    )?;
    let cont_is_dummy = cont.alloc_tag_equal(
        &mut cs.namespace(|| "cont_is_dummy"),
        ContTag::Dummy.to_field(),
    )?;
    let cont_is_error = cont.alloc_tag_equal(
        &mut cs.namespace(|| "cont_is_error"),
        ContTag::Error.to_field(),
    )?;
    let cont_is_outermost = cont.alloc_tag_equal(
        &mut cs.namespace(|| "cont_is_outermost"),
        ContTag::Outermost.to_field(),
    )?;

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
        ContTag::Call0.to_field(),
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
        ContTag::Call.to_field(),
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
        ContTag::Call2.to_field(),
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
        ContTag::Let.to_field(),
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
        ContTag::LetRec.to_field(),
        &g.tail_cont_tag,
        letrec_components,
    );

    // Commitment values used in Unop but also outside, so can't be in Unop scope.
    let (commitment, commitment_secret, committed_expr) = {
        let cs = &mut cs.namespace(|| "common");
        let operator = AllocatedPtr::by_index(0, &continuation_components);

        let is_op2_hide =
            operator.alloc_tag_equal(&mut cs.namespace(|| "is_op2_hide"), Op2::Hide.to_field())?;
        let is_op1_open =
            operator.alloc_tag_equal(&mut cs.namespace(|| "is_op1_open"), Op1::Open.to_field())?;
        let is_op1_secret = operator.alloc_tag_equal(
            &mut cs.namespace(|| "is_op1_secret"),
            Op1::Secret.to_field(),
        )?;
        let is_op1_open_or_secret = or!(cs, &is_op1_open, &is_op1_secret)?;

        // IF this is open, we need to know what we are opening.
        let digest = result.hash();

        let (open_secret_scalar, open_expr_ptr) = match store.get_maybe_opaque(
            ExprTag::Comm,
            digest.get_value().unwrap_or_else(|| F::zero()),
        ) {
            Some(commit) => match store.open(commit) {
                Some((secret, opening)) => (secret, opening),
                None => (F::zero(), store.get_nil()), // nil is dummy
            },
            None => (F::zero(), store.get_nil()), // nil is dummy
        };

        let open_expr = AllocatedPtr::alloc(&mut cs.namespace(|| "open_expr"), || {
            Ok(store.hash_expr(&open_expr_ptr).unwrap())
        })?;

        let open_secret = AllocatedNum::alloc(&mut cs.namespace(|| "open_secret"), || {
            Ok(open_secret_scalar)
        })?;

        let arg1 = AllocatedPtr::by_index(1, &continuation_components);

        let commit_secret = pick!(cs, &is_op2_hide, arg1.hash(), &g.default_num)?;
        let secret = pick!(cs, &is_op1_open_or_secret, &open_secret, &commit_secret)?;
        let committed = pick_ptr!(cs, &is_op1_open, &open_expr, result)?;
        let hide = hide(&mut cs.namespace(|| "Hide"), g, &secret, &committed, store)?;
        (hide, secret, committed)
    };

    // Continuation::Unop preimage
    /////////////////////////////////////////////////////////////////////////////
    let (unop_val, unop_continuation) = {
        let cs = &mut cs.namespace(|| "Unop preimage");
        let op1 = AllocatedPtr::by_index(0, &continuation_components);
        let unop_continuation = AllocatedContPtr::by_index(1, &continuation_components);

        let cont_is_unop = cont.alloc_tag_equal(
            &mut cs.namespace(|| "cont_is_unop"),
            ContTag::Unop.to_field(),
        )?;

        let unop_op_is_car =
            op1.alloc_tag_equal(&mut cs.namespace(|| "unop_op_is_car"), Op1::Car.to_field())?;
        let unop_op_is_cdr =
            op1.alloc_tag_equal(&mut cs.namespace(|| "unop_op_is_cdr"), Op1::Cdr.to_field())?;
        let unop_op_is_car_or_cdr = or!(cs, &unop_op_is_car, &unop_op_is_cdr)?;

        let result_is_cons = result.is_cons(&mut cs.namespace(|| "result_is_cons"))?;
        let result_is_str = result.is_str(&mut cs.namespace(|| "result_is_str"))?;

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
            &result_is_empty_str.not()
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

        let is_atom_ptr = AllocatedPtr::pick(
            &mut cs.namespace(|| "is_atom_ptr"),
            &result_is_cons,
            &g.nil_ptr,
            &g.t_ptr,
        )?;

        let num = to_num(result, g);
        let comm = to_comm(result, g);

        let (u32_elem, u64_elem) =
            to_unsigned_integers(&mut cs.namespace(|| "Unop u32 and u64"), g, result.hash())?;

        let res = multi_case(
            &mut cs.namespace(|| "Unop case"),
            op1.tag(),
            &[
                &[
                    CaseClause {
                        key: Op1::Car.to_field(),
                        value: res_car.tag(),
                    },
                    CaseClause {
                        key: Op1::Cdr.to_field(),
                        value: res_cdr.tag(),
                    },
                    CaseClause {
                        key: Op1::Atom.to_field(),
                        value: is_atom_ptr.tag(),
                    },
                    CaseClause {
                        key: Op1::Emit.to_field(),
                        value: result.tag(),
                    },
                    CaseClause {
                        key: Op1::Commit.to_field(),
                        value: commitment.tag(),
                    },
                    CaseClause {
                        key: Op1::Open.to_field(),
                        value: committed_expr.tag(),
                    },
                    CaseClause {
                        key: Op1::Secret.to_field(),
                        value: &g.num_tag,
                    },
                    CaseClause {
                        key: Op1::Num.to_field(),
                        value: num.tag(),
                    },
                    CaseClause {
                        key: Op1::U64.to_field(),
                        value: &g.u64_tag,
                    },
                    CaseClause {
                        key: Op1::Comm.to_field(),
                        value: comm.tag(),
                    },
                    CaseClause {
                        key: Op1::Char.to_field(),
                        value: &g.char_tag,
                    },
                    CaseClause {
                        key: Op1::Eval.to_field(),
                        value: result.tag(),
                    },
                ],
                &[
                    CaseClause {
                        key: Op1::Car.to_field(),
                        value: allocated_car.hash(),
                    },
                    CaseClause {
                        key: Op1::Cdr.to_field(),
                        value: allocated_cdr.hash(),
                    },
                    CaseClause {
                        key: Op1::Atom.to_field(),
                        value: is_atom_ptr.hash(),
                    },
                    CaseClause {
                        key: Op1::Emit.to_field(),
                        value: result.hash(),
                    },
                    CaseClause {
                        key: Op1::Commit.to_field(),
                        value: commitment.hash(),
                    },
                    CaseClause {
                        key: Op1::Open.to_field(),
                        value: committed_expr.hash(),
                    },
                    CaseClause {
                        key: Op1::Secret.to_field(),
                        value: &commitment_secret,
                    },
                    CaseClause {
                        key: Op1::Num.to_field(),
                        value: num.hash(),
                    },
                    CaseClause {
                        key: Op1::U64.to_field(),
                        value: &u64_elem,
                    },
                    CaseClause {
                        key: Op1::Comm.to_field(),
                        value: comm.hash(),
                    },
                    CaseClause {
                        key: Op1::Char.to_field(),
                        value: &u32_elem,
                    },
                    CaseClause {
                        key: Op1::Eval.to_field(),
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
        ContTag::Unop.to_field(),
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
        ContTag::Binop.to_field(),
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

    // Reused in Call0, Call, and Call2.
    let result_is_fun = function.is_fun(&mut cs.namespace(|| "result_is_fun"))?;

    // Continuation::Call0
    /////////////////////////////////////////////////////////////////////////////
    let (the_expr, the_env, the_cont, newer_cont2_not_dummy) = {
        let mut cs = cs.namespace(|| "Call0");
        let continuation = AllocatedContPtr::by_index(1, &continuation_components);

        let cont_is_call0 = cont.alloc_tag_equal(
            &mut cs.namespace(|| "cont_is_call0"),
            ContTag::Call0.to_field(),
        )?;
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

        let body_t_is_cons = body_t.is_cons(&mut cs.namespace(|| "body_t_is_cons"))?;
        let body_t_is_nil = body_t.is_nil(&mut cs.namespace(|| "body_t_is_nil"), g)?;

        let body_is_list = or!(cs, &body_t_is_cons, &body_t_is_nil)?;
        let zero_arg_call_not_dummy = and!(cs, &call0_not_dummy, &body_is_list, &args_is_dummy)?;

        let (body_form, end) = car_cdr_named(
            &mut cs.namespace(|| "body_form"),
            g,
            &body_t,
            ConsName::FunBody,
            allocated_cons_witness,
            &zero_arg_call_not_dummy,
            store,
        )?;

        let end_is_nil = end.is_nil(&mut cs.namespace(|| "end_is_nil"), g)?;

        let continuation_is_tail = continuation.alloc_tag_equal(
            &mut cs.namespace(|| "continuation is tail"),
            ContTag::Tail.to_field(),
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

        let body_form_is_nil = body_form.is_nil(&mut cs.namespace(|| "body_form_is_nil"), g)?;
        let body_is_well_formed = and!(cs, &body_form_is_nil.not(), &end_is_nil)?;

        let result_is_valid_fun = and!(cs, &result_is_fun, &body_is_well_formed)?;
        let result_is_valid_zero_arg_fun = and!(cs, &result_is_valid_fun, &args_is_dummy)?;

        let the_expr = AllocatedPtr::pick(
            &mut cs.namespace(|| "the_expr"),
            &result_is_valid_zero_arg_fun,
            &next_expr,
            result,
        )?;

        let the_env = AllocatedPtr::pick(
            &mut cs.namespace(|| "the_env"),
            &result_is_fun,
            &next_env,
            env,
        )?;

        let result_not_fun_and_zero_arg_call_is_dummy =
            and!(cs, &zero_arg_call_not_dummy.not(), &result_is_fun)?;
        let the_cont_not_error = or!(
            cs,
            &result_is_valid_fun,
            &result_not_fun_and_zero_arg_call_is_dummy
        )?;

        let the_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "the_cont"),
            &the_cont_not_error,
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
            let cont_is_call2_precomp = cont.alloc_tag_equal(
                &mut cs.namespace(|| "cont_is_call2_precomp"),
                ContTag::Call2.to_field(),
            )?;
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
            let args_is_not_dummy = args_is_dummy.not();

            let cont_is_call2_and_not_dummy_and_not_dummy_args =
                and!(cs, &cont_is_call2_and_not_dummy, &args_is_not_dummy)?;

            let (body_form, end) = car_cdr_named(
                &mut cs.namespace(|| "body_form"),
                g,
                &body_t,
                ConsName::FunBody,
                allocated_cons_witness,
                &cont_is_call2_and_not_dummy_and_not_dummy_args,
                store,
            )?;

            let body_form_is_nil = body_form.is_nil(&mut cs.namespace(|| "body_form_is_nil"), g)?;
            let end_is_nil = end.is_nil(&mut cs.namespace(|| "end_is_nil"), g)?;
            let body_is_well_formed = and!(cs, &body_form_is_nil.not(), &end_is_nil)?;

            let extend_not_dummy = and!(
                cs,
                &cont_is_call2_and_not_dummy,
                &args_is_dummy.not(),
                &body_is_well_formed
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

            let continuation_is_tail = continuation.alloc_tag_equal(
                &mut cs.namespace(|| "continuation is tail"),
                ContTag::Tail.to_field(),
            )?;

            let tail_cont = AllocatedContPtr::pick(
                &mut cs.namespace(|| "the tail continuation"),
                &continuation_is_tail,
                &continuation,
                &newer_cont2,
            );

            let cond0 = or!(cs, &args_is_dummy.not(), &result_is_fun)?;
            let cond = and!(cs, &cond0, &body_is_well_formed)?; // &body_form_is_nil.not(), &end_is_nil)?;

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

        let cont_is_binop = cont.alloc_tag_equal(
            &mut cs.namespace(|| "cont_is_binop"),
            ContTag::Binop.to_field(),
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

        let op_is_begin =
            operator.alloc_tag_equal(&mut cs.namespace(|| "op_is_begin"), Op2::Begin.to_field())?;

        let rest_is_nil = allocated_rest.is_nil(&mut cs.namespace(|| "rest_is_nil"), g)?;
        let rest_not_nil = rest_is_nil.not();

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

        let otherwise = op_is_begin.not();

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
        let mut cs = cs.namespace(|| "Binop2");
        let op2 = AllocatedPtr::by_index(0, &continuation_components);
        let arg1 = AllocatedPtr::by_index(1, &continuation_components);
        let continuation = AllocatedContPtr::by_index(2, &continuation_components);

        let arg2 = result;

        let arg1_is_num = arg1.is_num(&mut cs.namespace(|| "arg1_is_num"))?;
        let arg2_is_num = arg2.is_num(&mut cs.namespace(|| "arg2_is_num"))?;
        let both_args_are_nums = Boolean::and(
            &mut cs.namespace(|| "both_args_are_nums"),
            &arg1_is_num,
            &arg2_is_num,
        )?;
        let arg1_is_u64 = arg1.is_u64(&mut cs.namespace(|| "arg1_is_u64"))?;
        let arg2_is_u64 = arg2.is_u64(&mut cs.namespace(|| "arg2_is_u64"))?;
        let both_args_are_u64s = Boolean::and(
            &mut cs.namespace(|| "both_args_are_u64s"),
            &arg1_is_u64,
            &arg2_is_u64,
        )?;

        let arg1_is_num_and_arg2_is_u64 = Boolean::and(
            &mut cs.namespace(|| "arg1_is_num_and_arg2_is_u64"),
            &arg1_is_num,
            &arg2_is_u64,
        )?;
        let arg1_is_u64_and_arg2_is_num = Boolean::and(
            &mut cs.namespace(|| "arg1_is_u64_and_arg2_is_num"),
            &arg1_is_u64,
            &arg2_is_num,
        )?;

        let args_are_num_or_u64 = or!(
            cs,
            &both_args_are_nums,
            &both_args_are_u64s,
            &arg1_is_num_and_arg2_is_u64,
            &arg1_is_u64_and_arg2_is_num
        )?;

        let arg1_u64_to_num = to_num(&arg1, g);
        let arg1_final = AllocatedPtr::pick(
            &mut cs.namespace(|| "arg1_final"),
            &arg1_is_u64_and_arg2_is_num,
            &arg1_u64_to_num,
            &arg1,
        )?;

        let arg2_u64_to_num = to_num(arg2, g);
        let arg2_final = AllocatedPtr::pick(
            &mut cs.namespace(|| "arg2_final"),
            &arg1_is_num_and_arg2_is_u64,
            &arg2_u64_to_num,
            arg2,
        )?;

        let (a, b) = (arg1_final.hash(), arg2_final.hash()); // For Nums, the 'hash' is an immediate value.

        let args_equal = arg1_final.alloc_equal(&mut cs.namespace(|| "args_equal"), &arg2_final)?;

        let args_equal_ptr = AllocatedPtr::pick_const(
            &mut cs.namespace(|| "args_equal_ptr"),
            &args_equal,
            &c.t.scalar_ptr(),
            &c.nil.scalar_ptr(),
        )?;

        let not_dummy = cont.alloc_tag_equal(
            &mut cs.namespace(|| "Binop2 not dummy"),
            ContTag::Binop2.to_field(),
        )?;

        let sum = add(&mut cs.namespace(|| "sum"), a, b)?;
        let diff = sub(&mut cs.namespace(|| "difference"), a, b)?;
        let product = mul(&mut cs.namespace(|| "product"), a, b)?;

        let op2_is_div =
            op2.alloc_tag_equal(&mut cs.namespace(|| "op2_is_div"), Op2::Quotient.to_field())?;
        let op2_is_mod =
            op2.alloc_tag_equal(&mut cs.namespace(|| "op2_is_mod"), Op2::Modulo.to_field())?;

        let op2_is_div_or_mod = or(
            &mut cs.namespace(|| "op2 is div or mod"),
            &op2_is_div,
            &op2_is_mod,
        )?;

        let b_is_zero = &alloc_is_zero(&mut cs.namespace(|| "b_is_zero"), b)?;

        let divisor = pick(
            &mut cs.namespace(|| "maybe-dummy divisor"),
            b_is_zero,
            &g.true_num,
            b,
        )?;

        let quotient = div(&mut cs.namespace(|| "quotient"), a, &divisor)?;

        let is_cons =
            op2.alloc_tag_equal(&mut cs.namespace(|| "Op2 is Cons"), Op2::Cons.to_field())?;
        let is_strcons = op2.alloc_tag_equal(
            &mut cs.namespace(|| "Op2 is StrCons"),
            Op2::StrCons.to_field(),
        )?;

        let is_cons_or_strcons = or(
            &mut cs.namespace(|| "is cons or strcons"),
            &is_cons,
            &is_strcons,
        )?;

        let arg1_is_char = arg1.is_char(&mut cs.namespace(|| "arg1_is_char"))?;
        let arg2_is_str = arg2.is_str(&mut cs.namespace(|| "arg2_is_str"))?;
        let args_are_char_str = Boolean::and(
            &mut cs.namespace(|| "args_are_char_str"),
            &arg1_is_char,
            &arg2_is_str,
        )?;

        let args_not_char_str = args_are_char_str.not();
        let invalid_strcons_tag = Boolean::and(
            &mut cs.namespace(|| "invalid_strcons_tag"),
            &args_not_char_str,
            &is_strcons,
        )?;

        let cons_not_dummy = and!(
            cs,
            &is_cons_or_strcons,
            &not_dummy,
            &invalid_strcons_tag.not()
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
                    key: Op2::Sum.to_field(),
                    value: &sum,
                },
                CaseClause {
                    key: Op2::Diff.to_field(),
                    value: &diff,
                },
                CaseClause {
                    key: Op2::Product.to_field(),
                    value: &product,
                },
                CaseClause {
                    key: Op2::Quotient.to_field(),
                    value: &quotient,
                },
                CaseClause {
                    key: Op2::Equal.to_field(),
                    value: args_equal_ptr.hash(),
                },
                CaseClause {
                    key: Op2::NumEqual.to_field(),
                    value: args_equal_ptr.hash(),
                },
                CaseClause {
                    key: Op2::Cons.to_field(),
                    value: cons.hash(),
                },
                CaseClause {
                    key: Op2::StrCons.to_field(),
                    value: cons.hash(),
                },
                CaseClause {
                    key: Op2::Hide.to_field(),
                    value: commitment.hash(),
                },
            ],
            &g.default_num,
            g,
        )?;

        let is_equal =
            op2.alloc_tag_equal(&mut cs.namespace(|| "Op2 is Equal"), Op2::Equal.to_field())?;

        let is_num_equal = op2.alloc_tag_equal(
            &mut cs.namespace(|| "Op2 is NumEqual"),
            Op2::NumEqual.to_field(),
        )?;

        let is_equal_or_num_equal = or(
            &mut cs.namespace(|| "is_equal_or_num_equal"),
            &is_equal,
            &is_num_equal,
        )?;

        let op2_is_hide =
            op2.alloc_tag_equal(&mut cs.namespace(|| "Op2 is Hide"), Op2::Hide.to_field())?;

        let commitment_tag_is_comm =
            commitment.is_comm(&mut cs.namespace(|| "commitment tag is comm"))?;

        let commitment_tag_is_dummy = alloc_is_zero(
            &mut cs.namespace(|| "commitment tag is dummy"),
            commitment.tag(),
        )?;

        let commitment_tag_is_correct = or(
            &mut cs.namespace(|| "commitment tag is correct"),
            &commitment_tag_is_comm,
            &commitment_tag_is_dummy,
        )?;

        implies!(cs, &op2_is_hide, &commitment_tag_is_correct);

        let cons_tag = pick_const(
            &mut cs.namespace(|| "cons_tag"),
            &is_strcons,
            ExprTag::Str.to_field(),
            ExprTag::Cons.to_field(),
        )?;

        let comm_or_num_tag = pick_const(
            &mut cs.namespace(|| "Op2 tag is comm or num"),
            &op2_is_hide,
            ExprTag::Comm.to_field(),
            ExprTag::Num.to_field(),
        )?;

        let is_cons_or_hide = or!(cs, &is_cons, &op2_is_hide)?;

        let is_cons_or_strcons_or_hide_or_equal =
            or!(cs, &is_cons_or_hide, &is_strcons, &is_equal)?;

        let is_cons_or_strcons_or_hide_or_equal_or_num_equal = or(
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

        let (is_comparison_tag, comp_val, diff_is_negative) = comparison_helper(
            &mut cs.namespace(|| "enforce comparison"),
            g,
            a,
            b,
            &diff,
            op2.tag(),
            store.get_constants(),
        )?;

        let field_arithmetic_result = AllocatedPtr::pick(
            &mut cs.namespace(|| "field arithmetic result"),
            &is_comparison_tag,
            &comp_val,
            &res,
        )?;

        // Subtraction in U64 is almost the same as subtraction in the field.
        // If the difference is negative, we need to add 2^64 to get back to U64 domain.
        let field_arithmetic_result_plus_2p64 = add(
            &mut cs.namespace(|| "field arithmetic result plus 2^64"),
            field_arithmetic_result.hash(),
            &g.power2_64_num,
        )?;

        let op2_is_diff =
            op2.alloc_tag_equal(&mut cs.namespace(|| "op2_is_diff"), Op2::Diff.to_field())?;

        let diff_is_negative_and_op2_is_diff = Boolean::and(
            &mut cs.namespace(|| "diff is negative and op2 is diff"),
            &diff_is_negative,
            &op2_is_diff,
        )?;

        let field_arith_and_u64_diff_result = pick(
            &mut cs.namespace(|| "field arith and u64 diff result"),
            &diff_is_negative_and_op2_is_diff,
            &field_arithmetic_result_plus_2p64,
            field_arithmetic_result.hash(),
        )?;

        let coerce_to_u64 = to_u64(
            &mut cs.namespace(|| "binop coerce to u64"),
            g,
            &field_arith_and_u64_diff_result,
        )?;
        let coerce_to_u64_ptr = AllocatedPtr::from_parts(&g.u64_tag, &coerce_to_u64);

        let both_args_are_u64s_and_not_comparison = Boolean::and(
            &mut cs.namespace(|| "both_args_are_u64_and_not_comparison"),
            &both_args_are_u64s,
            &is_comparison_tag.not(),
        )?;

        let partial_u64_result = AllocatedPtr::pick(
            &mut cs.namespace(|| "partial u64 result"),
            &both_args_are_u64s_and_not_comparison,
            &coerce_to_u64_ptr,
            &field_arithmetic_result,
        )?;

        let (alloc_q, alloc_r) = enforce_u64_div_mod(
            &mut cs.namespace(|| "u64 div mod equation"),
            op2_is_mod.clone(),
            &arg1,
            arg2,
        )?;
        let alloc_q_ptr = AllocatedPtr::from_parts(&g.u64_tag, &alloc_q);
        let alloc_r_ptr = AllocatedPtr::from_parts(&g.u64_tag, &alloc_r);

        let op2_is_div_and_args_are_u64s = Boolean::and(
            &mut cs.namespace(|| "op2 is div and args are u64s"),
            &op2_is_div,
            &both_args_are_u64s,
        )?;
        let include_u64_quotient = AllocatedPtr::pick(
            &mut cs.namespace(|| "include u64 quotient"),
            &op2_is_div_and_args_are_u64s,
            &alloc_q_ptr,
            &partial_u64_result,
        )?;
        let op2_is_mod_and_args_are_u64s = Boolean::and(
            &mut cs.namespace(|| "op2 is mod and args are u64s"),
            &op2_is_mod,
            &both_args_are_u64s,
        )?;
        let op2_is_mod_and_args_are_not_u64s = Boolean::and(
            &mut cs.namespace(|| "op2 is mod and args are not u64s"),
            &op2_is_mod,
            &both_args_are_u64s.not(),
        )?;
        // include u64 mod
        let arithmetic_result = AllocatedPtr::pick(
            &mut cs.namespace(|| "arithmetic result"),
            &op2_is_mod_and_args_are_u64s,
            &alloc_r_ptr,
            &include_u64_quotient,
        )?;

        let valid_types = or(
            &mut cs.namespace(|| "Op2 called with valid types"),
            &is_cons_or_strcons_or_hide_or_equal,
            &args_are_num_or_u64,
        )?;

        let real_div_or_mor_and_b_is_zero = and!(cs, &not_dummy, &op2_is_div_or_mod, b_is_zero)?;

        let valid_types_and_not_div_by_zero = Boolean::and(
            &mut cs.namespace(|| "Op2 called with no errors"),
            &valid_types,
            &real_div_or_mor_and_b_is_zero.not(),
        )?;

        let op2_not_num_or_u64_and_not_cons_or_strcons_or_hide_or_equal_or_num_equal =
            Boolean::and(
                &mut cs
                    .namespace(|| "not num and not cons or strcons or hide or equal or num_equal"),
                &args_are_num_or_u64.not(),
                &is_cons_or_strcons_or_hide_or_equal_or_num_equal.not(),
            )?;

        let invalid_secret_tag_hide = Boolean::and(
            &mut cs.namespace(|| "invalid_secret_tag_hide"),
            &arg1_is_u64,
            &op2_is_hide,
        )?;

        let op2_is_hide_and_arg1_is_not_num = and!(cs, &op2_is_hide, &arg1_is_num.not())?;

        let any_error = or!(
            cs,
            &valid_types_and_not_div_by_zero.not(),
            &op2_not_num_or_u64_and_not_cons_or_strcons_or_hide_or_equal_or_num_equal,
            &invalid_strcons_tag,
            &op2_is_hide_and_arg1_is_not_num,
            &op2_is_mod_and_args_are_not_u64s,
            &invalid_secret_tag_hide
        )?;

        let op2_is_eval =
            op2.alloc_tag_equal(&mut cs.namespace(|| "op2_is_eval"), Op2::Eval.to_field())?;

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
            &arithmetic_result,
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

        let make_thunk_num = boolean_to_num(
            &mut cs.namespace(|| "maybe eval make_thunk_num"),
            &op2_is_eval.not(),
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

        let cont_is_if =
            cont.alloc_tag_equal(&mut cs.namespace(|| "cont_is_if"), ContTag::If.to_field())?;

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

        let condition_is_nil = condition.is_nil(&mut cs.namespace(|| "condition is nil"), g)?;

        let (arg2, end) = car_cdr_named(
            &mut cs.namespace(|| "more cons"),
            g,
            &more,
            ConsName::UnevaledArgsCdr,
            allocated_cons_witness,
            &if_not_dummy,
            store,
        )?;

        let end_is_nil = end.is_nil(&mut cs.namespace(|| "end_is_nil"), g)?;

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

        let cont_is_let =
            cont.alloc_tag_equal(&mut cs.namespace(|| "cont_is_let"), ContTag::Let.to_field())?;
        let let_cont_is_let = let_cont.alloc_tag_equal(
            &mut cs.namespace(|| "let_cont_is_let"),
            ContTag::Let.to_field(),
        )?;

        let extended_env_not_dummy = and!(cs, &let_cont_is_let, not_dummy, &cont_is_let)?;

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

        let continuation_is_tail = let_cont.alloc_tag_equal(
            &mut cs.namespace(|| "continuation is tail"),
            ContTag::Tail.to_field(),
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

        let letrec_cont_is_letrec_cont = letrec_cont.alloc_tag_equal(
            &mut cs.namespace(|| "letrec_cont_is_letrec_cont"),
            ContTag::LetRec.to_field(),
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

        let continuation_is_tail = letrec_cont.alloc_tag_equal(
            &mut cs.namespace(|| "continuation is tail"),
            ContTag::Tail.to_field(),
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
        let mut cs = cs.namespace(|| "Unop new_cont2");
        let unop_op1 = AllocatedPtr::by_index(0, &continuation_components);
        let other_unop_continuation = AllocatedContPtr::by_index(1, &continuation_components);

        let op1_is_emit =
            unop_op1.alloc_tag_equal(&mut cs.namespace(|| "op1_is_emit"), Op1::Emit.to_field())?;
        let op1_is_eval =
            unop_op1.alloc_tag_equal(&mut cs.namespace(|| "op1_is_eval"), Op1::Eval.to_field())?;

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

        let result_is_cons = result.is_cons(&mut cs.namespace(|| "result_is_cons"))?;
        let result_is_str = result.is_str(&mut cs.namespace(|| "result_is_str"))?;

        let result_is_nil = result.is_nil(&mut cs.namespace(|| "result_is_nil"), g)?;

        let car_cdr_is_valid = or!(cs, &result_is_cons, &result_is_str, &result_is_nil)?;

        let op1_is_car =
            unop_op1.alloc_tag_equal(&mut cs.namespace(|| "op1_is_car"), Op1::Car.to_field())?;
        let op1_is_cdr =
            unop_op1.alloc_tag_equal(&mut cs.namespace(|| "op1_is_cdr"), Op1::Cdr.to_field())?;
        let op1_is_car_or_cdr = or!(cs, &op1_is_car, &op1_is_cdr)?;
        let car_cdr_is_invalid = and!(cs, &op1_is_car_or_cdr, &car_cdr_is_valid.not())?;

        let op1_is_comm =
            unop_op1.alloc_tag_equal(&mut cs.namespace(|| "op1_is_comm"), Op1::Comm.to_field())?;
        let op1_is_num =
            unop_op1.alloc_tag_equal(&mut cs.namespace(|| "op1_is_num"), Op1::Num.to_field())?;
        let op1_is_char =
            unop_op1.alloc_tag_equal(&mut cs.namespace(|| "op1_is_char"), Op1::Char.to_field())?;
        let op1_is_open =
            unop_op1.alloc_tag_equal(&mut cs.namespace(|| "op1_is_open"), Op1::Open.to_field())?;
        let op1_is_secret = unop_op1.alloc_tag_equal(
            &mut cs.namespace(|| "op1_is_secret"),
            Op1::Secret.to_field(),
        )?;
        let op1_is_u64 =
            unop_op1.alloc_tag_equal(&mut cs.namespace(|| "op1_is_u64"), Op1::U64.to_field())?;

        let tag_is_char = result.alloc_tag_equal(
            &mut cs.namespace(|| "result_is_char"),
            ExprTag::Char.to_field(),
        )?;
        let tag_is_num = result.alloc_tag_equal(
            &mut cs.namespace(|| "result_is_num"),
            ExprTag::Num.to_field(),
        )?;
        let tag_is_comm = result.alloc_tag_equal(
            &mut cs.namespace(|| "result_is_comm"),
            ExprTag::Comm.to_field(),
        )?;
        let tag_is_u64 = result.alloc_tag_equal(
            &mut cs.namespace(|| "result_is_u64"),
            ExprTag::U64.to_field(),
        )?;

        let tag_is_num_or_comm = or!(cs, &tag_is_num, &tag_is_comm)?;
        let tag_is_num_or_char = or!(cs, &tag_is_num, &tag_is_char)?;
        let tag_is_num_or_comm_or_char = or!(cs, &tag_is_num_or_comm, &tag_is_char)?;
        let tag_is_num_or_comm_or_char_or_u64 = or!(cs, &tag_is_num_or_comm_or_char, &tag_is_u64)?;

        let comm_invalid_tag_error = and!(cs, &tag_is_num_or_comm.not(), &op1_is_comm)?;
        let num_invalid_tag_error =
            and!(cs, &tag_is_num_or_comm_or_char_or_u64.not(), &op1_is_num)?;
        let char_invalid_tag_error = and!(cs, &tag_is_num_or_char.not(), &op1_is_char)?;
        let open_invalid_tag_error = and!(cs, &tag_is_num_or_comm.not(), &op1_is_open)?;
        let secret_invalid_tag_error = and!(cs, &tag_is_num_or_comm.not(), &op1_is_secret)?;
        let u64_invalid_tag_error = and!(cs, &op1_is_u64, &tag_is_num.not())?;

        let any_error = or!(
            cs,
            &car_cdr_is_invalid,
            &comm_invalid_tag_error,
            &num_invalid_tag_error,
            &char_invalid_tag_error,
            &open_invalid_tag_error,
            &secret_invalid_tag_error,
            &u64_invalid_tag_error
        )?;

        let the_expr = pick_ptr!(cs, &any_error, result, &unop_val)?;

        let the_env = pick_ptr!(cs, &op1_is_eval, &g.nil_ptr, env)?;

        let the_cont = AllocatedContPtr::pick(
            &mut cs.namespace(|| "the_cont"),
            &any_error,
            &g.error_ptr_cont,
            &unop_continuation,
        )?;

        let make_thunk_num = boolean_to_num(
            &mut cs.namespace(|| "pick make_thunk_num"),
            &op1_is_eval.not(),
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
    let newer_cont2_not_dummy_ = equal_const!(cs, &newer_cont2_not_dummy_result_num, F::one())?;
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

fn get_named_components<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    cont_ptr: &AllocatedContPtr<F>,
    name: ContName,
    allocated_cont_witness: &mut AllocatedContWitness<F>,
    not_dummy: &Boolean,
    _store: &Store<F>,
) -> Result<(AllocatedNum<F>, Vec<AllocatedNum<F>>), SynthesisError> {
    let expect_dummy = !not_dummy.get_value().unwrap_or(false);

    let (allocated_cont_components, allocated_cont_hash) =
        allocated_cont_witness.get_components(name, expect_dummy);

    implies_equal!(cs, not_dummy, cont_ptr.hash(), &allocated_cont_hash);

    Ok((allocated_cont_hash, allocated_cont_components))
}

// This function helps to enforce a  comparison relation between a and b.
// It receives as input argument `diff`, which must be constrained to be
// equal to the difference (a - b).
// The last argument is `op2`, which can be <, <=, >, >=
pub fn comparison_helper<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
    diff: &AllocatedNum<F>,
    op2: &AllocatedNum<F>,
    c: &NamedConstants<F>,
) -> Result<(Boolean, AllocatedPtr<F>, Boolean), SynthesisError> {
    let a_is_negative = allocate_is_negative(&mut cs.namespace(|| "enforce a is negative"), a)?;
    let b_is_negative = allocate_is_negative(&mut cs.namespace(|| "enforce b is negative"), b)?;
    let diff_is_negative =
        allocate_is_negative(&mut cs.namespace(|| "enforce diff is negative"), diff)?;

    let diff_is_zero = alloc_is_zero(&mut cs.namespace(|| "diff is zero"), diff)?;

    let diff_is_not_positive = or(
        &mut cs.namespace(|| "diff is not positive"),
        &diff_is_negative,
        &diff_is_zero,
    )?;

    let diff_is_positive = diff_is_not_positive.not();

    let diff_is_not_negative = diff_is_negative.not();

    let not_one_negative_and_other_not_negative = Boolean::xor(
        &mut cs.namespace(|| "not one negative and other not negative"),
        &a_is_negative,
        &b_is_negative,
    )?
    .not();

    let a_negative_and_b_not_negative = Boolean::and(
        &mut cs.namespace(|| "a negative and b not negative"),
        &a_is_negative,
        &b_is_negative.not(),
    )?;

    let alloc_num_diff_is_negative = boolean_to_num(
        &mut cs.namespace(|| "Allocate num for diff_is_negative"),
        &diff_is_negative,
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
        Op2::Less.to_field(),
        &alloc_num_diff_is_negative,
        &g.true_num,
        &g.false_num,
    );
    comp_results.add_clauses_comp(
        Op2::LessEqual.to_field(),
        &alloc_num_diff_is_not_positive,
        &g.true_num,
        &g.false_num,
    );
    comp_results.add_clauses_comp(
        Op2::Greater.to_field(),
        &alloc_num_diff_is_positive,
        &g.false_num,
        &g.true_num,
    );
    comp_results.add_clauses_comp(
        Op2::GreaterEqual.to_field(),
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
        op2,
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
        &not_one_negative_and_other_not_negative,
        &comp_val_same_sign_num,
        &comp_val1,
    )?;

    let comp_val_is_zero = alloc_is_zero(&mut cs.namespace(|| "comp_val_is_zero"), &comp_val2)?;

    let comp_val = AllocatedPtr::pick_const(
        &mut cs.namespace(|| "comp_val"),
        &comp_val_is_zero,
        &c.nil.scalar_ptr(),
        &c.t.scalar_ptr(),
    )?;

    Ok((is_comparison_tag, comp_val, diff_is_negative))
}

// Lurk supported uint coercion
#[derive(Copy, Clone)]
pub enum UnsignedInt {
    U32,
    U64,
}

impl UnsignedInt {
    pub fn num_bits(&self) -> u32 {
        match self {
            UnsignedInt::U32 => 32,
            UnsignedInt::U64 => 64,
        }
    }
}

pub fn to_unsigned_integer_helper<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    field_elem: &AllocatedNum<F>,
    field_bn: BigUint,
    field_elem_bits: &[Boolean],
    size: UnsignedInt,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let power_of_two_bn = BigUint::pow(&BigUint::from_u32(2).unwrap(), size.num_bits());

    let (q_bn, r_bn) = field_bn.div_rem(&power_of_two_bn);
    let q_num = allocate_unconstrained_bignum(&mut cs.namespace(|| "q"), q_bn)?;
    let r_num = allocate_unconstrained_bignum(&mut cs.namespace(|| "r"), r_bn)?;
    let pow2_size = match size {
        UnsignedInt::U32 => &g.power2_32_num,
        UnsignedInt::U64 => &g.power2_64_num,
    };

    // field element = pow(2, size).q + r
    linear(
        &mut cs,
        || "product(q,pow(2,size)) + r",
        &q_num,
        pow2_size,
        &r_num,
        field_elem,
    );

    let r_bits = &field_elem_bits[0..size.num_bits() as usize];
    enforce_pack(
        &mut cs.namespace(|| "enforce unsigned pack"),
        r_bits,
        &r_num,
    )?;

    Ok(r_num)
}

// Convert from num to unsigned integers by taking the least significant bits.
// The output is a pair of allocated numbers, where the first one corresponds to
// the u32 coercion, while the second corresponds to the u64 coercion.
pub fn to_unsigned_integers<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    maybe_unsigned: &AllocatedNum<F>,
) -> Result<(AllocatedNum<F>, AllocatedNum<F>), SynthesisError> {
    let field_elem = match maybe_unsigned.get_value() {
        Some(v) => v,
        None => F::zero(), //dummy
    };
    let field_bn = BigUint::from_bytes_le(field_elem.to_repr().as_ref());
    // Since bit decomposition is expensive, we compute it only once here
    let field_elem_bits =
        maybe_unsigned.to_bits_le(&mut cs.namespace(|| "field element bit decomp"))?;

    let r32_num = to_unsigned_integer_helper(
        &mut cs.namespace(|| "enforce u32"),
        g,
        maybe_unsigned,
        field_bn.clone(),
        &field_elem_bits,
        UnsignedInt::U32,
    )?;
    let r64_num = to_unsigned_integer_helper(
        &mut cs.namespace(|| "enforce u64"),
        g,
        maybe_unsigned,
        field_bn,
        &field_elem_bits,
        UnsignedInt::U64,
    )?;

    Ok((r32_num, r64_num))
}

// Convert from num to u64.
pub fn to_u64<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    g: &GlobalAllocations<F>,
    maybe_u64: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let field_elem = maybe_u64.get_value().unwrap_or_else(|| F::zero()); //
    let field_bn = BigUint::from_bytes_le(field_elem.to_repr().as_ref());
    let field_elem_bits = maybe_u64.to_bits_le(&mut cs.namespace(|| "field element bit decomp"))?;

    let r64_num = to_unsigned_integer_helper(
        &mut cs.namespace(|| "enforce u64"),
        g,
        maybe_u64,
        field_bn,
        &field_elem_bits,
        UnsignedInt::U64,
    )?;

    Ok(r64_num)
}

// Enforce div and mod operation for U64. We need to show that
// arg1 = q * arg2 + r, such that 0 <= r < arg2.
pub fn enforce_u64_div_mod<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    cond: Boolean,
    arg1: &AllocatedPtr<F>,
    arg2: &AllocatedPtr<F>,
) -> Result<(AllocatedNum<F>, AllocatedNum<F>), SynthesisError> {
    let arg1_u64 = match arg1.hash().get_value() {
        Some(v) => v.to_u64_unchecked(),
        None => 0, // Blank and Dummy
    };
    let arg2_u64 = match arg2.hash().get_value() {
        Some(v) => v.to_u64_unchecked(),
        None => 0, // Blank and Dummy
    };

    let (q, r) = if arg2_u64 != 0 {
        (arg1_u64 / arg2_u64, arg1_u64 % arg2_u64)
    } else {
        (0, 0) // Dummy
    };

    let alloc_r_num = AllocatedNum::alloc(&mut cs.namespace(|| "r num"), || Ok(F::from_u64(r)))?;
    let alloc_q_num = AllocatedNum::alloc(&mut cs.namespace(|| "q num"), || Ok(F::from_u64(q)))?;
    let alloc_arg1_num = AllocatedNum::alloc(&mut cs.namespace(|| "arg1 num"), || {
        Ok(F::from_u64(arg1_u64))
    })?;
    let alloc_arg2_num = AllocatedNum::alloc(&mut cs.namespace(|| "arg2 num"), || {
        Ok(F::from_u64(arg2_u64))
    })?;

    // a = b * q + r
    let product_u64mod = mul(
        &mut cs.namespace(|| "product(q,arg2)"),
        &alloc_q_num,
        &alloc_arg2_num,
    )?;
    let sum_u64mod = add(
        &mut cs.namespace(|| "sum remainder mod u64"),
        &product_u64mod,
        &alloc_r_num,
    )?;
    let u64mod_decomp = alloc_equal(
        &mut cs.namespace(|| "check u64 mod decomposition"),
        &sum_u64mod,
        &alloc_arg1_num,
    )?;
    let b_is_zero = alloc_is_zero(&mut cs.namespace(|| "b is zero"), arg2.hash())?;
    let b_is_not_zero_and_cond = Boolean::and(
        &mut cs.namespace(|| "b is not zero and cond"),
        &b_is_zero.not(),
        &cond,
    )?;
    enforce_implication(
        &mut cs.namespace(|| "enforce u64 mod decomposition"),
        &b_is_not_zero_and_cond,
        &u64mod_decomp,
    )?;

    enforce_less_than_bound(
        &mut cs.namespace(|| "remainder in range b"),
        cond,
        alloc_r_num.clone(),
        alloc_arg2_num,
    )?;

    Ok((alloc_q_num, alloc_r_num))
}

// Given that `cond` is satisfied, enforce the num < bound.
// This is done by proving (bound - num) is positive.
// `num` and `bound` must be a positive field element.
// `cond` is a Boolean condition that enforces the validation iff it is True.
pub fn enforce_less_than_bound<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    cond: Boolean,
    num: AllocatedNum<F>,
    bound: AllocatedNum<F>,
) -> Result<(), SynthesisError> {
    let diff_bound_num = sub(&mut cs.namespace(|| "bound minus num"), &bound, &num)?;

    let diff_bound_num_is_negative = allocate_is_negative(
        &mut cs.namespace(|| "diff bound num is negative"),
        &diff_bound_num,
    )?;

    enforce_implication(
        &mut cs.namespace(|| "enforce u64 range"),
        &cond,
        &diff_bound_num_is_negative.not(),
    )
}

// ATTENTION:
// Convert from bn to num. This allocation is NOT constrained here.
// In the circuit we use it to prove u64 decomposition, since using bn
// we have division with remainder, which is used to find the quotient
// after dividing by 2ˆ64. Therefore we constrain this relation afterwards.
pub fn allocate_unconstrained_bignum<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    bn: BigUint,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let bytes_le = bn.to_bytes_le();
    let mut bytes_padded = [0u8; 32];
    bytes_padded[0..bytes_le.len()].copy_from_slice(&bytes_le);
    let ff = F::from_bytes(&bytes_padded).unwrap();
    let num = AllocatedNum::alloc(&mut cs.namespace(|| "num"), || Ok(ff)).unwrap();
    Ok(num)
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
    let maybe_cons_is_nil = maybe_cons.is_nil(&mut cs.namespace(|| "maybe_cons_is_nil"), g)?;

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

    let var_or_binding_is_cons =
        var_or_binding.is_cons(&mut cs.namespace(|| "var_or_binding_is_cons"))?;

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

    let is_sym = var_or_binding.is_sym(&mut cs.namespace(|| "var_or_binding is sym"))?;
    let is_nil = var_or_binding.is_nil(&mut cs.namespace(|| "var_or_binding is nil"), g)?;
    let is_sym_or_nil = or!(cs, &is_sym, &is_nil)?;
    let is_cons = var_or_binding_is_cons;

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
        out += &format!("{i}: {input}\n");
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
    use crate::circuit::circuit_frame::constraints::{popcount, sub};
    use crate::eval::{empty_sym_env, Evaluable, IO};
    use crate::proof::Provable;
    use crate::proof::{groth16::Groth16Prover, Prover};
    use crate::store::Store;
    use bellperson::groth16;
    use bellperson::util_cs::{
        metric_cs::MetricCS, test_cs::TestConstraintSystem, Comparable, Delta,
    };
    use blstrs::{Bls12, Scalar as Fr};
    use ff::{Field, PrimeField};
    use pairing_lib::Engine;

    const DEFAULT_REDUCTION_COUNT: usize = 1;

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

        let public_params = Groth16Prover::create_groth_params(DEFAULT_REDUCTION_COUNT).unwrap();
        let groth_prover = Groth16Prover::new(DEFAULT_REDUCTION_COUNT);
        let groth_params = &public_params.0;

        let vk = &groth_params.vk;
        let pvk = groth16::prepare_verifying_key(vk);

        store.hydrate_scalar_cache();
        let test_with_output = |output: IO<Fr>, expect_success: bool, store: &Store<Fr>| {
            let mut cs = TestConstraintSystem::new();

            let mut cs_blank = MetricCS::<Fr>::new();
            let blank_multiframe =
                MultiFrame::<<Bls12 as Engine>::Fr, _, _>::blank(DEFAULT_REDUCTION_COUNT);

            blank_multiframe
                .synthesize(&mut cs_blank)
                .expect("failed to synthesize");

            let multiframes = MultiFrame::from_frames(
                DEFAULT_REDUCTION_COUNT,
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
            assert_eq!(12096, cs.num_constraints());
            assert_eq!(13, cs.num_inputs());
            assert_eq!(11751, cs.aux().len());

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
        store.hydrate_scalar_cache();

        let test_with_output = |output: IO<Fr>, expect_success: bool, store: &Store<Fr>| {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let frame = Frame {
                input,
                output,
                i: 0,
                witness,
            };

            MultiFrame::<<Bls12 as Engine>::Fr, _, _>::from_frames(
                DEFAULT_REDUCTION_COUNT,
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
        store.hydrate_scalar_cache();

        let test_with_output = |output: IO<Fr>, expect_success: bool, store: &Store<Fr>| {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let frame = Frame {
                input,
                output,
                i: 0,
                witness,
            };

            MultiFrame::<<Bls12 as Engine>::Fr, _, _>::from_frames(
                DEFAULT_REDUCTION_COUNT,
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

        store.hydrate_scalar_cache();

        let test_with_output = |output: IO<Fr>, expect_success: bool, store: &Store<Fr>| {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let frame = Frame {
                input,
                output,
                i: 0,
                witness,
            };

            MultiFrame::<<Bls12 as Engine>::Fr, _, _>::from_frames(
                DEFAULT_REDUCTION_COUNT,
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

        store.hydrate_scalar_cache();

        let test_with_output = |output, expect_success, store: &mut Store<Fr>| {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let frame = Frame {
                input,
                output,
                i: 0,
                witness,
            };

            MultiFrame::<<Bls12 as Engine>::Fr, _, _>::from_frames(
                DEFAULT_REDUCTION_COUNT,
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

    #[test]
    fn test_enforce_comparison() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        s.hydrate_scalar_cache();

        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();
        let a = s.num(42);
        let alloc_a = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "a"), s, || Ok(&a)).unwrap();
        let b = s.num(43);
        let alloc_b = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "b"), s, || Ok(&b)).unwrap();
        let diff = sub(&mut cs.namespace(|| "sub"), alloc_a.hash(), alloc_b.hash()).unwrap();

        let (_, comp_val, _) = comparison_helper(
            &mut cs.namespace(|| "enforce u64 div mod"),
            &g,
            alloc_a.hash(),
            alloc_b.hash(),
            &diff,
            &g.op2_less_tag,
            s.get_constants(),
        )
        .unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(comp_val.hash().get_value(), g.t_ptr.hash().get_value());
    }

    #[test]
    fn test_u64_op() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();

        let a = s.num(42);
        let alloc_a = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "a"), s, || Ok(&a)).unwrap();

        let a_u64 = to_u64(&mut cs.namespace(|| "u64 op"), &g, alloc_a.hash()).unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(a_u64.get_value(), Some(Fr::from_u64(42)));
    }

    #[test]
    fn test_u64_op_coercion() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();
        let alloc_pow2_64 = AllocatedPtr::from_parts(&g.num_tag, &g.power2_64_num);

        let a_u64 = to_u64(&mut cs.namespace(|| "u64 op"), &g, alloc_pow2_64.hash()).unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(a_u64.get_value(), Some(Fr::from_u64(0)));
    }

    #[test]
    fn test_enforce_less_than_bound_corner_case() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let alloc_most_positive =
            AllocatedNum::alloc(&mut cs.namespace(|| "most positive"), || {
                Ok(Fr::most_positive())
            })
            .unwrap();
        let alloc_num =
            AllocatedNum::alloc(&mut cs.namespace(|| "num"), || Ok(Fr::from_u64(42))).unwrap();
        let cond = Boolean::Constant(true);

        let res = enforce_less_than_bound(
            &mut cs.namespace(|| "enforce less than bound"),
            cond,
            alloc_num,
            alloc_most_positive,
        );
        assert!(res.is_ok());
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_enforce_less_than_bound() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let alloc_num =
            AllocatedNum::alloc(&mut cs.namespace(|| "num"), || Ok(Fr::from_u64(42))).unwrap();
        let alloc_bound =
            AllocatedNum::alloc(&mut cs.namespace(|| "bound"), || Ok(Fr::from_u64(43))).unwrap();
        let cond = Boolean::Constant(true);

        let res = enforce_less_than_bound(
            &mut cs.namespace(|| "enforce less than bound"),
            cond,
            alloc_num,
            alloc_bound,
        );
        assert!(res.is_ok());
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_enforce_less_than_bound_negative() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let alloc_num =
            AllocatedNum::alloc(&mut cs.namespace(|| "num"), || Ok(Fr::from_u64(43))).unwrap();
        let alloc_bound =
            AllocatedNum::alloc(&mut cs.namespace(|| "bound"), || Ok(Fr::from_u64(42))).unwrap();
        let cond = Boolean::Constant(true);

        let res = enforce_less_than_bound(
            &mut cs.namespace(|| "enforce less than bound"),
            cond,
            alloc_num,
            alloc_bound,
        );
        assert!(res.is_ok());
        assert!(!cs.is_satisfied());
    }

    #[test]
    fn test_enforce_u64_div_mod() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let a = s.num(42);
        let alloc_a = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "a"), s, || Ok(&a)).unwrap();
        let b = s.num(5);
        let alloc_b = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "b"), s, || Ok(&b)).unwrap();

        let cond = Boolean::Constant(true);

        let (q, r) = enforce_u64_div_mod(
            &mut cs.namespace(|| "enforce u64 div mod"),
            cond,
            &alloc_a,
            &alloc_b,
        )
        .unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(q.get_value(), Some(Fr::from_u64(8)));
        assert_eq!(r.get_value(), Some(Fr::from_u64(2)));
    }

    #[test]
    fn test_enforce_u64_div_mod_zero() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        let a = s.num(42);
        let alloc_a = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "a"), s, || Ok(&a)).unwrap();
        let b = s.num(0);
        let alloc_b = AllocatedPtr::alloc_ptr(&mut cs.namespace(|| "b"), s, || Ok(&b)).unwrap();

        let cond = Boolean::Constant(true);

        let (q, r) = enforce_u64_div_mod(
            &mut cs.namespace(|| "enforce u64 div mod"),
            cond,
            &alloc_a,
            &alloc_b,
        )
        .unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(q.get_value(), Some(Fr::from_u64(0)));
        assert_eq!(r.get_value(), Some(Fr::from_u64(0)));
    }

    #[test]
    fn test_enforce_popcount() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();

        for x in 0..128 {
            let a = s.num(x);
            let alloc_a =
                AllocatedPtr::alloc_ptr(&mut cs.namespace(|| x.to_string()), s, || Ok(&a)).unwrap();
            let bits = alloc_a
                .hash()
                .to_bits_le(&mut cs.namespace(|| format!("bits_{x}")))
                .unwrap();
            let popcount_result = s.num(x.count_ones() as u64);
            let alloc_popcount = AllocatedPtr::alloc_ptr(
                &mut cs.namespace(|| format!("alloc popcount {x}")),
                s,
                || Ok(&popcount_result),
            )
            .unwrap();

            popcount(
                &mut cs.namespace(|| format!("popcount {x}")),
                &bits,
                alloc_popcount.hash(),
            )
            .unwrap();
        }

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_to_u32() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();

        let a = Fr::from_u64(2);
        let v = a + Fr::pow_vartime(&Fr::from_u64(2), [32]);
        let field_bn = BigUint::from_bytes_le(v.to_repr().as_ref());

        let a_plus_power2_32_num =
            AllocatedNum::alloc(&mut cs.namespace(|| "pow(2, 32) + 2"), || Ok(v)).unwrap();

        let bits = a_plus_power2_32_num
            .to_bits_le(&mut cs.namespace(|| "bits"))
            .unwrap();

        let res = to_unsigned_integer_helper(
            &mut cs,
            &g,
            &a_plus_power2_32_num,
            field_bn,
            &bits,
            UnsignedInt::U32,
        )
        .unwrap();

        assert_eq!(a, res.get_value().unwrap());
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_to_u64() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        let g = GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), s).unwrap();

        let a = Fr::from_u64(2);
        let v = a + Fr::pow_vartime(&Fr::from_u64(2), [64]);
        let field_bn = BigUint::from_bytes_le(v.to_repr().as_ref());

        let a_plus_power2_64_num =
            AllocatedNum::alloc(&mut cs.namespace(|| "pow(2, 64) + 2"), || Ok(v)).unwrap();

        let bits = a_plus_power2_64_num
            .to_bits_le(&mut cs.namespace(|| "bits"))
            .unwrap();

        let res = to_unsigned_integer_helper(
            &mut cs,
            &g,
            &a_plus_power2_64_num,
            field_bn,
            &bits,
            UnsignedInt::U64,
        )
        .unwrap();

        assert_eq!(a, res.get_value().unwrap());
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_enforce_pack() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let a_num =
            AllocatedNum::alloc(&mut cs.namespace(|| "a num"), || Ok(Fr::from_u64(42))).unwrap();
        let bits = a_num.to_bits_le(&mut cs.namespace(|| "bits")).unwrap();
        enforce_pack(&mut cs, &bits, &a_num).unwrap();
        assert!(cs.is_satisfied());
    }
}
