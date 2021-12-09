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

use crate::gadgets::case::{case, multi_case, CaseClause, CaseConstraint};

use crate::data::{
    fr_from_u64, BaseContinuationTag, Continuation, Expression, Op1, Op2, Rel2, Store, Tag, Tagged,
    TaggedHash, Thunk, POSEIDON_CONSTANTS_4, POSEIDON_CONSTANTS_6, POSEIDON_CONSTANTS_8,
};
use crate::eval::{Control, Frame, Witness, IO};
use crate::gadgets::constraints::{
    self, alloc_equal, alloc_is_zero, enforce_implication, equal, or, pick,
};
use crate::gadgets::data::{allocate_constant, pick_tagged_hash, AllocatedTaggedHash};

pub const DUMMY_RNG_SEED: [u8; 16] = [
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
];

pub trait Provable {
    fn public_inputs(&self) -> Vec<Fr>;
}

pub struct Proof<F: Provable, E: Engine> {
    _frame: F,
    groth16_proof: groth16::Proof<E>,
}

impl<W> Provable for Frame<IO<W>> {
    fn public_inputs(&self) -> Vec<Fr> {
        let mut inputs: Vec<Fr> = Vec::with_capacity(10);

        if let Some(input) = self.input {
            inputs.extend(input.public_inputs());
        }
        if let Some(output) = self.output {
            inputs.extend(output.public_inputs());
        }
        if let Some(initial) = self.initial {
            inputs.extend(initial.public_inputs());
        }
        if let Some(i) = self.i {
            inputs.push(fr_from_u64(i as u64));
        }

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

impl Frame<IO<Witness>> {
    fn dummy() -> Self {
        Self {
            input: None,
            output: None,
            initial: None,
            i: None,
        }
    }

    fn frame_groth_params(self) -> Result<groth16::Parameters<Bls12>, SynthesisError> {
        let rng = &mut XorShiftRng::from_seed(DUMMY_RNG_SEED);
        groth16::generate_random_parameters::<Bls12, _, _>(self, rng)
    }

    fn groth_params() -> Result<groth16::Parameters<Bls12>, SynthesisError> {
        Self::dummy().frame_groth_params()
    }
}

impl Frame<IO<Witness>> {
    pub fn generate_groth16_proof<R: RngCore>(
        self,
        rng: &mut R,
    ) -> Result<groth16::Proof<Bls12>, SynthesisError> {
        let params = Frame::<IO<Witness>>::groth_params()?;

        groth16::create_random_proof(self, &params, rng)
    }

    pub fn verify_groth16_proof(
        p: Proof<Frame<IO<Witness>>, Bls12>,
        f: Frame<IO<Witness>>,
    ) -> Result<bool, SynthesisError> {
        let groth_params = Frame::groth_params()?;
        let vk = groth_params.vk;
        let pvk = groth16::prepare_verifying_key(&vk);
        let inputs = f.public_inputs();

        verify_proof(&pvk, &p.groth16_proof, &inputs)
    }
}

fn bind_input<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    expr: &Option<Expression>,
) -> Result<AllocatedTaggedHash, SynthesisError> {
    let tagged_hash = expr.map(|e| e.tagged_hash());
    let tag = AllocatedNum::alloc(cs.namespace(|| "tag"), || {
        tagged_hash
            .map(|th| th.tag)
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    tag.inputize(cs.namespace(|| "tag input"))?;

    let hash = AllocatedNum::alloc(cs.namespace(|| "hash"), || {
        tagged_hash
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
        cont.map(|c| c.get_continuation_tag().cont_tag_fr())
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    tag.inputize(cs.namespace(|| "continuation tag input"))?;

    let hash = AllocatedNum::alloc(cs.namespace(|| "continuation hash"), || {
        cont.map(|c| c.get_hash())
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

impl Circuit<Fr> for Frame<IO<Witness>> {
    fn synthesize<CS: ConstraintSystem<Fr>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let witness = if let Some(output) = self.output {
            output.witness.clone().unwrap()
        } else {
            Witness::default()
        };

        ////////////////////////////////////////////////////////////////////////////////
        // Bind public inputs.
        //
        // The frame's input:
        let input_expr = bind_input(
            &mut cs.namespace(|| "input expression"),
            &self.input.map(|input| input.expr),
        )?;

        let input_env = bind_input(
            &mut cs.namespace(|| "input env"),
            &self.input.map(|input| input.env),
        )?;

        let input_cont = bind_input_cont(
            &mut cs.namespace(|| "input cont"),
            &self.input.map(|input| input.cont),
        )?;

        // The frame's output:
        let output_expr = bind_input(
            &mut cs.namespace(|| "output expression"),
            &self.output.map(|output| output.expr),
        )?;

        let output_env = bind_input(
            &mut cs.namespace(|| "output env"),
            &self.output.map(|output| output.env),
        )?;

        let output_cont = bind_input_cont(
            &mut cs.namespace(|| "output cont"),
            &self.output.map(|output| output.cont),
        )?;

        // The initial input to the IVC computation.
        let initial_expr = bind_input(
            &mut cs.namespace(|| "initial expression"),
            &self.initial.map(|initial| initial.expr),
        )?;

        let initial_env = bind_input(
            &mut cs.namespace(|| "initial env"),
            &self.initial.map(|initial| initial.env),
        )?;

        let initial_cont = bind_input_cont(
            &mut cs.namespace(|| "initial cont"),
            &self.initial.map(|initial| initial.cont),
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
            &self.output.and_then(|output| output.witness),
        )?;

        output_expr.enforce_equal(&mut cs.namespace(|| "output expr is correct"), &new_expr);
        output_env.enforce_equal(&mut cs.namespace(|| "output env is correct"), &new_env);
        output_cont.enforce_equal(&mut cs.namespace(|| "output cont is correct"), &new_cont);

        Ok(())
    }
}

struct GlobalAllocations {
    terminal_tagged_hash: AllocatedTaggedHash,
    outermost_tagged_hash: AllocatedTaggedHash,
    error_tagged_hash: AllocatedTaggedHash,
    dummy_tagged_hash: AllocatedTaggedHash,
    nil_tagged_hash: AllocatedTaggedHash,
    t_tagged_hash: AllocatedTaggedHash,
    lambda_tagged_hash: AllocatedTaggedHash,
    quote_tagged_hash: AllocatedTaggedHash,
    dummy_arg_tagged_hash: AllocatedTaggedHash,
    dummy_value: AllocatedNum<Fr>,
    nil_tag: AllocatedNum<Fr>,
    sym_tag: AllocatedNum<Fr>,
    thunk_tag: AllocatedNum<Fr>,
    cons_tag: AllocatedNum<Fr>,
    num_tag: AllocatedNum<Fr>,
    fun_tag: AllocatedNum<Fr>,
    letstar_cont_tag: AllocatedNum<Fr>,
    letrecstar_cont_tag: AllocatedNum<Fr>,
    lookup_cont_tag: AllocatedNum<Fr>,
    tail_cont_tag: AllocatedNum<Fr>,
    call_cont_tag: AllocatedNum<Fr>,
    call2_cont_tag: AllocatedNum<Fr>,
    unop_cont_tag: AllocatedNum<Fr>,
    binop_cont_tag: AllocatedNum<Fr>,
    relop_cont_tag: AllocatedNum<Fr>,
    binop2_cont_tag: AllocatedNum<Fr>,
    relop2_cont_tag: AllocatedNum<Fr>,
    if_cont_tag: AllocatedNum<Fr>,
    op1_car_tag: AllocatedNum<Fr>,
    op1_cdr_tag: AllocatedNum<Fr>,
    op1_atom_tag: AllocatedNum<Fr>,
    op2_cons_tag: AllocatedNum<Fr>,
    op2_sum_tag: AllocatedNum<Fr>,
    op2_diff_tag: AllocatedNum<Fr>,
    op2_product_tag: AllocatedNum<Fr>,
    op2_quotient_tag: AllocatedNum<Fr>,
    rel2_equal_tag: AllocatedNum<Fr>,
    rel2_numequal_tag: AllocatedNum<Fr>,
    true_num: AllocatedNum<Fr>,
    false_num: AllocatedNum<Fr>,

    default: AllocatedNum<Fr>,

    destructured_thunk_hash: AllocatedNum<Fr>,
    destructured_thunk_value: AllocatedTaggedHash,
    destructured_thunk_continuation: AllocatedTaggedHash,
}

impl GlobalAllocations {
    fn new<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        witness: &Option<Witness>,
    ) -> Result<Self, SynthesisError> {
        let terminal_tagged_hash = Continuation::Terminal
            .allocate_constant_tagged_hash(&mut cs.namespace(|| "terminal continuation"))?;

        let outermost_tagged_hash = Continuation::Outermost
            .allocate_constant_tagged_hash(&mut cs.namespace(|| "outermost continuation"))?;

        let error_tagged_hash = Continuation::Error
            .allocate_constant_tagged_hash(&mut cs.namespace(|| "error continuation"))?;

        let dummy_tagged_hash = Continuation::Dummy
            .allocate_constant_tagged_hash(&mut cs.namespace(|| "dummy continuation"))?;

        let nil_tagged_hash =
            Expression::Nil.allocate_constant_tagged_hash(&mut cs.namespace(|| "nil"))?;

        let t_tagged_hash =
            Expression::read_sym("T").allocate_constant_tagged_hash(&mut cs.namespace(|| "T"))?;

        let lambda_tagged_hash = Expression::read_sym("LAMBDA")
            .allocate_constant_tagged_hash(&mut cs.namespace(|| "LAMBDA"))?;

        let quote_tagged_hash = Expression::read_sym("QUOTE")
            .allocate_constant_tagged_hash(&mut cs.namespace(|| "QUOTE"))?;

        let dummy_arg_tagged_hash =
            Expression::read_sym("_").allocate_constant_tagged_hash(&mut cs.namespace(|| "_"))?;

        let dummy_value = allocate_constant(&mut cs.namespace(|| "arbitrary dummy"), Fr::zero())?;

        let nil_tag = Tag::Sym.allocate_constant(&mut cs.namespace(|| "nil_tag"))?;
        let sym_tag = Tag::Sym.allocate_constant(&mut cs.namespace(|| "sym_tag"))?;
        let thunk_tag = Tag::Thunk.allocate_constant(&mut cs.namespace(|| "thunk_tag"))?;
        let cons_tag = Tag::Cons.allocate_constant(&mut cs.namespace(|| "cons_tag"))?;
        let num_tag = Tag::Num.allocate_constant(&mut cs.namespace(|| "num_tag"))?;
        let fun_tag = Tag::Fun.allocate_constant(&mut cs.namespace(|| "fun_tag"))?;

        let lookup_cont_tag = BaseContinuationTag::Lookup
            .allocate_constant(&mut cs.namespace(|| "lookup_cont_tag"))?;
        let letstar_cont_tag = BaseContinuationTag::LetStar
            .allocate_constant(&mut cs.namespace(|| "letstar_cont_tag"))?;
        let letrecstar_cont_tag = BaseContinuationTag::LetStar
            .allocate_constant(&mut cs.namespace(|| "letrecstar_cont_tag"))?;
        let tail_cont_tag =
            BaseContinuationTag::Tail.allocate_constant(&mut cs.namespace(|| "tail_cont_tag"))?;
        let call_cont_tag =
            BaseContinuationTag::Call.allocate_constant(&mut cs.namespace(|| "call_cont_tag"))?;
        let call2_cont_tag =
            BaseContinuationTag::Call2.allocate_constant(&mut cs.namespace(|| "call2_cont_tag"))?;
        let unop_cont_tag =
            BaseContinuationTag::Unop.allocate_constant(&mut cs.namespace(|| "unop_cont_tag"))?;
        let binop_cont_tag =
            BaseContinuationTag::Binop.allocate_constant(&mut cs.namespace(|| "binop_cont_tag"))?;
        let relop_cont_tag =
            BaseContinuationTag::Relop.allocate_constant(&mut cs.namespace(|| "relop_cont_tag"))?;
        let binop2_cont_tag = BaseContinuationTag::Binop2
            .allocate_constant(&mut cs.namespace(|| "binop2_cont_tag"))?;
        let relop2_cont_tag = BaseContinuationTag::Relop2
            .allocate_constant(&mut cs.namespace(|| "relop2_cont_tag"))?;
        let if_cont_tag =
            BaseContinuationTag::If.allocate_constant(&mut cs.namespace(|| "if_cont_tag"))?;
        let op1_car_tag = Op1::Car.allocate_constant(&mut cs.namespace(|| "op1_car_tag"))?;
        let op1_cdr_tag = Op1::Cdr.allocate_constant(&mut cs.namespace(|| "op1_cdr_tag"))?;
        let op1_atom_tag = Op1::Atom.allocate_constant(&mut cs.namespace(|| "op1_atom_tag"))?;
        let op2_cons_tag = Op2::Cons.allocate_constant(&mut cs.namespace(|| "op2_cons_tag"))?;
        let op2_sum_tag = Op2::Sum.allocate_constant(&mut cs.namespace(|| "op2_sum_tag"))?;
        let op2_diff_tag = Op2::Diff.allocate_constant(&mut cs.namespace(|| "op2_diff_tag"))?;
        let op2_product_tag =
            Op2::Product.allocate_constant(&mut cs.namespace(|| "op2_product_tag"))?;
        let op2_quotient_tag =
            Op2::Quotient.allocate_constant(&mut cs.namespace(|| "op2_quotient_tag"))?;
        let rel2_numequal_tag =
            AllocatedNum::alloc(&mut cs.namespace(|| "relop2_numequal_tag"), || {
                Ok(Rel2::NumEqual.fr())
            })?;
        let rel2_equal_tag = AllocatedNum::alloc(&mut cs.namespace(|| "relop2_equal_tag"), || {
            Ok(Rel2::Equal.fr())
        })?;
        let true_num = allocate_constant(&mut cs.namespace(|| "true"), Fr::one())?;
        let false_num = allocate_constant(&mut cs.namespace(|| "false"), Fr::zero())?;

        // NOTE: The choice of zero is significant.
        // For example, TaggedHash::default() has both tag and hash of zero.
        let default = allocate_constant(&mut cs.namespace(|| "default"), Fr::zero())?;

        let maybe_thunk = witness.and_then(|w| w.destructured_thunk.clone());
        let (destructured_thunk_hash, destructured_thunk_value, destructured_thunk_continuation) =
            allocate_thunk_components(
                &mut cs.namespace(|| "allocate thunk components"),
                &maybe_thunk,
            )?;

        Ok(Self {
            terminal_tagged_hash,
            outermost_tagged_hash,
            error_tagged_hash,
            dummy_tagged_hash,
            nil_tagged_hash,
            dummy_value,
            nil_tag,
            t_tagged_hash,
            lambda_tagged_hash,
            quote_tagged_hash,
            dummy_arg_tagged_hash,
            sym_tag,
            thunk_tag,
            cons_tag,
            num_tag,
            fun_tag,
            lookup_cont_tag,
            letstar_cont_tag,
            letrecstar_cont_tag,
            tail_cont_tag,
            call_cont_tag,
            call2_cont_tag,
            unop_cont_tag,
            binop_cont_tag,
            relop_cont_tag,
            binop2_cont_tag,
            relop2_cont_tag,
            if_cont_tag,
            op1_car_tag,
            op1_cdr_tag,
            op1_atom_tag,
            op2_cons_tag,
            op2_sum_tag,
            op2_diff_tag,
            op2_product_tag,
            op2_quotient_tag,
            rel2_equal_tag,
            rel2_numequal_tag,
            true_num,
            false_num,
            default,

            destructured_thunk_hash,
            destructured_thunk_value,
            destructured_thunk_continuation,
        })
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
    let global_allocations =
        GlobalAllocations::new(&mut cs.namespace(|| "global_allocations"), witness)?;

    let mut result_expr_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_expr_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_env_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_env_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_cont_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_cont_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_make_thunk_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_invoke_continuation_clauses: Vec<CaseClause<Fr>> = Vec::new();

    let mut add_clauses = |key,
                           (
        result_expr,
        result_env,
        result_cont,
        result_make_thunk,
        result_invoke_continuation,
    ): (
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedTaggedHash,
        AllocatedNum<Fr>,
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

        add_clause(&mut result_make_thunk_clauses, result_make_thunk);
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
                cont.clone(),
                expr.clone(),
                env.clone(),
                global_allocations.true_num.clone(),
                global_allocations.false_num.clone(),
            ),
        );

        add_clauses(
            Tag::Num.fr(),
            (
                cont.clone(),
                expr.clone(),
                env.clone(),
                global_allocations.true_num.clone(),
                global_allocations.false_num.clone(),
            ),
        );

        add_clauses(
            Tag::Fun.fr(),
            (
                cont.clone(),
                expr.clone(),
                env.clone(),
                global_allocations.true_num.clone(),
                global_allocations.false_num.clone(),
            ),
        );
    }

    {
        let thunk_continuation = global_allocations.destructured_thunk_continuation.clone();
        let thunk_value = global_allocations.destructured_thunk_value.clone();
        let thunk_hash = global_allocations.destructured_thunk_hash.clone();

        // Enforce (expr.tag == thunk_tag) implies (thunk_hash == expr.hash).
        let expr_is_a_thunk = constraints::alloc_equal(
            &mut cs.namespace(|| "expr.tag == thunk_tag"),
            &expr.tag,
            &global_allocations.thunk_tag,
        )?;
        let expr_is_the_thunk = constraints::alloc_equal(
            &mut cs.namespace(|| "thunk_hash == expr.hash"),
            &thunk_hash,
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
                thunk_continuation,
                thunk_value,
                env.clone(),
                global_allocations.false_num.clone(), // Is this okay? Make sure the case of make_thunk called by invoke_continuation works.
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
        let (result, env, cont, make_thunk) = eval_sym(
            &mut cs.namespace(|| "eval Sym"),
            expr,
            env,
            cont,
            &eval_sym_not_dummy,
            witness,
            &global_allocations,
        )?;

        add_clauses(
            Tag::Sym.fr(),
            (
                result,
                env,
                cont,
                make_thunk,
                global_allocations.false_num.clone(),
            ),
        );
    }

    {
        let eval_cons_not_dummy = alloc_equal(
            &mut cs.namespace(|| "eval_cons_not_dummy"),
            &expr.tag,
            &global_allocations.cons_tag,
        )?;
        let (result, env, cont, make_thunk) = eval_cons(
            &mut cs.namespace(|| "eval Cons"),
            expr,
            env,
            cont,
            &eval_cons_not_dummy,
            witness,
            &global_allocations,
        )?;

        add_clauses(
            Tag::Cons.fr(),
            (
                result,
                env,
                cont,
                make_thunk,
                global_allocations.false_num.clone(),
            ),
        );
    }

    let mut all_clauses = vec![
        result_expr_tag_clauses.as_slice(),
        result_expr_hash_clauses.as_slice(),
        result_env_tag_clauses.as_slice(),
        result_env_hash_clauses.as_slice(),
        result_cont_tag_clauses.as_slice(),
        result_cont_hash_clauses.as_slice(),
        result_make_thunk_clauses.as_slice(),
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
            global_allocations.false_num.clone(),
        ],
    )?;

    let first_result_expr = tagged_hash_by_index(0, &case_results);
    let first_result_env = tagged_hash_by_index(1, &case_results);
    let first_result_cont = tagged_hash_by_index(2, &case_results);
    let first_result_make_thunk: &AllocatedNum<Fr> = &case_results[6];
    let first_result_invoke_continuation: &AllocatedNum<Fr> = &case_results[7];

    let invoke_continuation_boolean = Boolean::not(&alloc_is_zero(
        &mut cs.namespace(|| "invoke_continuation_is_zero"),
        first_result_invoke_continuation,
    )?);

    let invoke_continuation_results = invoke_continuation(
        &mut cs.namespace(|| "invoke_continuation-make_thunk"),
        &first_result_expr,
        &first_result_env,
        &first_result_cont,
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
        first_result_make_thunk,
    )?;

    let make_thunk_boolean = Boolean::not(&alloc_is_zero(
        &mut cs.namespace(|| "make_thunk_num is zero"),
        &make_thunk_num,
    )?);

    let thunk_results = make_thunk(
        &mut cs.namespace(|| "make_thunk"),
        &first_result_expr,
        &first_result_env,
        &first_result_cont,
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
        w.store.as_ref().expect("Store missing.")
    } else {
        &Store::default()
    };

    let output_expr = witness
        .prethunk_output_expr
        .as_ref()
        .unwrap()
        .allocated_tagged_hash(&mut cs.namespace(|| "output_expr"))?;
    let output_env = witness
        .prethunk_output_env
        .as_ref()
        .unwrap()
        .allocated_tagged_hash(&mut cs.namespace(|| "output_env"))?;
    let output_cont = witness
        .prethunk_output_cont
        .as_ref()
        .unwrap()
        .allocated_tagged_hash(&mut cs.namespace(|| "output_cont"))?;

    let sym_is_nil = expr.alloc_equal(&mut cs.namespace(|| "sym is nil"), &g.nil_tagged_hash)?;
    let sym_is_t = expr.alloc_equal(&mut cs.namespace(|| "sym is t"), &g.t_tagged_hash)?;

    let sym_is_self_evaluating = or!(cs, &sym_is_nil, &sym_is_t)?;
    let sym_otherwise = Boolean::not(&sym_is_self_evaluating);

    let (binding, smaller_env) =
        car_cdr(&mut cs.namespace(|| "If unevaled_args cons"), g, env, store)?;

    let binding_is_nil =
        binding.alloc_equal(&mut cs.namespace(|| "binding is nil"), &g.nil_tagged_hash)?;

    let binding_not_nil = Boolean::not(&binding_is_nil);

    let otherwise_and_binding_is_nil = and!(cs, &sym_otherwise, &binding_is_nil)?;
    let otherwise_and_binding_not_nil = and!(cs, &sym_otherwise, &binding_not_nil)?;

    let (var_or_rec_binding, val_or_more_rec_env) =
        car_cdr(&mut cs.namespace(|| "car_cdr binding"), g, &binding, store)?;

    let var_or_rec_binding_is_sym = alloc_equal(
        &mut cs.namespace(|| "var_or_rec_binding_is_sym"),
        &var_or_rec_binding.tag,
        &g.sym_tag,
    )?;

    let v = var_or_rec_binding.clone();
    let val = val_or_more_rec_env.clone();
    let v_is_expr1 = expr.alloc_equal(&mut cs.namespace(|| "v_is_expr1"), &v)?;
    let v_not_expr1 = Boolean::not(&v_is_expr1);

    let otherwise_and_v_not_expr = and!(cs, &otherwise_and_binding_not_nil, &v_not_expr1)?;
    let otherwise_and_sym = and!(cs, &otherwise_and_v_not_expr, &var_or_rec_binding_is_sym)?;

    let v_is_expr1_real = and!(cs, &v_is_expr1, &otherwise_and_sym)?;

    let var_or_rec_binding_is_cons = alloc_equal(
        &mut cs.namespace(|| "var_or_rec_binding_is_cons"),
        &var_or_rec_binding.tag,
        &g.cons_tag,
    )?;

    let otherwise_and_cons = and!(cs, &otherwise_and_v_not_expr, &var_or_rec_binding_is_cons)?;

    let (v2, val2) = car_cdr(
        &mut cs.namespace(|| "car_cdr var_or_rec_binding"),
        g,
        &var_or_rec_binding,
        store,
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

    let otherwise_cons_neither = and!(cs, &var_or_rec_binding_is_neither, &otherwise_and_cons)?;

    let make_thunk_bool0 = or!(cs, &sym_is_self_evaluating, &v_is_expr1_real)?;
    let make_thunk_bool = or!(cs, &make_thunk_bool0, &v2_is_expr_real)?;

    let make_thunk = ifx!(cs, &make_thunk_bool, &g.true_num, &g.false_num)?;

    let cont_is_lookup = alloc_equal(
        &mut cs.namespace(|| "cont_is_lookup"),
        &cont.tag,
        &g.lookup_cont_tag,
    )?;

    let cont_is_lookup_sym = and!(cs, &cont_is_lookup, &otherwise_and_sym)?;
    let cont_not_lookup_sym = and!(cs, &Boolean::not(&cont_is_lookup), &otherwise_and_sym)?;

    let cont_is_lookup_cons = and!(cs, &cont_is_lookup, &otherwise_and_cons)?;
    let cont_not_lookup_cons = and!(cs, &Boolean::not(&cont_is_lookup), &otherwise_and_cons)?;

    let lookup_continuation = Continuation::construct(
        &mut cs.namespace(|| "lookup_continuation"),
        &g.lookup_cont_tag.clone(),
        // Mirrors Continuation::get_hash_components()
        vec![
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
        witness.extended_closure.clone(),
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

    let cs = &mut cs.namespace(|| "a");
    {
        let cond = and!(cs, &sym_is_self_evaluating, not_dummy)?;
        implies_equal_t!(cs, &cond, &output_expr, &expr);
        implies_equal_t!(cs, &cond, &output_env, &env);
        implies_equal_t!(cs, &cond, &output_cont, &cont);
    }

    let cs = &mut cs.namespace(|| "b");
    {
        let cond = and!(cs, &otherwise_and_binding_is_nil, not_dummy)?;
        implies_equal_t!(cs, &cond, &output_expr, &expr);
        implies_equal_t!(cs, &cond, &output_env, &env);
        implies_equal_t!(cs, &cond, &output_cont, &g.error_tagged_hash);
    }
    let cs = &mut cs.namespace(|| "c");

    {
        let cond = and!(cs, &v_is_expr1_real, not_dummy)?;
        implies_equal_t!(cs, &cond, &output_expr, &val);
        implies_equal_t!(cs, &cond, &output_env, &env);
        implies_equal_t!(cs, &cond, &output_cont, &cont);
    }
    let cs = &mut cs.namespace(|| "d");

    {
        let cond = and!(cs, &cont_is_lookup_sym, not_dummy)?;
        implies_equal_t!(cs, &cond, &output_expr, &expr);
        implies_equal_t!(cs, &cond, &output_env, &smaller_env);
        implies_equal_t!(cs, &cond, &output_cont, &cont);
    }
    let cs = &mut cs.namespace(|| "e");

    {
        let cond = and!(cs, &cont_not_lookup_sym, not_dummy)?;
        implies_equal_t!(cs, &cond, &output_expr, &expr);
        implies_equal_t!(cs, &cond, &output_env, &smaller_env);
        implies_equal_t!(cs, &cond, &output_cont, &lookup_continuation);
    }

    let cs = &mut cs.namespace(|| "f");
    {
        let cond = and!(cs, &v2_is_expr_real, not_dummy)?;
        implies_equal_t!(cs, &cond, &output_expr, &val_to_use);
        implies_equal_t!(cs, &cond, &output_env, &env);
        implies_equal_t!(cs, &cond, &output_cont, &cont);
    }

    let cs = &mut cs.namespace(|| "g");
    {
        let cond = and!(cs, &otherwise_and_v2_not_expr, not_dummy)?;
        implies_equal_t!(cs, &cond, &output_expr, &expr);
        implies_equal_t!(cs, &cond, &output_env, &env_to_use);
    }
    let cs = &mut cs.namespace(|| "h");

    {
        let cond = and!(cs, &cont_is_lookup_cons, not_dummy)?;
        implies_equal_t!(cs, &cond, &output_cont, &cont);
    }
    let cs = &mut cs.namespace(|| "i");
    {
        let cond = and!(cs, &cont_not_lookup_cons, not_dummy)?;
        implies_equal_t!(cs, &cond, &output_cont, &lookup_continuation);
    }

    {
        let cond = and!(cs, &otherwise_cons_neither, not_dummy)?;
        // "Bad form"
        implies_equal_t!(cs, &cond, &output_cont, &g.error_tagged_hash);
    }

    Ok((output_expr, output_env, output_cont, make_thunk))
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
    let store = witness.store.as_ref().expect("Store missing.");

    let lambda = g.lambda_tagged_hash.clone();
    // let quote = g.quote_tagged_hash.clone();
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
    let fun_hash = Expression::read_sym("FUN").get_hash();

    let (head, rest) = car_cdr(&mut cs.namespace(|| "eval_cons expr"), g, expr, store)?;

    let not_dummy = alloc_equal(&mut cs.namespace(|| "rest is cons"), &rest.tag, &g.cons_tag)?;

    let (arg1, more) = car_cdr(&mut cs.namespace(|| "car_cdr(rest)"), g, &rest, store)?;

    let mut result_expr_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_expr_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_env_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_env_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_cont_tag_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_cont_hash_clauses: Vec<CaseClause<Fr>> = Vec::new();
    let mut result_make_thunk_clauses: Vec<CaseClause<Fr>> = Vec::new();

    let mut add_clauses = |key,
                           (result_expr, result_env, result_cont, make_thunk): (
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
        add_clause_aux(&mut result_make_thunk_clauses, make_thunk);
    };

    {
        // head == LAMBDA
        let (args, body) = (arg1.clone(), more.clone());
        let args_is_nil =
            args.alloc_equal(&mut cs.namespace(|| "args_is_nil"), &g.nil_tagged_hash)?;

        let not_dummy1 = Boolean::not(&args_is_nil);
        let not_dummy2 = Boolean::and(&mut cs.namespace(|| "not_dummy2"), &not_dummy, &not_dummy1)?;

        let (car_args, cdr_args) = car_cdr(&mut cs.namespace(|| "car_cdr args"), g, &args, store)?;

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

        let list = Expression::construct_list(&mut cs.namespace(|| "xxx"), g, &[l])?;
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
        let (body1, rest_body) = car_cdr(&mut cs.namespace(|| "car_cdr body"), g, &body, store)?;

        let (binding1, rest_bindings) = car_cdr(
            &mut cs.namespace(|| "car_cdr bindings"),
            g,
            &bindings,
            store,
        )?;
        let (var, more_vals) = car_cdr(
            &mut cs.namespace(|| "car_cdr binding1"),
            g,
            &binding1,
            store,
        )?;
        let (val, end) = car_cdr(
            &mut cs.namespace(|| "car_cdr more_vals"),
            g,
            &more_vals,
            store,
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
            vec![
                var.tag.clone(),
                var.hash.clone(),
                expanded.clone().tag,
                expanded.clone().hash,
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
            vec![
                var.tag.clone(),
                var.hash,
                expanded.clone().tag,
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
            vec![
                g.op2_cons_tag.clone(),
                env.tag.clone(),
                env.hash.clone(),
                more.clone().tag,
                more.clone().hash,
                cont.tag.clone(),
                cont.hash.clone(),
                g.default.clone(),
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
            vec![
                g.op1_car_tag.clone(),
                arg1.clone().tag,
                arg1.clone().hash,
                env.tag.clone(),
                env.hash.clone(),
                g.default.clone(),
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
            vec![
                g.op1_cdr_tag.clone(),
                arg1.clone().tag,
                arg1.clone().hash,
                env.tag.clone(),
                env.hash.clone(),
                g.default.clone(),
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
            vec![
                g.op1_atom_tag.clone(),
                arg1.clone().tag,
                arg1.clone().hash,
                env.tag.clone(),
                env.hash.clone(),
                g.default.clone(),
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
            vec![
                g.op2_sum_tag.clone(),
                env.tag.clone(),
                env.hash.clone(),
                more.clone().tag,
                more.clone().hash,
                cont.tag.clone(),
                cont.hash.clone(),
                g.default.clone(),
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
            vec![
                g.op2_diff_tag.clone(),
                env.tag.clone(),
                env.hash.clone(),
                more.clone().tag,
                more.clone().hash,
                cont.tag.clone(),
                cont.hash.clone(),
                g.default.clone(),
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
            vec![
                g.op2_product_tag.clone(),
                env.tag.clone(),
                env.hash.clone(),
                more.clone().tag,
                more.clone().hash,
                cont.tag.clone(),
                cont.hash.clone(),
                g.default.clone(),
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
            vec![
                g.op2_quotient_tag.clone(),
                env.tag.clone(),
                env.hash.clone(),
                more.clone().tag,
                more.clone().hash,
                cont.tag.clone(),
                cont.hash.clone(),
                g.default.clone(),
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
            vec![
                g.rel2_numequal_tag.clone(),
                env.tag.clone(),
                env.hash.clone(),
                more.clone().tag,
                more.clone().hash,
                cont.tag.clone(),
                cont.hash.clone(),
                g.default.clone(),
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
            vec![
                g.rel2_numequal_tag.clone(),
                env.tag.clone(),
                env.hash.clone(),
                more.clone().tag,
                more.clone().hash,
                cont.tag.clone(),
                cont.hash.clone(),
                g.default.clone(),
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
            vec![
                g.rel2_numequal_tag.clone(),
                unevaled_args.clone().tag,
                unevaled_args.hash,
                cont.tag.clone(),
                cont.hash.clone(),
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
    {
        // head == (FN . ARGS)

        let fun_form = head;
        let args = rest;

        let call_continuation = Continuation::construct(
            &mut cs.namespace(|| "Call"),
            &g.call_cont_tag,
            vec![
                arg1.tag.clone(),
                arg1.hash.clone(),
                env.tag.clone(),
                env.hash.clone(),
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

        add_clauses(
            fun_hash,
            (res, env.clone(), continuation, g.false_num.clone()),
        );
    }

    let mut all_clauses = vec![
        result_expr_tag_clauses.as_slice(),
        result_expr_hash_clauses.as_slice(),
        result_env_tag_clauses.as_slice(),
        result_env_hash_clauses.as_slice(),
        result_cont_tag_clauses.as_slice(),
        result_cont_hash_clauses.as_slice(),
        result_make_thunk_clauses.as_slice(),
    ];

    let case_results = multi_case(
        &mut cs.namespace(|| "input expr tag case"),
        &expr.tag,
        &all_clauses,
        &[
            g.default.clone(),
            g.default.clone(),
            g.default.clone(),
            g.default.clone(),
            g.default.clone(),
            g.default.clone(),
            g.false_num.clone(),
        ],
    )?;

    let result_expr = tagged_hash_by_index(0, &case_results);
    let result_env = tagged_hash_by_index(1, &case_results);
    let result_cont = tagged_hash_by_index(2, &case_results);
    let result_make_thunk: &AllocatedNum<Fr> = &case_results[6];

    Ok((
        result_expr,
        result_env,
        result_cont,
        result_make_thunk.clone(),
    ))
}

fn make_thunk<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    cont: &AllocatedTaggedHash,
    result: &AllocatedTaggedHash,
    env: &AllocatedTaggedHash,
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

    let (witnessed_cont_hash, witnessed_cont_components) = allocate_continuation_components(
        &mut cs.namespace(|| "cont components"),
        &witness.make_thunk_cont,
    )?;
    {
        equal(
            cs,
            || "witnessed cont hash equals cont hash",
            &witnessed_cont_hash,
            &cont.hash,
        );
    }
    let witnessed_cont_continuation = AllocatedTaggedHash::from_tag_and_hash(
        witnessed_cont_components[3].clone(),
        witnessed_cont_components[4].clone(),
    );

    let effective_env = {
        let saved_env = AllocatedTaggedHash::from_tag_and_hash(
            witnessed_cont_components[1].clone(),
            witnessed_cont_components[2].clone(),
        );

        let cont_tag_is_lookup = alloc_equal(
            &mut cs.namespace(|| "cont_tag_is_lookup"),
            &cont.tag,
            &global_allocations.lookup_cont_tag,
        )?;

        let cont_tag_is_tail = alloc_equal(
            &mut cs.namespace(|| "cont_tag_is_tail"),
            &cont.tag,
            &global_allocations.tail_cont_tag,
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

    let tail_clause_results = {
        // If this is true,
        let tail_cont_cont_is_tail = alloc_equal(
            &mut cs.namespace(|| "tail_cont_cont_is_tail"),
            &cont.tag,
            &global_allocations.tail_cont_tag,
        )?;

        let (witnessed_tail_cont_cont_hash, witnessed_tail_cont_cont_components) =
            allocate_continuation_components(
                &mut cs.namespace(|| "tail_cont cont components"),
                &witness.make_thunk_tail_continuation_cont,
            )?;

        // Then these are the results.
        let inner_cont_tail_results = {
            {
                {
                    let witnessed_cont_tag_is_tail = &alloc_equal(
                        &mut cs.namespace(|| "witnessed_cont_tag_is_tail"),
                        &cont.tag,
                        &global_allocations.tail_cont_tag,
                    )?;
                    let actual_continuation_or_no_op = pick(
                        &mut cs.namespace(|| "maybe witnessed_cont_continuation.hash"),
                        witnessed_cont_tag_is_tail,
                        &witnessed_cont_continuation.hash,
                        &witnessed_tail_cont_cont_hash, // This branch will make the following equality constraint never fail.
                    )?;
                    equal(
                        cs,
                        || "witnessed tail cont cont hash equals cont hash",
                        &witnessed_tail_cont_cont_hash,
                        &actual_continuation_or_no_op,
                    );
                }
            }

            let saved_env = AllocatedTaggedHash::from_tag_and_hash(
                witnessed_tail_cont_cont_components[0].clone(),
                witnessed_tail_cont_cont_components[1].clone(),
            );

            let previous_cont = AllocatedTaggedHash::from_tag_and_hash(
                witnessed_tail_cont_cont_components[2].clone(),
                witnessed_tail_cont_cont_components[3].clone(),
            );

            let thunk_hash = Thunk::hash_components(
                &mut cs.namespace(|| "tail_thunk_hash"),
                &[
                    result.tag.clone(),
                    result.hash.clone(),
                    previous_cont.tag.clone(),
                    previous_cont.hash,
                ],
            )?;

            let result_expr = AllocatedTaggedHash::from_tag_and_hash(
                global_allocations.thunk_tag.clone(),
                thunk_hash,
            );
            let result_env = saved_env;
            let result_cont = global_allocations.dummy_tagged_hash.clone();

            (result_expr, result_env, result_cont)
        };

        // Otherwise, these are the results.
        let otherwise_results: (
            AllocatedTaggedHash,
            AllocatedTaggedHash,
            AllocatedTaggedHash,
        ) = {
            let effective_env2 = {
                let saved_env2 = AllocatedTaggedHash::from_tag_and_hash(
                    witnessed_tail_cont_cont_components[1].clone(),
                    witnessed_tail_cont_cont_components[2].clone(),
                );

                let tail_cont_cont_tag_is_lookup = alloc_equal(
                    &mut cs.namespace(|| "tail_cont_cont_tag_is_lookup"),
                    &witnessed_cont_continuation.tag,
                    &global_allocations.lookup_cont_tag,
                )?;
                assert!(
                    witnessed_cont_continuation.tag.get_value()
                        != global_allocations.tail_cont_tag.get_value()
                );

                let effective_env2 = pick_tagged_hash(
                    &mut cs.namespace(|| "effective_env2"),
                    &tail_cont_cont_tag_is_lookup,
                    &saved_env2,
                    &effective_env,
                )?;

                effective_env2
            };

            let outermost_result = (
                result.clone(),
                effective_env.clone(),
                global_allocations.terminal_tagged_hash.clone(),
            );

            let otherwise_result: (
                AllocatedTaggedHash,
                AllocatedTaggedHash,
                AllocatedTaggedHash,
            ) = {
                let thunk_hash = Thunk::hash_components(
                    &mut cs.namespace(|| "tail thunk_hash"),
                    &[
                        result.tag.clone(),
                        result.hash.clone(),
                        witnessed_cont_continuation.tag.clone(),
                        witnessed_tail_cont_cont_hash.clone(),
                    ],
                )?;

                let result_expr = AllocatedTaggedHash::from_tag_and_hash(
                    global_allocations.thunk_tag.clone(),
                    thunk_hash,
                );

                (
                    result_expr,
                    effective_env2,
                    global_allocations.dummy_tagged_hash.clone(),
                )
            };

            let witnessed_tail_cont_cont_is_outermost = alloc_equal(
                &mut cs.namespace(|| "witnessed_tail_cont_cont_is_outermost"),
                &witnessed_cont_continuation.tag,
                &global_allocations.outermost_tagged_hash.tag,
            )?;

            let inner_result_expr = pick_tagged_hash(
                &mut cs.namespace(|| "inner_result_expr"),
                &witnessed_tail_cont_cont_is_outermost,
                &outermost_result.0,
                &otherwise_result.0,
            )?;
            let inner_result_env = pick_tagged_hash(
                &mut cs.namespace(|| "inner_result_env"),
                &witnessed_tail_cont_cont_is_outermost,
                &outermost_result.1,
                &otherwise_result.1,
            )?;
            let inner_result_cont = pick_tagged_hash(
                &mut cs.namespace(|| "inner_result_cont"),
                &witnessed_tail_cont_cont_is_outermost,
                &outermost_result.2,
                &otherwise_result.2,
            )?;

            (inner_result_expr, inner_result_env, inner_result_cont)
        };

        // Assign results based on the condition.
        let the_result_expr = pick_tagged_hash(
            &mut cs.namespace(|| "the_result_expr"),
            &tail_cont_cont_is_tail,
            &inner_cont_tail_results.0,
            &otherwise_results.0,
        )?;

        let the_result_env = pick_tagged_hash(
            &mut cs.namespace(|| "the_result_env"),
            &tail_cont_cont_is_tail,
            &inner_cont_tail_results.1,
            &otherwise_results.1,
        )?;

        let the_result_cont = pick_tagged_hash(
            &mut cs.namespace(|| "the_result_cont"),
            &tail_cont_cont_is_tail,
            &inner_cont_tail_results.2,
            &otherwise_results.2,
        )?;

        (the_result_expr, the_result_env, the_result_cont)
    };

    add_clauses(BaseContinuationTag::Tail.cont_tag_fr(), tail_clause_results);

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

        let result_expr_tag = global_allocations.thunk_tag.clone();
        let result_expr_hash = thunk_hash;

        let result_cont_tag = global_allocations.dummy_tagged_hash.tag.clone();
        let result_cont_hash = global_allocations.dummy_tagged_hash.hash.clone();
        [
            result_expr_tag,
            result_expr_hash,
            effective_env.tag,
            effective_env.hash,
            result_cont_tag,
            result_cont_hash,
        ]
    };

    let all_clauses = vec![
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
    let store = witness.store.as_ref().expect("Store missing");
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

    let (continuation_hash, continuation_components) = allocate_continuation_components(
        &mut cs.namespace(|| "allocate_continuation_components"),
        &witness.invoke_continuation_cont,
    )?;

    {
        // Continuation::Call
        let saved_env = tagged_hash_by_index(0, &continuation_components);
        let arg = tagged_hash_by_index(1, &continuation_components);
        let continuation = tagged_hash_by_index(2, &continuation_components);

        let function = result;
        let next_expr = arg;

        let call2_components = vec![global_allocations.call2_cont_tag.clone()];
        let newer_cont = Continuation::construct(
            &mut cs.namespace(|| "construct newer_cont"),
            &global_allocations.call2_cont_tag.clone(),
            // Mirrors Continuation::get_hash_components()
            vec![
                function.tag.clone(),
                function.hash.clone(),
                saved_env.tag,
                saved_env.hash,
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
        let cont = tagged_hash_by_index(2, &continuation_components);
        {
            // An alternate way to do this would be to have just a single allocate_fun()
            // function, and extract either real or dummy values from the witness.
            // That's probably better and cleaner.
            let (hash, arg_t, body_t, closed_env) = Expression::allocate_maybe_fun(
                &mut cs.namespace(|| "allocate Call2 fun"),
                witness.invoke_continuation_output_result.clone(),
            )?;

            let fun_is_correct = constraints::alloc_equal(
                &mut cs.namespace(|| "fun hash is correct"),
                &fun.hash,
                &hash,
            )?;

            let call2_branch_taken = constraints::alloc_equal(
                &mut cs.namespace(|| "Call2 branch taken"),
                &global_allocations.call2_cont_tag,
                &cont.tag,
            )?;

            enforce_implication(
                &mut cs.namespace(|| "Call2 implies non-dummy fun"),
                &call2_branch_taken,
                &fun_is_correct,
            );

            let newer_env = extend(
                &mut cs.namespace(|| "Call2 extend env"),
                global_allocations,
                &closed_env,
                &arg_t,
                result,
                store,
            )?;

            let tail_cont = make_tail_continuation(
                &mut cs.namespace(|| "Call2 make_tail_continuation"),
                global_allocations,
                &saved_env,
                &cont,
            )?;

            add_clauses(
                BaseContinuationTag::Call2.cont_tag_fr(),
                (
                    body_t,
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
            store,
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
                cont,
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
            store,
        )?;

        let tail_cont = make_tail_continuation(
            &mut cs.namespace(|| "LetRecStar make_tail_continuation"),
            global_allocations,
            &saved_env,
            &cont,
        )?;

        add_clauses(
            BaseContinuationTag::LetRecStar.cont_tag_fr(),
            (
                body,
                extended_env,
                cont,
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
            store,
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
        let saved_env = tagged_hash_by_index(0, &continuation_components[1..]);
        let unevaled_args = tagged_hash_by_index(1, &continuation_components[1..]);
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
            store,
        )?;

        let binop2_cont = Continuation::construct(
            &mut cs.namespace(|| "Binop2"),
            &global_allocations.binop2_cont_tag,
            vec![
                op2,
                result.tag.clone(),
                result.hash.clone(),
                continuation.tag,
                continuation.hash,
                global_allocations.default.clone(),
                global_allocations.default.clone(),
            ],
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

        let sum = constraints::add(&mut cs.namespace(|| "sum"), &a, &b)?;
        let diff = constraints::sub(&mut cs.namespace(|| "difference"), &a, &b)?;
        let product = constraints::mul(&mut cs.namespace(|| "product"), &a, &b)?;
        let quotient = constraints::div(&mut cs.namespace(|| "quotient"), &a, &b)?;

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
        let saved_env = tagged_hash_by_index(0, &continuation_components[1..]);
        let unevaled_args = tagged_hash_by_index(1, &continuation_components[1..]);
        let continuation = tagged_hash_by_index(2, &continuation_components[1..]);

        let not_dummy = alloc_equal(
            &mut cs.namespace(|| "Relop not dummy"),
            &continuation.tag,
            &global_allocations.binop_cont_tag,
        )?;

        let (allocated_arg2, allocated_rest) = car_cdr(
            &mut cs.namespace(|| "Relops cons"),
            global_allocations,
            &unevaled_args,
            store,
        )?;

        // FIXME: If allocated_rest != Nil, then error.
        let relop2_cont = Continuation::construct(
            &mut cs.namespace(|| "Relop2"),
            &global_allocations.relop2_cont_tag,
            vec![
                relop2,
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

        let (arg1, more) = car_cdr(
            &mut cs.namespace(|| "If unevaled_args cons"),
            global_allocations,
            &unevaled_args,
            store,
        )?;

        let condition_is_nil = condition.alloc_equal(
            &mut cs.namespace(|| "condition is nil"),
            &global_allocations.nil_tagged_hash,
        )?;

        let (arg2, end) = car_cdr(
            &mut cs.namespace(|| "If more cons"),
            global_allocations,
            &more,
            store,
        )?;

        let res = pick_tagged_hash(
            &mut cs.namespace(|| "pick1 arg1 or arg2"),
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

    let all_clauses = vec![
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
    let not_dummy = alloc_equal(
        &mut cs.namespace(|| "not_dummy"),
        &maybe_cons.tag,
        &g.cons_tag,
    )?;

    let (car, cdr) = if not_dummy.get_value().expect("not_dummy missing") {
        let (car, cdr) = store.car_cdr(
            &store
                .fetch(&maybe_cons.tagged_hash())
                .expect("Cons missing from store"),
        );
        (car, cdr)
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
        &g.cons_tag,
        &constructed_cons.tag,
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
    Expression::construct_cons(cs, g, var, val)
}

fn extend_rec<CS: ConstraintSystem<Fr>>(
    mut cs: CS,
    g: &GlobalAllocations,
    env: &AllocatedTaggedHash,
    var: &AllocatedTaggedHash,
    val: &AllocatedTaggedHash,
    store: &Store,
) -> Result<AllocatedTaggedHash, SynthesisError> {
    if let Some(fetched_env) = store.fetch(&env.tagged_hash()) {
        let (binding_or_env, rest) = store.car_cdr(&fetched_env);
        let (var_or_binding, val_or_more_bindings) = store.car_cdr(&binding_or_env);

        let a = var_or_binding.allocated_tagged_hash(&mut cs.namespace(|| "var_or_binding"))?;
        let b =
            var_or_binding.allocated_tagged_hash(&mut cs.namespace(|| "val_or_more_bindings"))?;

        let is_sym = constraints::alloc_equal(
            &mut cs.namespace(|| "var_or_binding is sym"),
            &a.tag,
            &g.sym_tag,
        )?;
        let is_nil = constraints::alloc_equal(
            &mut cs.namespace(|| "var_or_binding is nil"),
            &a.tag,
            &g.nil_tag,
        )?;
        let is_sym_or_nil = constraints::or(
            &mut cs.namespace(|| "var_or_binding is sym or nil"),
            &is_sym,
            &is_nil,
        )?;

        let binding = Expression::construct_cons(&mut cs.namespace(|| "binding"), g, var, val)?;
        let extended_env = Expression::construct_cons(
            &mut cs.namespace(|| "extended env"),
            g,
            &binding,
            &g.nil_tagged_hash,
        )?;

        let is_cons = constraints::alloc_equal(
            &mut cs.namespace(|| "var_or_binding is cons"),
            &a.tag,
            &g.cons_tag,
        )?;

        let binding_or_env_allocated =
            binding_or_env.allocated_tagged_hash(&mut cs.namespace(|| "binding_or_env"))?;

        let extended_rec_env = Expression::construct_cons(
            &mut cs.namespace(|| "extended rec env"),
            g,
            &binding,
            &binding_or_env_allocated,
        )?;

        let is_bad_input = Boolean::not(&constraints::or(
            &mut cs.namespace(|| "is sym or nil or cons"),
            &is_sym_or_nil,
            &is_cons,
        )?);

        let if_good = pick_tagged_hash(
            &mut cs.namespace(|| "pick env or rec env"),
            &is_sym_or_nil,
            &extended_env,
            &extended_rec_env,
        )?;

        Ok(pick_tagged_hash(
            &mut cs.namespace(|| "error if bad input to extend_rec"),
            &is_bad_input,
            &g.error_tagged_hash,
            &if_good,
        )?)
    } else {
        panic!("extend_rec env missing from store");
    }
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
    let continuation_is_outermost = alloc_equal(
        &mut cs.namespace(|| "continuation is outermost"),
        &continuation.tag,
        &g.outermost_tagged_hash.tag, // FIXME: Technically should check hash also.
    )?;

    let new_tail = Continuation::construct(
        &mut cs.namespace(|| "new tail continuation"),
        &g.tail_cont_tag,
        vec![
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

    let tail_or_outermost = constraints::or(
        &mut cs.namespace(|| "tail_or_outermost"),
        &continuation_is_tail,
        &continuation_is_outermost,
    )?;

    pick_tagged_hash(
        &mut cs.namespace(|| "the tail continuation"),
        &tail_or_outermost,
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

impl Continuation {
    fn allocate_components<CS: ConstraintSystem<Fr>>(
        &self,
        mut cs: CS,
    ) -> Result<(AllocatedNum<Fr>, Vec<AllocatedNum<Fr>>), SynthesisError> {
        let component_frs = self.get_hash_components();
        let mut components = Vec::with_capacity(8);

        for (i, fr) in component_frs.iter().enumerate() {
            components.push(AllocatedNum::alloc(
                cs.namespace(|| format!("Continuation component {}", i)),
                || Ok(*fr),
            )?);
        }

        let hash = poseidon_hash(
            cs.namespace(|| "Continuation"),
            components.clone(),
            &POSEIDON_CONSTANTS_8,
        )?;

        Ok((hash, components))
    }

    fn allocate_dummy_components<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
    ) -> Result<(AllocatedNum<Fr>, Vec<AllocatedNum<Fr>>), SynthesisError> {
        let length = 8;
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
            &POSEIDON_CONSTANTS_8,
        )?;

        Ok((dummy_hash, result))
    }

    fn construct<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        cont_tag: &AllocatedNum<Fr>,
        components: Vec<AllocatedNum<Fr>>,
    ) -> Result<AllocatedTaggedHash, SynthesisError> {
        let hash = poseidon_hash(
            cs.namespace(|| "Continuation"),
            components,
            &POSEIDON_CONSTANTS_8,
        )?;

        let cont = AllocatedTaggedHash::from_tag_and_hash(cont_tag.clone(), hash);
        Ok(cont)
    }
}

impl Thunk {
    // First component is the hash, which is wrong.
    fn allocate_components<CS: ConstraintSystem<Fr>>(
        &self,
        mut cs: CS,
    ) -> Result<(AllocatedNum<Fr>, Vec<AllocatedNum<Fr>>), SynthesisError> {
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

    fn allocate_dummy_components<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
    ) -> Result<(AllocatedNum<Fr>, Vec<AllocatedNum<Fr>>), SynthesisError> {
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

    fn hash_components<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        components: &[AllocatedNum<Fr>],
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
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

impl Expression {
    fn allocate_maybe_fun<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        maybe_fun: Option<Expression>,
    ) -> Result<
        (
            AllocatedNum<Fr>,
            AllocatedTaggedHash,
            AllocatedTaggedHash,
            AllocatedTaggedHash,
        ),
        SynthesisError,
    > {
        match maybe_fun {
            Some(f) => f.allocate_fun(cs),
            _ => Self::allocate_dummy_fun(cs),
        }
    }

    fn allocate_fun<CS: ConstraintSystem<Fr>>(
        &self,
        mut cs: CS,
    ) -> Result<
        (
            AllocatedNum<Fr>,
            AllocatedTaggedHash,
            AllocatedTaggedHash,
            AllocatedTaggedHash,
        ),
        SynthesisError,
    > {
        match self {
            Expression::Fun(arg, body, closed_env) => {
                let arg_t = AllocatedTaggedHash::from_tagged_hash(
                    &mut cs.namespace(|| "allocate arg"),
                    *arg,
                )?;
                let body_t = AllocatedTaggedHash::from_tagged_hash(
                    &mut cs.namespace(|| "allocate body"),
                    *body,
                )?;
                let closed_env_t = AllocatedTaggedHash::from_tagged_hash(
                    &mut cs.namespace(|| "allocate closed_env"),
                    *closed_env,
                )?;

                let preimage = vec![];
                let hash =
                    poseidon_hash(cs.namespace(|| "Fun hash"), preimage, &POSEIDON_CONSTANTS_6)?;

                Ok((hash, arg_t, body_t, closed_env_t))
            }
            _ => Err(SynthesisError::AssignmentMissing),
        }
    }

    fn allocate_dummy_fun<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
    ) -> Result<
        (
            AllocatedNum<Fr>,
            AllocatedTaggedHash,
            AllocatedTaggedHash,
            AllocatedTaggedHash,
        ),
        SynthesisError,
    > {
        let arg_t = AllocatedTaggedHash::from_unallocated_tag_and_hash(
            &mut cs.namespace(|| "dummy arg_t"),
            Fr::zero(),
            Fr::zero(),
        )?;

        let body_t = AllocatedTaggedHash::from_unallocated_tag_and_hash(
            &mut cs.namespace(|| "dummy body_t"),
            Fr::zero(),
            Fr::zero(),
        )?;

        let closed_env_t = AllocatedTaggedHash::from_unallocated_tag_and_hash(
            &mut cs.namespace(|| "dummy closed_env_t"),
            Fr::zero(),
            Fr::zero(),
        )?;

        let preimage = vec![];
        let hash = poseidon_hash(cs.namespace(|| "Fun hash"), preimage, &POSEIDON_CONSTANTS_6)?;

        Ok((hash, arg_t, body_t, closed_env_t))
    }

    fn construct_cons<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        g: &GlobalAllocations,
        a: &AllocatedTaggedHash,
        b: &AllocatedTaggedHash,
    ) -> Result<AllocatedTaggedHash, SynthesisError> {
        // This is actually binary_hash, considering creating that helper for use elsewhere.
        let preimage = vec![a.tag.clone(), a.hash.clone(), b.tag.clone(), b.hash.clone()];

        let hash = poseidon_hash(
            cs.namespace(|| "Cons hash"),
            preimage,
            &POSEIDON_CONSTANTS_4,
        )?;
        Ok(AllocatedTaggedHash::from_tag_and_hash(
            g.cons_tag.clone(),
            hash,
        ))
    }

    fn construct_list<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        g: &GlobalAllocations,
        elts: &[AllocatedTaggedHash],
    ) -> Result<AllocatedTaggedHash, SynthesisError> {
        if elts.is_empty() {
            Ok(g.nil_tagged_hash.clone())
        } else {
            let tail = Self::construct_list(&mut cs.namespace(|| "Cons tail"), g, &elts[1..])?;
            Self::construct_cons(&mut cs.namespace(|| "Cons"), g, &elts[0], &tail)
        }
    }

    fn construct_fun<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        g: &GlobalAllocations,
        arg: &AllocatedTaggedHash,
        body: &AllocatedTaggedHash,
        closed_env: &AllocatedTaggedHash,
    ) -> Result<AllocatedTaggedHash, SynthesisError> {
        let preimage = vec![
            arg.tag.clone(),
            arg.hash.clone(),
            body.tag.clone(),
            body.hash.clone(),
            closed_env.tag.clone(),
            closed_env.hash.clone(),
        ];

        let hash = poseidon_hash(cs.namespace(|| "Fun hash"), preimage, &POSEIDON_CONSTANTS_6)?;
        Ok(AllocatedTaggedHash::from_tag_and_hash(
            g.cons_tag.clone(),
            hash,
        ))
    }
}

fn allocate_continuation_components<CS: ConstraintSystem<Fr>>(
    mut cs: CS,
    cont: &Option<Continuation>,
) -> Result<(AllocatedNum<Fr>, Vec<AllocatedNum<Fr>>), SynthesisError> {
    if let Some(cont) = cont {
        cont.allocate_components(cs)
    } else {
        Continuation::allocate_dummy_components(cs)
    }
}

fn allocate_thunk_components<CS: ConstraintSystem<Fr>>(
    mut cs: CS,
    thunk: &Option<Thunk>,
) -> Result<(AllocatedNum<Fr>, AllocatedTaggedHash, AllocatedTaggedHash), SynthesisError> {
    let (hash, components) = if let Some(thunk) = thunk {
        thunk.allocate_components(cs)
    } else {
        Thunk::allocate_dummy_components(cs)
    }?;

    // allocate_thunk_components should probably returned AllocatedTaggedHashes.
    let thunk_value =
        AllocatedTaggedHash::from_tag_and_hash(components[0].clone(), components[1].clone());

    let thunk_continuation =
        AllocatedTaggedHash::from_tag_and_hash(components[2].clone(), components[3].clone());

    Ok((hash, thunk_value, thunk_continuation))
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

            frame
                .clone()
                .synthesize(&mut cs)
                .expect("failed to synthesize");

            assert_eq!(29379, cs.num_constraints());

            if expect_success {
                assert!(cs.is_satisfied());
            } else {
                assert!(!cs.is_satisfied());
            }
            let mut rng = rand::thread_rng();
            let proof = frame.generate_groth16_proof(&mut rng);
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
