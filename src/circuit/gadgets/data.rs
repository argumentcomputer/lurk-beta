use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};
use neptune::{
    circuit2::poseidon_hash_allocated as poseidon_hash,
    circuit2_witness::poseidon_hash_allocated_witness,
    poseidon::{Arity, PoseidonConstants},
};

use crate::field::LurkField;
use crate::store::Store;
use crate::tag::{ContTag, ExprTag, Op1, Op2, Tag};

use super::pointer::{AllocatedContPtr, AllocatedPtr};

#[derive(Clone, Debug)]
pub struct GlobalAllocations<F: LurkField> {
    pub terminal_ptr: AllocatedContPtr<F>,
    pub error_ptr_cont: AllocatedContPtr<F>,
    pub error_ptr: AllocatedPtr<F>,
    pub dummy_ptr: AllocatedContPtr<F>,
    pub nil_ptr: AllocatedPtr<F>,
    pub t_ptr: AllocatedPtr<F>,
    pub dummy_arg_ptr: AllocatedPtr<F>,
    pub empty_str_ptr: AllocatedPtr<F>,

    pub thunk_tag: AllocatedNum<F>,
    pub cons_tag: AllocatedNum<F>,
    pub char_tag: AllocatedNum<F>,
    pub str_tag: AllocatedNum<F>,
    pub num_tag: AllocatedNum<F>,
    pub u64_tag: AllocatedNum<F>,
    pub comm_tag: AllocatedNum<F>,
    pub fun_tag: AllocatedNum<F>,
    pub let_cont_tag: AllocatedNum<F>,
    pub letrec_cont_tag: AllocatedNum<F>,
    pub outermost_cont_tag: AllocatedNum<F>,
    pub lookup_cont_tag: AllocatedNum<F>,
    pub tail_cont_tag: AllocatedNum<F>,
    pub call0_cont_tag: AllocatedNum<F>,
    pub call_cont_tag: AllocatedNum<F>,
    pub call2_cont_tag: AllocatedNum<F>,
    pub unop_cont_tag: AllocatedNum<F>,
    pub emit_cont_tag: AllocatedNum<F>,
    pub binop_cont_tag: AllocatedNum<F>,
    pub binop2_cont_tag: AllocatedNum<F>,
    pub if_cont_tag: AllocatedNum<F>,

    pub op1_car_tag: AllocatedNum<F>,
    pub op1_cdr_tag: AllocatedNum<F>,
    pub op1_commit_tag: AllocatedNum<F>,
    pub op1_num_tag: AllocatedNum<F>,
    pub op1_char_tag: AllocatedNum<F>,
    pub op1_u64_tag: AllocatedNum<F>,
    pub op1_comm_tag: AllocatedNum<F>,
    pub op1_open_tag: AllocatedNum<F>,
    pub op1_secret_tag: AllocatedNum<F>,
    pub op1_atom_tag: AllocatedNum<F>,
    pub op1_emit_tag: AllocatedNum<F>,
    pub op2_cons_tag: AllocatedNum<F>,
    pub op2_strcons_tag: AllocatedNum<F>,
    pub op2_hide_tag: AllocatedNum<F>,
    pub op2_begin_tag: AllocatedNum<F>,
    pub op2_sum_tag: AllocatedNum<F>,
    pub op2_diff_tag: AllocatedNum<F>,
    pub op2_product_tag: AllocatedNum<F>,
    pub op2_quotient_tag: AllocatedNum<F>,
    pub op2_modulo_tag: AllocatedNum<F>,
    pub op2_equal_tag: AllocatedNum<F>,
    pub op2_numequal_tag: AllocatedNum<F>,
    pub op2_less_tag: AllocatedNum<F>,
    pub op2_less_equal_tag: AllocatedNum<F>,
    pub op2_greater_tag: AllocatedNum<F>,
    pub op2_greater_equal_tag: AllocatedNum<F>,

    pub lambda_sym: AllocatedPtr<F>,
    pub quote_ptr: AllocatedPtr<F>,

    pub true_num: AllocatedNum<F>,
    pub false_num: AllocatedNum<F>,
    pub default_num: AllocatedNum<F>,
    pub power2_32_num: AllocatedNum<F>,
    pub power2_64_num: AllocatedNum<F>,
}

impl<F: LurkField> GlobalAllocations<F> {
    pub fn new<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        store: &Store<F>,
    ) -> Result<Self, SynthesisError> {
        let terminal_ptr = AllocatedContPtr::alloc_constant_cont_ptr(
            &mut cs.namespace(|| "terminal continuation"),
            store,
            &store.get_cont_terminal(),
        )?;

        let error_ptr_cont = AllocatedContPtr::alloc_constant_cont_ptr(
            &mut cs.namespace(|| "error continuation"),
            store,
            &store.get_cont_error(),
        )?;
        let error_ptr =
            AllocatedPtr::from_parts(error_ptr_cont.tag().clone(), error_ptr_cont.hash().clone());

        let dummy_ptr = AllocatedContPtr::alloc_constant_cont_ptr(
            &mut cs.namespace(|| "dummy continuation"),
            store,
            &store.get_cont_dummy(),
        )?;

        let empty_str_ptr = AllocatedPtr::alloc_constant_ptr(
            &mut cs.namespace(|| "empty_str_ptr"),
            store,
            &store.strnil(),
        )?;

        let thunk_tag = ExprTag::Thunk.allocate_constant(&mut cs.namespace(|| "thunk_tag"));
        let cons_tag = ExprTag::Cons.allocate_constant(&mut cs.namespace(|| "cons_tag"));
        let char_tag = ExprTag::Char.allocate_constant(&mut cs.namespace(|| "char_tag"));
        let str_tag = ExprTag::Str.allocate_constant(&mut cs.namespace(|| "str_tag"));
        let num_tag = ExprTag::Num.allocate_constant(&mut cs.namespace(|| "num_tag"));
        let u64_tag = ExprTag::U64.allocate_constant(&mut cs.namespace(|| "u64_tag"));
        let comm_tag = ExprTag::Comm.allocate_constant(&mut cs.namespace(|| "comm_tag"));
        let fun_tag = ExprTag::Fun.allocate_constant(&mut cs.namespace(|| "fun_tag"));

        let outermost_cont_tag =
            ContTag::Outermost.allocate_constant(&mut cs.namespace(|| "outermost_cont_tag"));
        let lookup_cont_tag =
            ContTag::Lookup.allocate_constant(&mut cs.namespace(|| "lookup_cont_tag"));
        let let_cont_tag = ContTag::Let.allocate_constant(&mut cs.namespace(|| "let_cont_tag"));
        let letrec_cont_tag =
            ContTag::LetRec.allocate_constant(&mut cs.namespace(|| "letrec_cont_tag"));
        let tail_cont_tag = ContTag::Tail.allocate_constant(&mut cs.namespace(|| "tail_cont_tag"));
        let call0_cont_tag =
            ContTag::Call0.allocate_constant(&mut cs.namespace(|| "call0_cont_tag"));
        let call_cont_tag = ContTag::Call.allocate_constant(&mut cs.namespace(|| "call_cont_tag"));
        let call2_cont_tag =
            ContTag::Call2.allocate_constant(&mut cs.namespace(|| "call2_cont_tag"));
        let unop_cont_tag = ContTag::Unop.allocate_constant(&mut cs.namespace(|| "unop_cont_tag"));
        let emit_cont_tag = ContTag::Emit.allocate_constant(&mut cs.namespace(|| "emit_cont_tag"));
        let binop_cont_tag =
            ContTag::Binop.allocate_constant(&mut cs.namespace(|| "binop_cont_tag"));
        let binop2_cont_tag =
            ContTag::Binop2.allocate_constant(&mut cs.namespace(|| "binop2_cont_tag"));
        let if_cont_tag = ContTag::If.allocate_constant(&mut cs.namespace(|| "if_cont_tag"));

        let op1_car_tag = Op1::Car.allocate_constant(&mut cs.namespace(|| "op1_car_tag"));
        let op1_cdr_tag = Op1::Cdr.allocate_constant(&mut cs.namespace(|| "op1_cdr_tag"));
        let op1_commit_tag = Op1::Commit.allocate_constant(&mut cs.namespace(|| "op1_commit_tag"));
        let op1_num_tag = Op1::Num.allocate_constant(&mut cs.namespace(|| "op1_num_tag"));
        let op1_char_tag = Op1::Char.allocate_constant(&mut cs.namespace(|| "op1_char_tag"));
        let op1_u64_tag = Op1::U64.allocate_constant(&mut cs.namespace(|| "op1_u64_tag"));
        let op1_comm_tag = Op1::Comm.allocate_constant(&mut cs.namespace(|| "op1_comm_tag"));
        let op1_open_tag = Op1::Open.allocate_constant(&mut cs.namespace(|| "op1_open_tag"));
        let op1_secret_tag = Op1::Secret.allocate_constant(&mut cs.namespace(|| "op1_secret_tag"));
        let op1_atom_tag = Op1::Atom.allocate_constant(&mut cs.namespace(|| "op1_atom_tag"));
        let op1_emit_tag = Op1::Emit.allocate_constant(&mut cs.namespace(|| "op1_emit_tag"));
        let op2_cons_tag = Op2::Cons.allocate_constant(&mut cs.namespace(|| "op2_cons_tag"));
        let op2_strcons_tag =
            Op2::StrCons.allocate_constant(&mut cs.namespace(|| "op2_strcons_tag"));
        let op2_hide_tag = Op2::Hide.allocate_constant(&mut cs.namespace(|| "op2_hide_tag"));
        let op2_begin_tag = Op2::Begin.allocate_constant(&mut cs.namespace(|| "op2_begin_tag"));
        let op2_sum_tag = Op2::Sum.allocate_constant(&mut cs.namespace(|| "op2_sum_tag"));
        let op2_diff_tag = Op2::Diff.allocate_constant(&mut cs.namespace(|| "op2_diff_tag"));

        let op2_product_tag =
            Op2::Product.allocate_constant(&mut cs.namespace(|| "op2_product_tag"));
        let op2_quotient_tag =
            Op2::Quotient.allocate_constant(&mut cs.namespace(|| "op2_quotient_tag"));
        let op2_modulo_tag = Op2::Modulo.allocate_constant(&mut cs.namespace(|| "op2_modulo_tag"));
        let op2_numequal_tag =
            AllocatedNum::alloc_infallible(&mut cs.namespace(|| "op2_numequal_tag"), || {
                Op2::NumEqual.to_field()
            });
        let op2_less_tag = Op2::Less.allocate_constant(&mut cs.namespace(|| "op2_less_tag"));
        let op2_less_equal_tag =
            Op2::LessEqual.allocate_constant(&mut cs.namespace(|| "op2_less_equal_tag"));
        let op2_greater_tag =
            Op2::Greater.allocate_constant(&mut cs.namespace(|| "op2_greater_tag"));
        let op2_greater_equal_tag =
            Op2::GreaterEqual.allocate_constant(&mut cs.namespace(|| "op2_greater_equal_tag"));
        let op2_equal_tag =
            AllocatedNum::alloc_infallible(&mut cs.namespace(|| "op2_equal_tag"), || {
                Op2::Equal.to_field()
            });

        let c = store.expect_constants();

        macro_rules! defsym {
            ($var:ident, $name:expr, $cname:ident) => {
                let $var =
                    AllocatedPtr::alloc_constant(&mut cs.namespace(|| $name), c.$cname.z_ptr())?;
            };
        }

        defsym!(nil_ptr, "nil", nil);
        defsym!(t_ptr, "t", t);
        defsym!(dummy_arg_ptr, "_", dummy);
        defsym!(lambda_sym, "lambda", lambda);
        defsym!(quote_ptr, "quote", quote);

        let true_num = allocate_constant(&mut cs.namespace(|| "true"), F::ONE);
        let false_num = allocate_constant(&mut cs.namespace(|| "false"), F::ZERO);
        let default_num = allocate_constant(&mut cs.namespace(|| "default"), F::ZERO);

        let power2_32_ff = F::pow_vartime(&F::from_u64(2), [32]);
        let power2_32_num = allocate_constant(&mut cs.namespace(|| "pow(2,32)"), power2_32_ff);

        let power2_64_ff = F::pow_vartime(&F::from_u64(2), [64]);
        let power2_64_num = allocate_constant(&mut cs.namespace(|| "pow(2,64)"), power2_64_ff);

        Ok(Self {
            terminal_ptr,
            error_ptr_cont,
            error_ptr,
            dummy_ptr,
            nil_ptr,
            t_ptr,
            dummy_arg_ptr,
            empty_str_ptr,
            thunk_tag,
            cons_tag,
            char_tag,
            str_tag,
            num_tag,
            u64_tag,
            comm_tag,
            fun_tag,
            outermost_cont_tag,
            lookup_cont_tag,
            let_cont_tag,
            letrec_cont_tag,
            tail_cont_tag,
            call0_cont_tag,
            call_cont_tag,
            call2_cont_tag,
            unop_cont_tag,
            emit_cont_tag,
            binop_cont_tag,
            binop2_cont_tag,
            if_cont_tag,
            op1_car_tag,
            op1_cdr_tag,
            op1_commit_tag,
            op1_num_tag,
            op1_char_tag,
            op1_u64_tag,
            op1_comm_tag,
            op1_open_tag,
            op1_secret_tag,
            op1_atom_tag,
            op1_emit_tag,
            op2_cons_tag,
            op2_strcons_tag,
            op2_hide_tag,
            op2_begin_tag,
            op2_sum_tag,
            op2_diff_tag,
            op2_product_tag,
            op2_quotient_tag,
            op2_modulo_tag,
            op2_equal_tag,
            op2_numequal_tag,
            op2_less_tag,
            op2_less_equal_tag,
            op2_greater_tag,
            op2_greater_equal_tag,
            lambda_sym,
            quote_ptr,
            true_num,
            false_num,
            default_num,
            power2_32_num,
            power2_64_num,
        })
    }
}

pub(crate) fn hash_poseidon<CS: ConstraintSystem<F>, F: LurkField, A: Arity<F>>(
    mut cs: CS,
    preimage: Vec<AllocatedNum<F>>,
    constants: &PoseidonConstants<F, A>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    if cs.is_witness_generator() {
        poseidon_hash_allocated_witness(&mut cs, &preimage, constants)
    } else {
        poseidon_hash(cs, preimage, constants)
    }
}

pub(crate) fn allocate_constant<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    val: F,
) -> AllocatedNum<F> {
    let allocated = AllocatedNum::<F>::alloc_infallible(cs.namespace(|| "allocate"), || val);

    // allocated * 1 = val
    cs.enforce(
        || "enforce constant",
        |lc| lc + allocated.get_variable(),
        |lc| lc + CS::one(),
        |_| Boolean::Constant(true).lc(CS::one(), val),
    );

    allocated
}

impl ExprTag {
    pub fn allocate_constant<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> AllocatedNum<F> {
        allocate_constant(
            &mut cs.namespace(|| format!("{self:?} tag")),
            self.to_field(),
        )
    }
}

impl ContTag {
    pub fn allocate_constant<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> AllocatedNum<F> {
        allocate_constant(
            &mut cs.namespace(|| format!("{self:?} base continuation tag")),
            self.to_field(),
        )
    }
}

impl Op1 {
    pub fn allocate_constant<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> AllocatedNum<F> {
        allocate_constant(
            &mut cs.namespace(|| format!("{self:?} tag")),
            self.to_field(),
        )
    }
}

impl Op2 {
    pub fn allocate_constant<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> AllocatedNum<F> {
        allocate_constant(
            &mut cs.namespace(|| format!("{self:?} tag")),
            self.to_field(),
        )
    }
}
