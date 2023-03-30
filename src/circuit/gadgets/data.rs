use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    ConstraintSystem, SynthesisError,
};
use neptune::{
    circuit2::poseidon_hash_allocated as poseidon_hash,
    poseidon::{Arity, PoseidonConstants},
};

use super::pointer::AsAllocatedHashComponents;
use crate::field::LurkField;
use crate::store::ScalarContPtr;
use crate::store::{Expression, Pointer, Ptr, Store, Thunk};
use crate::store::{IntoHashComponents, ScalarPtr};
use crate::tag::{ContTag, ExprTag, Op1, Op2, Tag};

use super::pointer::{AllocatedContPtr, AllocatedPtr};

#[derive(Clone)]
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
        let error_ptr = AllocatedPtr::from_parts(error_ptr_cont.tag(), error_ptr_cont.hash());

        let dummy_ptr = AllocatedContPtr::alloc_constant_cont_ptr(
            &mut cs.namespace(|| "dummy continuation"),
            store,
            &store.get_cont_dummy(),
        )?;

        let empty_str_ptr = AllocatedPtr::alloc_constant_ptr(
            &mut cs.namespace(|| "empty_str_ptr"),
            store,
            &store.get_str("").unwrap(),
        )?;

        let thunk_tag = ExprTag::Thunk.allocate_constant(&mut cs.namespace(|| "thunk_tag"))?;
        let cons_tag = ExprTag::Cons.allocate_constant(&mut cs.namespace(|| "cons_tag"))?;
        let char_tag = ExprTag::Char.allocate_constant(&mut cs.namespace(|| "char_tag"))?;
        let str_tag = ExprTag::Str.allocate_constant(&mut cs.namespace(|| "str_tag"))?;
        let num_tag = ExprTag::Num.allocate_constant(&mut cs.namespace(|| "num_tag"))?;
        let u64_tag = ExprTag::U64.allocate_constant(&mut cs.namespace(|| "u64_tag"))?;
        let comm_tag = ExprTag::Comm.allocate_constant(&mut cs.namespace(|| "comm_tag"))?;
        let fun_tag = ExprTag::Fun.allocate_constant(&mut cs.namespace(|| "fun_tag"))?;

        let outermost_cont_tag =
            ContTag::Outermost.allocate_constant(&mut cs.namespace(|| "outermost_cont_tag"))?;
        let lookup_cont_tag =
            ContTag::Lookup.allocate_constant(&mut cs.namespace(|| "lookup_cont_tag"))?;
        let let_cont_tag = ContTag::Let.allocate_constant(&mut cs.namespace(|| "let_cont_tag"))?;
        let letrec_cont_tag =
            ContTag::LetRec.allocate_constant(&mut cs.namespace(|| "letrec_cont_tag"))?;
        let tail_cont_tag =
            ContTag::Tail.allocate_constant(&mut cs.namespace(|| "tail_cont_tag"))?;
        let call0_cont_tag =
            ContTag::Call0.allocate_constant(&mut cs.namespace(|| "call0_cont_tag"))?;
        let call_cont_tag =
            ContTag::Call.allocate_constant(&mut cs.namespace(|| "call_cont_tag"))?;
        let call2_cont_tag =
            ContTag::Call2.allocate_constant(&mut cs.namespace(|| "call2_cont_tag"))?;
        let unop_cont_tag =
            ContTag::Unop.allocate_constant(&mut cs.namespace(|| "unop_cont_tag"))?;
        let emit_cont_tag =
            ContTag::Emit.allocate_constant(&mut cs.namespace(|| "emit_cont_tag"))?;
        let binop_cont_tag =
            ContTag::Binop.allocate_constant(&mut cs.namespace(|| "binop_cont_tag"))?;
        let binop2_cont_tag =
            ContTag::Binop2.allocate_constant(&mut cs.namespace(|| "binop2_cont_tag"))?;
        let if_cont_tag = ContTag::If.allocate_constant(&mut cs.namespace(|| "if_cont_tag"))?;

        let op1_car_tag = Op1::Car.allocate_constant(&mut cs.namespace(|| "op1_car_tag"))?;
        let op1_cdr_tag = Op1::Cdr.allocate_constant(&mut cs.namespace(|| "op1_cdr_tag"))?;
        let op1_commit_tag =
            Op1::Commit.allocate_constant(&mut cs.namespace(|| "op1_commit_tag"))?;
        let op1_num_tag = Op1::Num.allocate_constant(&mut cs.namespace(|| "op1_num_tag"))?;
        let op1_char_tag = Op1::Char.allocate_constant(&mut cs.namespace(|| "op1_char_tag"))?;
        let op1_u64_tag = Op1::U64.allocate_constant(&mut cs.namespace(|| "op1_u64_tag"))?;
        let op1_comm_tag = Op1::Comm.allocate_constant(&mut cs.namespace(|| "op1_comm_tag"))?;
        let op1_open_tag = Op1::Open.allocate_constant(&mut cs.namespace(|| "op1_open_tag"))?;
        let op1_secret_tag =
            Op1::Secret.allocate_constant(&mut cs.namespace(|| "op1_secret_tag"))?;
        let op1_atom_tag = Op1::Atom.allocate_constant(&mut cs.namespace(|| "op1_atom_tag"))?;
        let op1_emit_tag = Op1::Emit.allocate_constant(&mut cs.namespace(|| "op1_emit_tag"))?;
        let op2_cons_tag = Op2::Cons.allocate_constant(&mut cs.namespace(|| "op2_cons_tag"))?;
        let op2_strcons_tag =
            Op2::StrCons.allocate_constant(&mut cs.namespace(|| "op2_strcons_tag"))?;
        let op2_hide_tag = Op2::Hide.allocate_constant(&mut cs.namespace(|| "op2_hide_tag"))?;
        let op2_begin_tag = Op2::Begin.allocate_constant(&mut cs.namespace(|| "op2_begin_tag"))?;
        let op2_sum_tag = Op2::Sum.allocate_constant(&mut cs.namespace(|| "op2_sum_tag"))?;
        let op2_diff_tag = Op2::Diff.allocate_constant(&mut cs.namespace(|| "op2_diff_tag"))?;

        let op2_product_tag =
            Op2::Product.allocate_constant(&mut cs.namespace(|| "op2_product_tag"))?;
        let op2_quotient_tag =
            Op2::Quotient.allocate_constant(&mut cs.namespace(|| "op2_quotient_tag"))?;
        let op2_modulo_tag =
            Op2::Modulo.allocate_constant(&mut cs.namespace(|| "op2_modulo_tag"))?;
        let op2_numequal_tag =
            AllocatedNum::alloc(&mut cs.namespace(|| "op2_numequal_tag"), || {
                Ok(Op2::NumEqual.to_field())
            })?;
        let op2_less_tag = Op2::Less.allocate_constant(&mut cs.namespace(|| "op2_less_tag"))?;
        let op2_less_equal_tag =
            Op2::LessEqual.allocate_constant(&mut cs.namespace(|| "op2_less_equal_tag"))?;
        let op2_greater_tag =
            Op2::Greater.allocate_constant(&mut cs.namespace(|| "op2_greater_tag"))?;
        let op2_greater_equal_tag =
            Op2::GreaterEqual.allocate_constant(&mut cs.namespace(|| "op2_greater_equal_tag"))?;
        let op2_equal_tag = AllocatedNum::alloc(&mut cs.namespace(|| "op2_equal_tag"), || {
            Ok(Op2::Equal.to_field())
        })?;

        let c = store.get_constants();

        macro_rules! defsym {
            ($var:ident, $name:expr, $cname:ident) => {
                let $var = AllocatedPtr::alloc_constant(
                    &mut cs.namespace(|| $name),
                    c.$cname.scalar_ptr(),
                )?;
            };
        }

        defsym!(nil_ptr, "nil", nil);
        defsym!(t_ptr, "t", t);
        defsym!(dummy_arg_ptr, "_", dummy);
        defsym!(lambda_sym, "lambda", lambda);

        let true_num = allocate_constant(&mut cs.namespace(|| "true"), F::one())?;
        let false_num = allocate_constant(&mut cs.namespace(|| "false"), F::zero())?;
        let default_num = allocate_constant(&mut cs.namespace(|| "default"), F::zero())?;

        let power2_32_ff = F::pow_vartime(&F::from_u64(2), [32]);
        let power2_32_num = allocate_constant(&mut cs.namespace(|| "pow(2,32)"), power2_32_ff)?;

        let power2_64_ff = F::pow_vartime(&F::from_u64(2), [64]);
        let power2_64_num = allocate_constant(&mut cs.namespace(|| "pow(2,64)"), power2_64_ff)?;

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
            true_num,
            false_num,
            default_num,
            power2_32_num,
            power2_64_num,
        })
    }
}

pub fn hash_poseidon<CS: ConstraintSystem<F>, F: LurkField, A: Arity<F>>(
    cs: CS,
    preimage: Vec<AllocatedNum<F>>,
    constants: &PoseidonConstants<F, A>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    poseidon_hash(cs, preimage, constants)
}

impl<F: LurkField> Ptr<F> {
    pub fn allocate_maybe_fun_unconstrained<CS: ConstraintSystem<F>>(
        cs: CS,
        store: &Store<F>,
        maybe_fun: Option<&Ptr<F>>,
    ) -> Result<
        (
            AllocatedNum<F>,
            AllocatedPtr<F>,
            AllocatedPtr<F>,
            AllocatedPtr<F>,
        ),
        SynthesisError,
    > {
        match maybe_fun.map(|ptr| (ptr, ptr.tag())) {
            Some((ptr, ExprTag::Fun)) => match store.fetch(ptr).expect("missing fun") {
                Expression::Fun(arg, body, closed_env) => {
                    let arg = store.get_expr_hash(&arg).expect("missing arg");
                    let body = store.get_expr_hash(&body).expect("missing body");
                    let closed_env = store
                        .get_expr_hash(&closed_env)
                        .expect("missing closed env");
                    Self::allocate_fun(cs, store, arg, body, closed_env)
                }
                _ => unreachable!(),
            },
            _ => Self::allocate_dummy_fun(cs, store),
        }
    }

    fn allocate_fun<CS: ConstraintSystem<F>, T: IntoHashComponents<F>>(
        mut cs: CS,
        store: &Store<F>,
        arg: T,
        body: T,
        closed_env: T,
    ) -> Result<
        (
            AllocatedNum<F>,
            AllocatedPtr<F>,
            AllocatedPtr<F>,
            AllocatedPtr<F>,
        ),
        SynthesisError,
    > {
        let arg_t =
            AllocatedPtr::alloc_hash_components(&mut cs.namespace(|| "allocate arg tag"), arg)?;
        let body_t =
            AllocatedPtr::alloc_hash_components(&mut cs.namespace(|| "allocate body tag"), body)?;
        let closed_env_t = AllocatedPtr::alloc_hash_components(
            &mut cs.namespace(|| "allocate closed_env tag"),
            closed_env,
        )?;

        let preimage = vec![
            arg_t.tag().clone(),
            arg_t.hash().clone(),
            body_t.tag().clone(),
            body_t.hash().clone(),
            closed_env_t.tag().clone(),
            closed_env_t.hash().clone(),
        ];

        let hash = hash_poseidon(
            cs.namespace(|| "Fun hash"),
            preimage,
            store.poseidon_constants().c6(),
        )?;

        Ok((hash, arg_t, body_t, closed_env_t))
    }

    fn allocate_dummy_fun<CS: ConstraintSystem<F>>(
        cs: CS,
        store: &Store<F>,
    ) -> Result<
        (
            AllocatedNum<F>,
            AllocatedPtr<F>,
            AllocatedPtr<F>,
            AllocatedPtr<F>,
        ),
        SynthesisError,
    > {
        Self::allocate_fun(
            cs,
            store,
            [F::zero(), F::zero()],
            [F::zero(), F::zero()],
            [F::zero(), F::zero()],
        )
    }
}

pub fn allocate_constant<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    val: F,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let allocated = AllocatedNum::<F>::alloc(cs.namespace(|| "allocate"), || Ok(val))?;

    // allocated * 1 = val
    cs.enforce(
        || "enforce constant",
        |lc| lc + allocated.get_variable(),
        |lc| lc + CS::one(),
        |_| Boolean::Constant(true).lc(CS::one(), val),
    );

    Ok(allocated)
}

impl ExprTag {
    pub fn allocate_constant<F: LurkField, CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
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
    ) -> Result<AllocatedNum<F>, SynthesisError> {
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
    ) -> Result<AllocatedNum<F>, SynthesisError> {
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
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        allocate_constant(
            &mut cs.namespace(|| format!("{self:?} tag")),
            self.to_field(),
        )
    }
}

impl<F: LurkField> Thunk<F> {
    pub fn allocate_maybe_dummy_components<CS: ConstraintSystem<F>>(
        cs: CS,
        thunk: Option<&Thunk<F>>,
        store: &Store<F>,
    ) -> Result<(AllocatedNum<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        if let Some(thunk) = thunk {
            thunk.allocate_components(cs, store)
        } else {
            Thunk::allocate_dummy_components(cs, store)
        }
    }

    // First component is the hash, which is wrong.
    pub fn allocate_components<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        store: &Store<F>,
    ) -> Result<(AllocatedNum<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        let component_frs = store.get_hash_components_thunk(self);

        let value = AllocatedPtr::alloc(&mut cs.namespace(|| "Thunk component: value"), || {
            component_frs
                .as_ref()
                .and_then(|frs| {
                    let opt_tag = ExprTag::from_field(&frs[0]);
                    opt_tag.map(|tag| ScalarPtr::from_parts(tag, frs[1]))
                })
                .ok_or(SynthesisError::AssignmentMissing)
        })?;

        let cont = AllocatedContPtr::alloc(
            &mut cs.namespace(|| "Thunk component: continuation"),
            || {
                component_frs
                    .as_ref()
                    .and_then(|frs| {
                        let opt_tag = ContTag::from_field(&frs[2]);
                        opt_tag.map(|tag| ScalarContPtr::from_parts(tag, frs[3]))
                    })
                    .ok_or(SynthesisError::AssignmentMissing)
            },
        )?;

        let hash = Self::hash_components(cs.namespace(|| "Thunk"), store, &value, &cont)?;

        Ok((hash, value, cont))
    }

    pub fn allocate_dummy_components<CS: ConstraintSystem<F>>(
        mut cs: CS,
        store: &Store<F>,
    ) -> Result<(AllocatedNum<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        let value = AllocatedPtr::alloc(&mut cs.namespace(|| "Thunk component: value"), || {
            Ok(ScalarPtr::from_parts(ExprTag::Nil, F::zero()))
        })?;

        let cont = AllocatedContPtr::alloc(
            &mut cs.namespace(|| "Thunk component: continuation"),
            || Ok(ScalarContPtr::from_parts(ContTag::Dummy, F::zero())),
        )?;

        let dummy_hash = Self::hash_components(cs.namespace(|| "Thunk"), store, &value, &cont)?;

        Ok((dummy_hash, value, cont))
    }

    pub fn hash_components<CS: ConstraintSystem<F>>(
        mut cs: CS,
        store: &Store<F>,
        value: &AllocatedPtr<F>,
        cont: &AllocatedContPtr<F>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let vs = value.as_allocated_hash_components();
        let conts = cont.as_allocated_hash_components();
        // This is a 'binary' hash but has arity 4 because of tag and hash components for each item.
        let hash = hash_poseidon(
            cs.namespace(|| "Thunk Continuation"),
            vec![
                vs[0].clone(),
                vs[1].clone(),
                conts[0].clone(),
                conts[1].clone(),
            ],
            store.poseidon_constants().c4(),
        )?;

        Ok(hash)
    }
}
