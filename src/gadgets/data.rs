use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    ConstraintSystem, SynthesisError,
};
use blstrs::Scalar as Fr;
use ff::Field;
use neptune::circuit::poseidon_hash;

use crate::{eval::Witness, pool::ScalarPtr};
use crate::{
    gadgets::constraints::pick,
    pool::{ScalarContPtr, ScalarPointer},
};
use crate::{
    gadgets::pointer::AsAllocatedHashComponents,
    pool::{
        ContPtr, ContTag, Expression, Op1, Op2, Pointer, Pool, Ptr, Rel2, Tag, Thunk,
        POSEIDON_CONSTANTS_4, POSEIDON_CONSTANTS_6, POSEIDON_CONSTANTS_8,
    },
};

use super::pointer::{AllocatedContPtr, AllocatedPtr};

pub struct GlobalAllocations {
    pub terminal_ptr: AllocatedContPtr,
    pub outermost_ptr: AllocatedContPtr,
    pub error_ptr: AllocatedPtr,
    pub error_ptr_cont: AllocatedContPtr,
    pub dummy_ptr: AllocatedContPtr,
    pub nil_ptr: AllocatedPtr,
    pub t_ptr: AllocatedPtr,
    pub lambda_ptr: AllocatedPtr,
    pub dummy_arg_ptr: AllocatedPtr,

    pub sym_tag: AllocatedNum<Fr>,
    pub thunk_tag: AllocatedNum<Fr>,
    pub cons_tag: AllocatedNum<Fr>,
    pub num_tag: AllocatedNum<Fr>,
    pub fun_tag: AllocatedNum<Fr>,
    pub letstar_cont_tag: AllocatedNum<Fr>,
    pub letrecstar_cont_tag: AllocatedNum<Fr>,
    pub outermost_cont_tag: AllocatedNum<Fr>,
    pub lookup_cont_tag: AllocatedNum<Fr>,
    pub tail_cont_tag: AllocatedNum<Fr>,
    pub call_cont_tag: AllocatedNum<Fr>,
    pub call2_cont_tag: AllocatedNum<Fr>,
    pub unop_cont_tag: AllocatedNum<Fr>,
    pub binop_cont_tag: AllocatedNum<Fr>,
    pub relop_cont_tag: AllocatedNum<Fr>,
    pub binop2_cont_tag: AllocatedNum<Fr>,
    pub relop2_cont_tag: AllocatedNum<Fr>,
    pub if_cont_tag: AllocatedNum<Fr>,

    pub op1_car_tag: AllocatedNum<Fr>,
    pub op1_cdr_tag: AllocatedNum<Fr>,
    pub op1_atom_tag: AllocatedNum<Fr>,
    pub op2_cons_tag: AllocatedNum<Fr>,
    pub op2_sum_tag: AllocatedNum<Fr>,
    pub op2_diff_tag: AllocatedNum<Fr>,
    pub op2_product_tag: AllocatedNum<Fr>,
    pub op2_quotient_tag: AllocatedNum<Fr>,
    pub rel2_equal_tag: AllocatedNum<Fr>,
    pub rel2_numequal_tag: AllocatedNum<Fr>,

    pub true_num: AllocatedNum<Fr>,
    pub false_num: AllocatedNum<Fr>,
    pub default_num: AllocatedNum<Fr>,

    pub destructured_thunk_hash: AllocatedNum<Fr>,
    pub destructured_thunk_value: AllocatedPtr,
    pub destructured_thunk_continuation: AllocatedContPtr,
}

impl GlobalAllocations {
    pub fn new<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        pool: &Pool,
        witness: &Option<Witness>,
    ) -> Result<Self, SynthesisError> {
        let terminal_ptr = AllocatedContPtr::alloc_constant_cont_ptr(
            &mut cs.namespace(|| "terminal continuation"),
            pool,
            &pool.get_cont_terminal(),
        )?;

        let outermost_ptr = AllocatedContPtr::alloc_constant_cont_ptr(
            &mut cs.namespace(|| "outermost continuation"),
            pool,
            &pool.get_cont_outermost(),
        )?;

        // EVIL: fix usage of error
        let error_ptr = AllocatedPtr::constant_from_scalar_ptr(
            &mut cs.namespace(|| "error continuation (fake)"),
            &pool.get_scalar_ptr_error(),
        )?;

        let error_ptr_cont = AllocatedContPtr::alloc_constant_cont_ptr(
            &mut cs.namespace(|| "error continuation"),
            pool,
            &pool.get_cont_error(),
        )?;

        let dummy_ptr = AllocatedContPtr::alloc_constant_cont_ptr(
            &mut cs.namespace(|| "dummy continuation"),
            pool,
            &pool.get_cont_dummy(),
        )?;

        let nil_ptr =
            AllocatedPtr::constant_from_ptr(&mut cs.namespace(|| "nil"), pool, &pool.get_nil())?;
        let t_ptr = AllocatedPtr::constant_from_ptr(
            &mut cs.namespace(|| "T"),
            pool,
            &pool.get_sym("T").unwrap(),
        )?;
        let lambda_ptr = AllocatedPtr::constant_from_ptr(
            &mut cs.namespace(|| "LAMBDA"),
            pool,
            &pool.get_sym("LAMBDA").unwrap(),
        )?;
        let dummy_arg_ptr = AllocatedPtr::constant_from_ptr(
            &mut cs.namespace(|| "_"),
            pool,
            &pool.get_sym("_").unwrap(),
        )?;

        let sym_tag = Tag::Sym.allocate_constant(&mut cs.namespace(|| "sym_tag"))?;
        let thunk_tag = Tag::Thunk.allocate_constant(&mut cs.namespace(|| "thunk_tag"))?;
        let cons_tag = Tag::Cons.allocate_constant(&mut cs.namespace(|| "cons_tag"))?;
        let num_tag = Tag::Num.allocate_constant(&mut cs.namespace(|| "num_tag"))?;
        let fun_tag = Tag::Fun.allocate_constant(&mut cs.namespace(|| "fun_tag"))?;

        let outermost_cont_tag =
            ContTag::Outermost.allocate_constant(&mut cs.namespace(|| "outermost_cont_tag"))?;
        let lookup_cont_tag =
            ContTag::Lookup.allocate_constant(&mut cs.namespace(|| "lookup_cont_tag"))?;
        let letstar_cont_tag =
            ContTag::LetStar.allocate_constant(&mut cs.namespace(|| "letstar_cont_tag"))?;
        let letrecstar_cont_tag =
            ContTag::LetRecStar.allocate_constant(&mut cs.namespace(|| "letrecstar_cont_tag"))?;
        let tail_cont_tag =
            ContTag::Tail.allocate_constant(&mut cs.namespace(|| "tail_cont_tag"))?;
        let call_cont_tag =
            ContTag::Call.allocate_constant(&mut cs.namespace(|| "call_cont_tag"))?;
        let call2_cont_tag =
            ContTag::Call2.allocate_constant(&mut cs.namespace(|| "call2_cont_tag"))?;
        let unop_cont_tag =
            ContTag::Unop.allocate_constant(&mut cs.namespace(|| "unop_cont_tag"))?;
        let binop_cont_tag =
            ContTag::Binop.allocate_constant(&mut cs.namespace(|| "binop_cont_tag"))?;
        let relop_cont_tag =
            ContTag::Relop.allocate_constant(&mut cs.namespace(|| "relop_cont_tag"))?;
        let binop2_cont_tag =
            ContTag::Binop2.allocate_constant(&mut cs.namespace(|| "binop2_cont_tag"))?;
        let relop2_cont_tag =
            ContTag::Relop2.allocate_constant(&mut cs.namespace(|| "relop2_cont_tag"))?;
        let if_cont_tag = ContTag::If.allocate_constant(&mut cs.namespace(|| "if_cont_tag"))?;

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
                Ok(Rel2::NumEqual.as_field())
            })?;
        let rel2_equal_tag = AllocatedNum::alloc(&mut cs.namespace(|| "relop2_equal_tag"), || {
            Ok(Rel2::Equal.as_field())
        })?;

        let true_num = allocate_constant(&mut cs.namespace(|| "true"), Fr::one())?;
        let false_num = allocate_constant(&mut cs.namespace(|| "false"), Fr::zero())?;

        // NOTE: The choice of zero is significant.
        // For example, Ptr::default() has both tag and hash of zero.
        // let default_num = allocate_constant(, Fr::zero())?;
        let default_ptr = AllocatedPtr::constant_from_scalar_ptr(
            &mut cs.namespace(|| "default"),
            &pool.hash_default(),
        )?;
        let default_num = default_ptr.hash().clone();
        let _default_cont_ptr = AllocatedContPtr::alloc_constant(
            &mut cs.namespace(|| "default cont"),
            pool.hash_default_cont(),
        )?;

        let maybe_thunk = if let Some(w) = witness {
            w.destructured_thunk
        } else {
            None
        };
        let (destructured_thunk_hash, destructured_thunk_value, destructured_thunk_continuation) =
            Thunk::allocate_maybe_dummy_components(
                &mut cs.namespace(|| "allocate thunk components"),
                maybe_thunk.as_ref(),
                pool,
            )?;

        Ok(Self {
            terminal_ptr,
            outermost_ptr,
            error_ptr,
            error_ptr_cont,
            dummy_ptr,
            nil_ptr,
            t_ptr,
            lambda_ptr,
            dummy_arg_ptr,
            sym_tag,
            thunk_tag,
            cons_tag,
            num_tag,
            fun_tag,
            outermost_cont_tag,
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
            default_num,

            destructured_thunk_hash,
            destructured_thunk_value,
            destructured_thunk_continuation,
        })
    }
}

impl ContPtr {
    pub fn allocate_maybe_dummy_components<CS: ConstraintSystem<Fr>>(
        cs: CS,
        cont: Option<&ContPtr>,
        pool: &Pool,
    ) -> Result<(AllocatedNum<Fr>, Vec<AllocatedNum<Fr>>), SynthesisError> {
        if let Some(cont) = cont {
            if cont.is_default() {
                ContPtr::allocate_dummy_components(cs)
            } else {
                cont.allocate_components(cs, pool)
            }
        } else {
            ContPtr::allocate_dummy_components(cs)
        }
    }

    fn allocate_components<CS: ConstraintSystem<Fr>>(
        &self,
        mut cs: CS,
        pool: &Pool,
    ) -> Result<(AllocatedNum<Fr>, Vec<AllocatedNum<Fr>>), SynthesisError> {
        let component_frs = pool
            .get_hash_components_cont(self)
            .expect("missing hash components");

        let components: Vec<_> = component_frs
            .iter()
            .enumerate()
            .map(|(i, fr)| {
                AllocatedNum::alloc(
                    &mut cs.namespace(|| format!("alloc component {}", i)),
                    || Ok(*fr),
                )
            })
            .collect::<Result<_, _>>()?;

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
        let result: Vec<_> = (0..8)
            .map(|i| {
                AllocatedNum::alloc(
                    cs.namespace(|| format!("Continuation component {}", i)),
                    || Ok(Fr::zero()),
                )
            })
            .collect::<Result<_, _>>()?;

        // We need to create these constraints, but eventually we can avoid doing any calculation.
        // We just need a precomputed dummy witness.
        let dummy_hash = poseidon_hash(
            cs.namespace(|| "Continuation"),
            result.clone(),
            &POSEIDON_CONSTANTS_8,
        )?;

        dbg!(dummy_hash.get_value());

        Ok((dummy_hash, result))
    }
}

impl Ptr {
    pub fn allocate_maybe_fun<CS: ConstraintSystem<Fr>>(
        cs: CS,
        pool: &Pool,
        maybe_fun: Option<&Ptr>,
    ) -> Result<(AllocatedNum<Fr>, AllocatedPtr, AllocatedPtr, AllocatedPtr), SynthesisError> {
        match maybe_fun {
            Some(ptr) => match ptr.tag() {
                Tag::Fun => match pool.fetch(ptr).expect("missing fun") {
                    Expression::Fun(arg, body, closed_env) => {
                        let arg = pool.hash_expr(&arg).expect("missing arg");
                        let body = pool.hash_expr(&body).expect("missing body");
                        let closed_env = pool.hash_expr(&closed_env).expect("missing closed env");
                        Self::allocate_fun(cs, &arg, &body, &closed_env)
                    }
                    _ => unreachable!(),
                },
                _ => Self::allocate_dummy_fun(cs, pool),
            },
            _ => Self::allocate_dummy_fun(cs, pool),
        }
    }

    fn allocate_fun<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        arg: &ScalarPtr,
        body: &ScalarPtr,
        closed_env: &ScalarPtr,
    ) -> Result<(AllocatedNum<Fr>, AllocatedPtr, AllocatedPtr, AllocatedPtr), SynthesisError> {
        let arg_t = AllocatedPtr::from_scalar_ptr(&mut cs.namespace(|| "allocate arg"), Some(arg))?;
        let body_t =
            AllocatedPtr::from_scalar_ptr(&mut cs.namespace(|| "allocate body"), Some(body))?;
        let closed_env_t = AllocatedPtr::from_scalar_ptr(
            &mut cs.namespace(|| "allocate closed_env"),
            Some(closed_env),
        )?;

        let preimage = vec![
            arg_t.tag().clone(),
            arg_t.hash().clone(),
            body_t.tag().clone(),
            body_t.hash().clone(),
            closed_env_t.tag().clone(),
            closed_env_t.hash().clone(),
        ];

        let hash = poseidon_hash(cs.namespace(|| "Fun hash"), preimage, &POSEIDON_CONSTANTS_6)?;

        Ok((hash, arg_t, body_t, closed_env_t))
    }

    fn allocate_dummy_fun<CS: ConstraintSystem<Fr>>(
        cs: CS,
        pool: &Pool,
    ) -> Result<(AllocatedNum<Fr>, AllocatedPtr, AllocatedPtr, AllocatedPtr), SynthesisError> {
        let def = pool.hash_default();

        Self::allocate_fun(cs, &def, &def, &def)
    }

    pub fn construct_cons<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        g: &GlobalAllocations,
        car: &AllocatedPtr,
        cdr: &AllocatedPtr,
        _pool: &Pool,
    ) -> Result<AllocatedPtr, SynthesisError> {
        // This is actually binary_hash, considering creating that helper for use elsewhere.
        let preimage = vec![
            car.tag().clone(),
            car.hash().clone(),
            cdr.tag().clone(),
            cdr.hash().clone(),
        ];

        let hash = poseidon_hash(
            cs.namespace(|| "Cons hash"),
            preimage,
            &POSEIDON_CONSTANTS_4,
        )?;

        Ok(AllocatedPtr::from_allocated_parts_unchecked(
            g.cons_tag.clone(),
            hash,
            // pool,
        ))
    }

    pub fn construct_list<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        g: &GlobalAllocations,
        elts: &[&AllocatedPtr],
        pool: &Pool,
    ) -> Result<AllocatedPtr, SynthesisError> {
        if elts.is_empty() {
            Ok(g.nil_ptr.clone())
        } else {
            let tail =
                Self::construct_list(&mut cs.namespace(|| "Cons tail"), g, &elts[1..], pool)?;
            Self::construct_cons(&mut cs.namespace(|| "Cons"), g, elts[0], &tail, pool)
        }
    }

    pub fn construct_fun<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        g: &GlobalAllocations,
        arg: &AllocatedPtr,
        body: &AllocatedPtr,
        closed_env: &AllocatedPtr,
        pool: &Pool,
    ) -> Result<AllocatedPtr, SynthesisError> {
        let preimage = vec![
            arg.tag().clone(),
            arg.hash().clone(),
            body.tag().clone(),
            body.hash().clone(),
            closed_env.tag().clone(),
            closed_env.hash().clone(),
        ];

        let hash = poseidon_hash(cs.namespace(|| "Fun hash"), preimage, &POSEIDON_CONSTANTS_6)?;

        Ok(AllocatedPtr::from_allocated_parts(
            g.fun_tag.clone(),
            hash,
            pool,
        ))
    }
}

impl ContPtr {
    pub fn allocate_ptr<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
        pool: &Pool,
    ) -> Result<AllocatedContPtr, SynthesisError> {
        AllocatedContPtr::alloc(cs, || {
            pool.hash_cont(self)
                .ok_or(SynthesisError::AssignmentMissing)
        })
    }

    pub fn allocate_constant_ptr<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
        pool: &Pool,
    ) -> Result<AllocatedContPtr, SynthesisError> {
        let ptr = pool
            .hash_cont(self)
            .ok_or(SynthesisError::AssignmentMissing)?;
        AllocatedContPtr::alloc_constant(cs, ptr)
    }
}

pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
    cs: &mut CS,
    val: Fr,
) -> Result<AllocatedNum<Fr>, SynthesisError> {
    let allocated = AllocatedNum::<Fr>::alloc(cs.namespace(|| "allocate"), || Ok(val))?;

    // allocated * 1 = val
    cs.enforce(
        || "enforce constant",
        |lc| lc + allocated.get_variable(),
        |lc| lc + CS::one(),
        |_| Boolean::Constant(true).lc(CS::one(), val),
    );

    Ok(allocated)
}

impl Tag {
    pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        allocate_constant(
            &mut cs.namespace(|| format!("{:?} tag", self)),
            self.as_field(),
        )
    }
}

impl ContTag {
    pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        allocate_constant(
            &mut cs.namespace(|| format!("{:?} base continuation tag", self)),
            self.as_field(),
        )
    }
}

impl Op1 {
    pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        allocate_constant(
            &mut cs.namespace(|| format!("{:?} tag", self)),
            self.as_field(),
        )
    }
}

impl Op2 {
    pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        allocate_constant(
            &mut cs.namespace(|| format!("{:?} tag", self)),
            self.as_field(),
        )
    }
}

impl Rel2 {
    pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        allocate_constant(
            &mut cs.namespace(|| format!("{:?} tag", self)),
            self.as_field(),
        )
    }
}

impl Thunk {
    pub fn allocate_maybe_dummy_components<CS: ConstraintSystem<Fr>>(
        cs: CS,
        thunk: Option<&Thunk>,
        pool: &Pool,
    ) -> Result<(AllocatedNum<Fr>, AllocatedPtr, AllocatedContPtr), SynthesisError> {
        if let Some(thunk) = thunk {
            thunk.allocate_components(cs, pool)
        } else {
            Thunk::allocate_dummy_components(cs)
        }
    }

    // First component is the hash, which is wrong.
    pub fn allocate_components<CS: ConstraintSystem<Fr>>(
        &self,
        mut cs: CS,
        pool: &Pool,
    ) -> Result<(AllocatedNum<Fr>, AllocatedPtr, AllocatedContPtr), SynthesisError> {
        let component_frs = pool.get_hash_components_thunk(self);

        let value = AllocatedPtr::from_scalar_ptr(
            &mut cs.namespace(|| "Thunk component: value"),
            component_frs
                .as_ref()
                .map(|frs| ScalarPtr::from_parts(frs[0], frs[1]))
                .as_ref(),
        )?;

        let cont = AllocatedContPtr::alloc(
            &mut cs.namespace(|| "Thunk component: continuation"),
            || {
                component_frs
                    .as_ref()
                    .map(|frs| ScalarContPtr::from_parts(frs[2], frs[3]))
                    .ok_or(SynthesisError::AssignmentMissing)
            },
        )?;

        let hash = Self::hash_components(cs.namespace(|| "Thunk"), &value, &cont)?;

        Ok((hash, value, cont))
    }

    pub fn allocate_dummy_components<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
    ) -> Result<(AllocatedNum<Fr>, AllocatedPtr, AllocatedContPtr), SynthesisError> {
        let value = AllocatedPtr::from_scalar_ptr(
            &mut cs.namespace(|| "Thunk component: value"),
            Some(&ScalarPtr::from_parts(Fr::zero(), Fr::zero())),
        )?;

        let cont = AllocatedContPtr::alloc(
            &mut cs.namespace(|| "Thunk component: continuation"),
            || Ok(ScalarContPtr::from_parts(Fr::zero(), Fr::zero())),
        )?;

        let dummy_hash = Self::hash_components(cs.namespace(|| "Thunk"), &value, &cont)?;

        Ok((dummy_hash, value, cont))
    }

    pub fn hash_components<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        value: &AllocatedPtr,
        cont: &AllocatedContPtr,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        let vs = value.as_allocated_hash_components();
        let conts = cont.as_allocated_hash_components();
        // This is a 'binary' hash but has arity 4 because of tag and hash components for each item.
        let hash = poseidon_hash(
            cs.namespace(|| "Thunk Continuation"),
            vec![
                vs[0].clone(),
                vs[1].clone(),
                conts[0].clone(),
                conts[1].clone(),
            ],
            &POSEIDON_CONSTANTS_4,
        )?;

        Ok(hash)
    }
}

/// Takes two allocated numbers (`a`, `b`) and returns `a` if the condition is true, and `b` otherwise.
pub fn pick_ptr<CS>(
    mut cs: CS,
    condition: &Boolean,
    a: &AllocatedPtr,
    b: &AllocatedPtr,
    pool: &Pool,
) -> Result<AllocatedPtr, SynthesisError>
where
    CS: ConstraintSystem<Fr>,
{
    let tag = pick(cs.namespace(|| "tag"), condition, a.tag(), b.tag())?;
    let hash = pick(cs.namespace(|| "hash"), condition, a.hash(), b.hash())?;
    Ok(AllocatedPtr::from_allocated_parts(tag, hash, pool))
}
