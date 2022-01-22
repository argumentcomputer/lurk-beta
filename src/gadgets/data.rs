use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    ConstraintSystem, SynthesisError,
};
use blstrs::Scalar as Fr;
use ff::Field;
use neptune::circuit::poseidon_hash;

use crate::pool::{
    ContPtr, ContTag, Expression, Op1, Op2, Pool, Ptr, Rel2, Tag, Thunk, POSEIDON_CONSTANTS_4,
    POSEIDON_CONSTANTS_6, POSEIDON_CONSTANTS_8,
};
use crate::{eval::Witness, pool::ScalarPtr};
use crate::{
    gadgets::constraints::{alloc_equal, equal, pick},
    writer::Write,
};

#[derive(Clone)]
pub struct AllocatedPtr {
    tag: AllocatedNum<Fr>,
    hash: AllocatedNum<Fr>,
}

impl AllocatedPtr {
    pub fn tag(&self) -> &AllocatedNum<Fr> {
        &self.tag
    }

    pub fn hash(&self) -> &AllocatedNum<Fr> {
        &self.hash
    }

    pub fn get_tag_value(&self) -> Option<Fr> {
        self.tag.get_value()
    }

    pub fn get_hash_value(&self) -> Option<Fr> {
        self.hash.get_value()
    }

    pub fn from_allocated_parts(tag: AllocatedNum<Fr>, hash: AllocatedNum<Fr>) -> Self {
        Self { tag, hash }
    }

    pub fn from_unallocated_parts<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        unallocated_tag: Fr,
        unallocated_hash: Fr,
    ) -> Result<Self, SynthesisError> {
        let tag = AllocatedNum::alloc(&mut cs.namespace(|| "tag"), || Ok(unallocated_tag))?;
        let hash = AllocatedNum::alloc(&mut cs.namespace(|| "hash"), || Ok(unallocated_hash))?;
        Ok(Self { tag, hash })
    }

    pub fn from_ptr<CS>(cs: &mut CS, pool: &Pool, ptr: Option<&Ptr>) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Fr>,
    {
        let scalar_ptr = ptr.and_then(|ptr| pool.hash_expr(ptr));
        Self::from_scalar_ptr(cs, scalar_ptr.as_ref())
    }

    pub fn constant_from_ptr<CS>(
        cs: &mut CS,
        pool: &Pool,
        ptr: &Ptr,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Fr>,
    {
        let scalar_ptr = pool.hash_expr(ptr).expect("missing constant ptr");
        Self::constant_from_scalar_ptr(cs, &scalar_ptr)
    }

    pub fn from_cont_ptr<CS>(
        cs: &mut CS,
        pool: &Pool,
        ptr: Option<&ContPtr>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Fr>,
    {
        let scalar_ptr = ptr.and_then(|ptr| pool.hash_cont(ptr));
        Self::from_scalar_ptr(cs, scalar_ptr.as_ref())
    }

    pub fn constant_from_cont_ptr<CS>(
        cs: &mut CS,
        pool: &Pool,
        ptr: &ContPtr,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Fr>,
    {
        let scalar_ptr = pool.hash_cont(ptr).expect("missing const cont ptr");
        Self::constant_from_scalar_ptr(cs, &scalar_ptr)
    }

    pub fn from_scalar_ptr<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        ptr: Option<&ScalarPtr>,
    ) -> Result<Self, SynthesisError> {
        let tag = AllocatedNum::alloc(&mut cs.namespace(|| "allocate tag"), || {
            ptr.map(|x| *x.tag())
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        let hash = AllocatedNum::alloc(&mut cs.namespace(|| "allocate hash"), || {
            ptr.map(|x| *x.value())
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        Ok(Self::from_allocated_parts(tag, hash))
    }

    pub fn constant_from_scalar_ptr<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        ptr: &ScalarPtr,
    ) -> Result<Self, SynthesisError> {
        let tag = allocate_constant(&mut cs.namespace(|| "allocate tag"), *ptr.tag())?;
        let hash = allocate_constant(&mut cs.namespace(|| "allocate hash"), *ptr.value())?;
        Ok(Self::from_allocated_parts(tag, hash))
    }

    pub fn enforce_equal<CS: ConstraintSystem<Fr>>(&self, cs: &mut CS, other: &Self) {
        equal(cs, || "tags equal", &self.tag, &other.tag);
        equal(cs, || "hashes equal", &self.hash, &other.hash);
    }

    pub fn alloc_equal<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Boolean, SynthesisError> {
        let tags_equal = alloc_equal(&mut cs.namespace(|| "tags equal"), &self.tag, &other.tag)?;
        let hashes_equal = alloc_equal(
            &mut cs.namespace(|| "hashes equal"),
            &self.hash,
            &other.hash,
        )?;

        Boolean::and(
            &mut cs.namespace(|| "tags and hashes equal"),
            &tags_equal,
            &hashes_equal,
        )
    }

    pub fn ptr(&self) -> Option<ScalarPtr> {
        match (self.tag.get_value(), self.hash.get_value()) {
            (Some(tag), Some(value)) => Some(ScalarPtr::from_parts(tag, value)),
            _ => None,
        }
    }

    pub fn fetch_and_write_str(&self, pool: &Pool) -> String {
        if let Some(aaa) = &self.ptr() {
            if let Some(bbb) = pool.fetch_scalar(aaa) {
                bbb.fmt_to_string(pool)
            } else {
                format!("expression not found in pool: {:?}", aaa)
            }
        } else {
            "no Ptr".to_string()
        }
    }
    pub fn fetch_and_write_cont_str(&self, pool: &Pool) -> String {
        if let Some(aaa) = &self.ptr() {
            if let Some(bbb) = pool.fetch_scalar_cont(aaa) {
                bbb.fmt_to_string(pool)
            } else {
                format!("continuation not found in pool: {:?}", aaa)
            }
        } else {
            "no Ptr".to_string()
        }
    }

    pub fn allocate_thunk_components<CS: ConstraintSystem<Fr>>(
        &self,
        cs: CS,
        pool: &Pool,
    ) -> Result<(AllocatedNum<Fr>, AllocatedPtr, AllocatedPtr), SynthesisError> {
        let maybe_thunk = self
            .ptr()
            .and_then(|ptr| pool.fetch_scalar(&ptr))
            .and_then(|ptr| pool.fetch(&ptr))
            .and_then(|expr| {
                if let Expression::Thunk(thunk) = expr {
                    Some(thunk)
                } else {
                    None
                }
            });
        Thunk::allocate_maybe_dummy_components(cs, maybe_thunk.as_ref(), pool)
    }
}

pub struct GlobalAllocations {
    pub terminal_ptr: AllocatedPtr,
    pub outermost_ptr: AllocatedPtr,
    pub error_ptr: AllocatedPtr,
    pub dummy_ptr: AllocatedPtr,
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

    pub op1_car_ptr: AllocatedPtr,
    pub op1_cdr_ptr: AllocatedPtr,
    pub op1_atom_ptr: AllocatedPtr,
    pub op2_cons_ptr: AllocatedPtr,
    pub op2_sum_ptr: AllocatedPtr,
    pub op2_diff_ptr: AllocatedPtr,
    pub op2_product_ptr: AllocatedPtr,
    pub op2_quotient_ptr: AllocatedPtr,
    pub rel2_equal_ptr: AllocatedPtr,
    pub rel2_numequal_ptr: AllocatedPtr,

    pub true_num: AllocatedNum<Fr>,
    pub false_num: AllocatedNum<Fr>,

    pub default: AllocatedNum<Fr>,

    pub destructured_thunk_hash: AllocatedNum<Fr>,
    pub destructured_thunk_value: AllocatedPtr,
    pub destructured_thunk_continuation: AllocatedPtr,
}

impl GlobalAllocations {
    pub fn new<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        pool: &Pool,
        witness: &Option<Witness>,
    ) -> Result<Self, SynthesisError> {
        let terminal_ptr = AllocatedPtr::constant_from_cont_ptr(
            &mut cs.namespace(|| "terminal continuation"),
            pool,
            &pool.get_cont_terminal(),
        )?;

        let outermost_ptr = AllocatedPtr::constant_from_cont_ptr(
            &mut cs.namespace(|| "outermost continuation"),
            pool,
            &pool.get_cont_outermost(),
        )?;

        let error_ptr = AllocatedPtr::constant_from_cont_ptr(
            &mut cs.namespace(|| "error continuation"),
            pool,
            &pool.get_cont_error(),
        )?;

        let dummy_ptr = AllocatedPtr::constant_from_cont_ptr(
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

        let nil_tag = nil_ptr.tag.clone(); //Tag::Nil.allocate_constant(&mut cs.namespace(|| "nil_tag"))?;
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
        let op1_car_ptr = AllocatedPtr::from_allocated_parts(op1_car_tag, nil_tag.clone());

        let op1_cdr_tag = Op1::Cdr.allocate_constant(&mut cs.namespace(|| "op1_cdr_tag"))?;
        let op1_cdr_ptr = AllocatedPtr::from_allocated_parts(op1_cdr_tag, nil_tag.clone());

        let op1_atom_tag = Op1::Atom.allocate_constant(&mut cs.namespace(|| "op1_atom_tag"))?;
        let op1_atom_ptr = AllocatedPtr::from_allocated_parts(op1_atom_tag, nil_tag.clone());

        let op2_cons_tag = Op2::Cons.allocate_constant(&mut cs.namespace(|| "op2_cons_tag"))?;
        let op2_cons_ptr = AllocatedPtr::from_allocated_parts(op2_cons_tag, nil_tag.clone());

        let op2_sum_tag = Op2::Sum.allocate_constant(&mut cs.namespace(|| "op2_sum_tag"))?;
        let op2_sum_ptr = AllocatedPtr::from_allocated_parts(op2_sum_tag, nil_tag.clone());

        let op2_diff_tag = Op2::Diff.allocate_constant(&mut cs.namespace(|| "op2_diff_tag"))?;
        let op2_diff_ptr = AllocatedPtr::from_allocated_parts(op2_diff_tag, nil_tag.clone());

        let op2_product_tag =
            Op2::Product.allocate_constant(&mut cs.namespace(|| "op2_product_tag"))?;
        let op2_product_ptr = AllocatedPtr::from_allocated_parts(op2_product_tag, nil_tag.clone());

        let op2_quotient_tag =
            Op2::Quotient.allocate_constant(&mut cs.namespace(|| "op2_quotient_tag"))?;
        let op2_quotient_ptr =
            AllocatedPtr::from_allocated_parts(op2_quotient_tag, nil_tag.clone());

        let rel2_numequal_tag =
            AllocatedNum::alloc(&mut cs.namespace(|| "relop2_numequal_tag"), || {
                Ok(Rel2::NumEqual.as_field())
            })?;
        let rel2_numequal_ptr =
            AllocatedPtr::from_allocated_parts(rel2_numequal_tag, nil_tag.clone());

        let rel2_equal_tag = AllocatedNum::alloc(&mut cs.namespace(|| "relop2_equal_tag"), || {
            Ok(Rel2::Equal.as_field())
        })?;
        let rel2_equal_ptr = AllocatedPtr::from_allocated_parts(rel2_equal_tag, nil_tag);

        let true_num = allocate_constant(&mut cs.namespace(|| "true"), Fr::one())?;
        let false_num = allocate_constant(&mut cs.namespace(|| "false"), Fr::zero())?;

        // NOTE: The choice of zero is significant.
        // For example, Ptr::default() has both tag and hash of zero.
        let default = allocate_constant(&mut cs.namespace(|| "default"), Fr::zero())?;

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
            op1_car_ptr,
            op1_cdr_ptr,
            op1_atom_ptr,
            op2_cons_ptr,
            op2_sum_ptr,
            op2_diff_ptr,
            op2_product_ptr,
            op2_quotient_ptr,
            rel2_equal_ptr,
            rel2_numequal_ptr,
            true_num,
            false_num,
            default,

            destructured_thunk_hash,
            destructured_thunk_value,
            destructured_thunk_continuation,
        })
    }
}

impl Ptr {
    pub fn allocate_ptr<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
        pool: &Pool,
    ) -> Result<AllocatedPtr, SynthesisError> {
        let scalar_ptr = pool.hash_expr(self).expect("missing ptr");
        scalar_ptr.allocate_ptr(cs)
    }

    pub fn allocate_constant_ptr<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
        pool: &Pool,
    ) -> Result<AllocatedPtr, SynthesisError> {
        dbg!(self);
        let scalar_ptr = pool.hash_expr(self).expect("missing ptr");
        scalar_ptr.allocate_constant_ptr(cs)
    }
}

impl ScalarPtr {
    pub fn allocate_ptr<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedPtr, SynthesisError> {
        AllocatedPtr::from_scalar_ptr(cs, Some(self))
    }

    pub fn allocate_constant_ptr<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedPtr, SynthesisError> {
        let allocated_tag = allocate_constant(&mut cs.namespace(|| "tag"), *self.tag())?;
        let allocated_hash = allocate_constant(&mut cs.namespace(|| "hash"), *self.value())?;

        Ok(AllocatedPtr::from_allocated_parts(
            allocated_tag,
            allocated_hash,
        ))
    }
}

impl ContPtr {
    pub fn allocate_maybe_dummy_components<CS: ConstraintSystem<Fr>>(
        cs: CS,
        cont: Option<&ContPtr>,
        pool: &Pool,
    ) -> Result<(AllocatedNum<Fr>, Vec<AllocatedPtr>), SynthesisError> {
        if let Some(cont) = cont {
            cont.allocate_components(cs, pool)
        } else {
            ContPtr::allocate_dummy_components(cs)
        }
    }

    fn allocate_components<CS: ConstraintSystem<Fr>>(
        &self,
        mut cs: CS,
        pool: &Pool,
    ) -> Result<(AllocatedNum<Fr>, Vec<AllocatedPtr>), SynthesisError> {
        let component_ptrs: Vec<_> = pool
            .get_hash_components_cont(self)
            .expect("missing hash components")
            .iter()
            .enumerate()
            .map(|(i, ptr)| {
                AllocatedPtr::from_scalar_ptr(
                    &mut cs.namespace(|| format!("Continuation support {}", i)),
                    Some(ptr),
                )
            })
            .collect::<Result<_, _>>()?;

        let mut components = Vec::with_capacity(8);

        for ptr in component_ptrs.iter() {
            components.push(ptr.tag().clone());
            components.push(ptr.hash().clone());
        }

        let hash = poseidon_hash(
            cs.namespace(|| "Continuation"),
            components,
            &POSEIDON_CONSTANTS_8,
        )?;
        Ok((hash, component_ptrs))
    }

    fn allocate_dummy_components<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
    ) -> Result<(AllocatedNum<Fr>, Vec<AllocatedPtr>), SynthesisError> {
        let length = 8;
        let mut result = Vec::with_capacity(length);
        for i in 0..length {
            result.push(AllocatedNum::alloc(
                cs.namespace(|| format!("Continuation component {}", i)),
                || Ok(Fr::zero()),
            )?);
        }
        let mut result_ptrs = Vec::with_capacity(4);
        for chunk in result.chunks(2) {
            result_ptrs.push(AllocatedPtr::from_allocated_parts(
                chunk[0].clone(),
                chunk[1].clone(),
            ));
        }

        // We need to create these constraints, but eventually we can avoid doing any calculation.
        // We just need a precomputed dummy witness.
        let dummy_hash = poseidon_hash(
            cs.namespace(|| "Continuation"),
            result,
            &POSEIDON_CONSTANTS_8,
        )?;

        Ok((dummy_hash, result_ptrs))
    }

    pub fn construct<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        cont_tag: &AllocatedNum<Fr>,
        ptrs: &[&AllocatedPtr; 4],
    ) -> Result<AllocatedPtr, SynthesisError> {
        let mut components = Vec::with_capacity(8);
        for ptr in ptrs {
            components.push(ptr.tag().clone());
            components.push(ptr.hash().clone());
        }
        let hash = poseidon_hash(
            cs.namespace(|| "Continuation"),
            components,
            &POSEIDON_CONSTANTS_8,
        )?;

        let cont = AllocatedPtr::from_allocated_parts(cont_tag.clone(), hash);
        Ok(cont)
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

        let preimage = {
            let arg_t = arg_t.clone();
            let body_t = body_t.clone();
            let closed_env_t = closed_env_t.clone();
            vec![
                arg_t.tag,
                arg_t.hash,
                body_t.tag,
                body_t.hash,
                closed_env_t.tag,
                closed_env_t.hash,
            ]
        };
        let hash = poseidon_hash(cs.namespace(|| "Fun hash"), preimage, &POSEIDON_CONSTANTS_6)?;

        Ok((hash, arg_t, body_t, closed_env_t))
    }

    fn allocate_dummy_fun<CS: ConstraintSystem<Fr>>(
        cs: CS,
        pool: &Pool,
    ) -> Result<(AllocatedNum<Fr>, AllocatedPtr, AllocatedPtr, AllocatedPtr), SynthesisError> {
        let nil = pool.hash_nil();

        Self::allocate_fun(cs, &nil, &nil, &nil)
    }

    pub fn construct_cons<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        g: &GlobalAllocations,
        a: &AllocatedPtr,
        b: &AllocatedPtr,
    ) -> Result<AllocatedPtr, SynthesisError> {
        // This is actually binary_hash, considering creating that helper for use elsewhere.
        let preimage = vec![a.tag.clone(), a.hash.clone(), b.tag.clone(), b.hash.clone()];

        let hash = poseidon_hash(
            cs.namespace(|| "Cons hash"),
            preimage,
            &POSEIDON_CONSTANTS_4,
        )?;
        Ok(AllocatedPtr::from_allocated_parts(g.cons_tag.clone(), hash))
    }

    pub fn construct_list<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        g: &GlobalAllocations,
        elts: &[&AllocatedPtr],
    ) -> Result<AllocatedPtr, SynthesisError> {
        if elts.is_empty() {
            Ok(g.nil_ptr.clone())
        } else {
            let tail = Self::construct_list(&mut cs.namespace(|| "Cons tail"), g, &elts[1..])?;
            Self::construct_cons(&mut cs.namespace(|| "Cons"), g, elts[0], &tail)
        }
    }

    pub fn construct_fun<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        g: &GlobalAllocations,
        arg: &AllocatedPtr,
        body: &AllocatedPtr,
        closed_env: &AllocatedPtr,
    ) -> Result<AllocatedPtr, SynthesisError> {
        let preimage = vec![
            arg.tag.clone(),
            arg.hash.clone(),
            body.tag.clone(),
            body.hash.clone(),
            closed_env.tag.clone(),
            closed_env.hash.clone(),
        ];

        let hash = poseidon_hash(cs.namespace(|| "Fun hash"), preimage, &POSEIDON_CONSTANTS_6)?;
        Ok(AllocatedPtr::from_allocated_parts(g.fun_tag.clone(), hash))
    }
}

impl ContPtr {
    pub fn allocate_ptr<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
        pool: &Pool,
    ) -> Result<AllocatedPtr, SynthesisError> {
        let scalar_ptr = pool.hash_cont(self).expect("missing continuation");
        scalar_ptr.allocate_ptr(cs)
    }

    pub fn allocate_constant_ptr<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
        pool: &Pool,
    ) -> Result<AllocatedPtr, SynthesisError> {
        let scalar_ptr = pool.hash_cont(self).expect("missing continuation");
        scalar_ptr.allocate_constant_ptr(cs)
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
    ) -> Result<(AllocatedNum<Fr>, AllocatedPtr, AllocatedPtr), SynthesisError> {
        let (hash, components) = if let Some(thunk) = thunk {
            thunk.allocate_components(cs, pool)
        } else {
            Thunk::allocate_dummy_components(cs)
        }?;

        // allocate_thunk_components should probably returned AllocatedPtres.
        let thunk_value =
            AllocatedPtr::from_allocated_parts(components[0].clone(), components[1].clone());

        let thunk_continuation =
            AllocatedPtr::from_allocated_parts(components[2].clone(), components[3].clone());

        Ok((hash, thunk_value, thunk_continuation))
    }

    // First component is the hash, which is wrong.
    pub fn allocate_components<CS: ConstraintSystem<Fr>>(
        &self,
        mut cs: CS,
        pool: &Pool,
    ) -> Result<(AllocatedNum<Fr>, Vec<AllocatedNum<Fr>>), SynthesisError> {
        let component_ptrs = pool
            .get_hash_components_thunk(self)
            .expect("missing hash components");
        let mut components = Vec::with_capacity(4);

        let mut i = 0;
        for ptr in component_ptrs.iter() {
            components.push(AllocatedNum::alloc(
                cs.namespace(|| format!("Thunk component {}", i)),
                || Ok(*ptr.tag()),
            )?);
            i += 1;
            components.push(AllocatedNum::alloc(
                cs.namespace(|| format!("Thunk component {}", i)),
                || Ok(*ptr.value()),
            )?);
            i += 1;
        }

        let hash = Self::hash_components(cs.namespace(|| "Thunk"), &components.clone())?;

        Ok((hash, components))
    }

    pub fn allocate_dummy_components<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
    ) -> Result<(AllocatedNum<Fr>, Vec<AllocatedNum<Fr>>), SynthesisError> {
        let length = 4;
        let mut result = Vec::with_capacity(length);
        for i in 0..length {
            result.push(AllocatedNum::alloc(
                cs.namespace(|| format!("Thunk component {}", i)),
                || Ok(Fr::zero()),
            )?);
        }

        let dummy_hash = Self::hash_components(cs.namespace(|| "Thunk"), &result)?;

        Ok((dummy_hash, result))
    }

    pub fn hash_components<CS: ConstraintSystem<Fr>>(
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

/// Takes two allocated numbers (`a`, `b`) and returns `a` if the condition is true, and `b` otherwise.
pub fn pick_ptr<CS>(
    mut cs: CS,
    condition: &Boolean,
    a: &AllocatedPtr,
    b: &AllocatedPtr,
) -> Result<AllocatedPtr, SynthesisError>
where
    CS: ConstraintSystem<Fr>,
{
    let tag = pick(cs.namespace(|| "tag"), condition, &a.tag, &b.tag)?;
    let hash = pick(cs.namespace(|| "hash"), condition, &a.hash, &b.hash)?;
    Ok(AllocatedPtr::from_allocated_parts(tag, hash))
}
