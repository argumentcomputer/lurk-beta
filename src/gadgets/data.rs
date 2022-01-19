use crate::data::{
    BaseContinuationTag, Continuation, Expression, Op1, Op2, Rel2, Store, Tag, TaggedHash, Thunk,
    POSEIDON_CONSTANTS_4, POSEIDON_CONSTANTS_6, POSEIDON_CONSTANTS_8,
};
use crate::eval::{Control, Frame, Witness, IO};
use crate::gadgets::constraints::{alloc_equal, enforce_implication, equal, pick};
use bellperson::{
    gadgets::{
        boolean::{AllocatedBit, Boolean},
        num::AllocatedNum,
    },
    groth16::{self, verify_proof},
    Circuit, ConstraintSystem, SynthesisError,
};
use blstrs::Scalar as Fr;
use ff::{Field, PrimeField};
use neptune::circuit::poseidon_hash;

#[derive(Clone)]
pub struct AllocatedTaggedHash {
    pub tag: AllocatedNum<Fr>,
    pub hash: AllocatedNum<Fr>,
}

impl AllocatedTaggedHash {
    pub fn from_tag_and_hash(tag: AllocatedNum<Fr>, hash: AllocatedNum<Fr>) -> Self {
        Self { tag, hash }
    }

    pub fn from_unallocated_tag_and_hash<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        unallocated_tag: Fr,
        unallocated_hash: Fr,
    ) -> Result<Self, SynthesisError> {
        let tag = AllocatedNum::alloc(&mut cs.namespace(|| "tag"), || Ok(unallocated_tag))?;
        let hash = AllocatedNum::alloc(&mut cs.namespace(|| "hash"), || Ok(unallocated_hash))?;
        Ok(Self { tag, hash })
    }

    pub fn from_tagged_hash<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        tagged_hash: Option<TaggedHash>,
    ) -> Result<Self, SynthesisError> {
        let tag = AllocatedNum::alloc(&mut cs.namespace(|| "allocate tag"), || {
            tagged_hash
                .map(|x| x.tag)
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        let hash = AllocatedNum::alloc(&mut cs.namespace(|| "allocate hash"), || {
            tagged_hash
                .map(|x| x.hash)
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        Ok(Self::from_tag_and_hash(tag, hash))
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

    pub fn tagged_hash(&self) -> Option<TaggedHash> {
        match (self.tag.get_value(), self.hash.get_value()) {
            (Some(tag), Some(hash)) => Some(TaggedHash { tag, hash }),
            _ => None,
        }
    }

    pub fn fetch_and_write_str(&self, store: &Store) -> String {
        if let Some(aaa) = &self.tagged_hash() {
            if let Some(bbb) = store.fetch(aaa) {
                store.write_expr_str(&bbb)
            } else {
                format!("expression not found in store: {:?}", aaa)
            }
        } else {
            "no TaggedHash".to_string()
        }
    }
    pub fn fetch_and_write_cont_str(&self, store: &Store) -> String {
        if let Some(aaa) = &self.tagged_hash() {
            if let Some(bbb) = store.fetch_continuation(aaa) {
                store.write_cont_str(&bbb)
            } else {
                format!("continuation not found in store: {:?}", aaa)
            }
        } else {
            "no TaggedHash".to_string()
        }
    }

    pub fn allocate_thunk_components<CS: ConstraintSystem<Fr>>(
        &self,
        mut cs: CS,
        store: &Store,
    ) -> Result<(AllocatedNum<Fr>, AllocatedTaggedHash, AllocatedTaggedHash), SynthesisError> {
        let maybe_thunk = if let Some(tagged_hash) = self.tagged_hash() {
            if let Some(Expression::Thunk(thunk)) = store.fetch(&tagged_hash) {
                Some(thunk)
            } else {
                None
            }
        } else {
            None
        };

        Thunk::allocate_maybe_dummy_components(cs, &maybe_thunk)
    }
}

pub struct GlobalAllocations {
    pub terminal_tagged_hash: AllocatedTaggedHash,
    pub outermost_tagged_hash: AllocatedTaggedHash,
    pub error_tagged_hash: AllocatedTaggedHash,
    pub dummy_tagged_hash: AllocatedTaggedHash,
    pub nil_tagged_hash: AllocatedTaggedHash,
    pub t_tagged_hash: AllocatedTaggedHash,
    pub lambda_tagged_hash: AllocatedTaggedHash,
    pub dummy_arg_tagged_hash: AllocatedTaggedHash,
    pub nil_tag: AllocatedNum<Fr>,
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

    pub default: AllocatedNum<Fr>,

    pub destructured_thunk_hash: AllocatedNum<Fr>,
    pub destructured_thunk_value: AllocatedTaggedHash,
    pub destructured_thunk_continuation: AllocatedTaggedHash,
}

impl GlobalAllocations {
    pub fn new<CS: ConstraintSystem<Fr>>(
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

        let dummy_arg_tagged_hash =
            Expression::read_sym("_").allocate_constant_tagged_hash(&mut cs.namespace(|| "_"))?;

        let nil_tag = nil_tagged_hash.tag.clone(); //Tag::Nil.allocate_constant(&mut cs.namespace(|| "nil_tag"))?;
        let sym_tag = Tag::Sym.allocate_constant(&mut cs.namespace(|| "sym_tag"))?;
        let thunk_tag = Tag::Thunk.allocate_constant(&mut cs.namespace(|| "thunk_tag"))?;
        let cons_tag = Tag::Cons.allocate_constant(&mut cs.namespace(|| "cons_tag"))?;
        let num_tag = Tag::Num.allocate_constant(&mut cs.namespace(|| "num_tag"))?;
        let fun_tag = Tag::Fun.allocate_constant(&mut cs.namespace(|| "fun_tag"))?;

        let outermost_cont_tag = BaseContinuationTag::Outermost
            .allocate_constant(&mut cs.namespace(|| "outermost_cont_tag"))?;
        let lookup_cont_tag = BaseContinuationTag::Lookup
            .allocate_constant(&mut cs.namespace(|| "lookup_cont_tag"))?;
        let letstar_cont_tag = BaseContinuationTag::LetStar
            .allocate_constant(&mut cs.namespace(|| "letstar_cont_tag"))?;
        let letrecstar_cont_tag = BaseContinuationTag::LetRecStar
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

        let maybe_thunk = if let Some(w) = witness {
            w.destructured_thunk.clone()
        } else {
            None
        };
        let (destructured_thunk_hash, destructured_thunk_value, destructured_thunk_continuation) =
            Thunk::allocate_maybe_dummy_components(
                &mut cs.namespace(|| "allocate thunk components"),
                &maybe_thunk,
            )?;

        Ok(Self {
            terminal_tagged_hash,
            outermost_tagged_hash,
            error_tagged_hash,
            dummy_tagged_hash,
            nil_tagged_hash,
            nil_tag,
            t_tagged_hash,
            lambda_tagged_hash,
            dummy_arg_tagged_hash,
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
            default,

            destructured_thunk_hash,
            destructured_thunk_value,
            destructured_thunk_continuation,
        })
    }
}

impl Expression {
    pub fn allocate_tagged_hash<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        expr: Option<Self>,
    ) -> Result<AllocatedTaggedHash, SynthesisError> {
        AllocatedTaggedHash::from_tagged_hash(cs, expr.map(|e| e.tagged_hash()))
    }

    pub fn allocated_tagged_hash<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedTaggedHash, SynthesisError> {
        AllocatedTaggedHash::from_tagged_hash(cs, Some(self.tagged_hash()))
    }

    pub fn allocate_constant_tagged_hash<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedTaggedHash, SynthesisError> {
        // TODO: This actually hashes, so when possible we should cache.
        // When this is constant, we should not hash on every circuit synthesis.
        let tagged_hash = self.tagged_hash();
        let allocated_tag = allocate_constant(&mut cs.namespace(|| "tag"), tagged_hash.tag)?;
        let allocated_hash = allocate_constant(&mut cs.namespace(|| "hash"), tagged_hash.hash)?;

        Ok(AllocatedTaggedHash::from_tag_and_hash(
            allocated_tag,
            allocated_hash,
        ))
    }
}

impl Continuation {
    pub fn allocate_maybe_dummy_components<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        cont: &Option<Continuation>,
    ) -> Result<(AllocatedNum<Fr>, Vec<AllocatedNum<Fr>>), SynthesisError> {
        if let Some(cont) = cont {
            cont.allocate_components(cs)
        } else {
            Continuation::allocate_dummy_components(cs)
        }
    }

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

    pub fn construct<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        cont_tag: &AllocatedNum<Fr>,
        components: &[AllocatedNum<Fr>; 8],
    ) -> Result<AllocatedTaggedHash, SynthesisError> {
        let hash = poseidon_hash(
            cs.namespace(|| "Continuation"),
            components.to_vec(), // FIXME: add slice based api to neptune
            &POSEIDON_CONSTANTS_8,
        )?;

        let cont = AllocatedTaggedHash::from_tag_and_hash(cont_tag.clone(), hash);
        Ok(cont)
    }
}

impl Expression {
    pub fn allocate_maybe_fun<CS: ConstraintSystem<Fr>>(
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
            Some(Expression::Fun(arg, body, closed_env)) => {
                Self::allocate_fun(cs, &arg, &body, &closed_env)
            }
            _ => Self::allocate_dummy_fun(cs),
        }
    }

    fn allocate_fun<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        arg: &TaggedHash,
        body: &TaggedHash,
        closed_env: &TaggedHash,
    ) -> Result<
        (
            AllocatedNum<Fr>,
            AllocatedTaggedHash,
            AllocatedTaggedHash,
            AllocatedTaggedHash,
        ),
        SynthesisError,
    > {
        let arg_t = AllocatedTaggedHash::from_tagged_hash(
            &mut cs.namespace(|| "allocate arg"),
            Some(*arg),
        )?;

        let body_t = AllocatedTaggedHash::from_tagged_hash(
            &mut cs.namespace(|| "allocate body"),
            Some(*body),
        )?;

        let closed_env_t = AllocatedTaggedHash::from_tagged_hash(
            &mut cs.namespace(|| "allocate closed_env"),
            Some(*closed_env),
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
        let default = TaggedHash {
            tag: Fr::zero(),
            hash: Fr::zero(),
        };

        Self::allocate_fun(cs, &default, &default, &default)
    }

    pub fn construct_cons<CS: ConstraintSystem<Fr>>(
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

    pub fn construct_list<CS: ConstraintSystem<Fr>>(
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

    pub fn construct_fun<CS: ConstraintSystem<Fr>>(
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
            g.fun_tag.clone(),
            hash,
        ))
    }
}

impl Continuation {
    pub fn allocate_tagged_hash<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        expr: Option<Self>,
    ) -> Result<AllocatedTaggedHash, SynthesisError> {
        AllocatedTaggedHash::from_tagged_hash(cs, expr.map(|c| c.continuation_tagged_hash()))
    }

    pub fn allocated_tagged_hash<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedTaggedHash, SynthesisError> {
        AllocatedTaggedHash::from_tagged_hash(cs, Some(self.continuation_tagged_hash()))
    }

    pub fn allocate_constant_tagged_hash<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedTaggedHash, SynthesisError> {
        // TODO: This actually hashes, so when possible we should cache.
        // When this is constant, we should not hash on every circuit synthesis.
        let tagged_hash = self.continuation_tagged_hash();
        let allocated_tag = allocate_constant(&mut cs.namespace(|| "tag"), tagged_hash.tag)?;
        let allocated_hash = allocate_constant(&mut cs.namespace(|| "hash"), tagged_hash.hash)?;

        Ok(AllocatedTaggedHash::from_tag_and_hash(
            allocated_tag,
            allocated_hash,
        ))
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
        allocate_constant(&mut cs.namespace(|| format!("{:?} tag", self)), self.fr())
    }
}

impl BaseContinuationTag {
    pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        allocate_constant(
            &mut cs.namespace(|| format!("{:?} base continuation tag", self)),
            self.cont_tag_fr(),
        )
    }
}

impl Op1 {
    pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        allocate_constant(&mut cs.namespace(|| format!("{:?} tag", self)), self.fr())
    }
}

impl Op2 {
    pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        allocate_constant(&mut cs.namespace(|| format!("{:?} tag", self)), self.fr())
    }
}

impl Rel2 {
    pub fn allocate_constant<CS: ConstraintSystem<Fr>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        allocate_constant(&mut cs.namespace(|| format!("{:?} tag", self)), self.fr())
    }
}

impl Thunk {
    pub fn allocate_maybe_dummy_components<CS: ConstraintSystem<Fr>>(
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

    // First component is the hash, which is wrong.
    pub fn allocate_components<CS: ConstraintSystem<Fr>>(
        &self,
        mut cs: CS,
    ) -> Result<(AllocatedNum<Fr>, Vec<AllocatedNum<Fr>>), SynthesisError> {
        let component_frs = self.get_hash_components();
        let mut components = Vec::with_capacity(4);

        for (i, fr) in component_frs.iter().enumerate() {
            components.push(AllocatedNum::alloc(
                cs.namespace(|| format!("Thunk component {}", i)),
                || Ok(*fr),
            )?);
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
pub fn pick_tagged_hash<CS>(
    mut cs: CS,
    condition: &Boolean,
    a: &AllocatedTaggedHash,
    b: &AllocatedTaggedHash,
) -> Result<AllocatedTaggedHash, SynthesisError>
where
    CS: ConstraintSystem<Fr>,
{
    let tag = pick(cs.namespace(|| "tag"), condition, &a.tag, &b.tag)?;
    let hash = pick(cs.namespace(|| "hash"), condition, &a.hash, &b.hash)?;
    Ok(AllocatedTaggedHash::from_tag_and_hash(tag, hash))
}
