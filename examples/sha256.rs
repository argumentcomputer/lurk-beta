use std::env;
use std::marker::PhantomData;
use std::time::{Duration, Instant};

// use bellperson::gadgets::multipack;
use bellperson::gadgets::sha256::sha256;
use bellperson::{ConstraintSystem, SynthesisError};
use bellperson::gadgets::num::AllocatedNum;
use bellperson::gadgets::boolean::{Boolean, AllocatedBit};
use bellperson::gadgets::num::Num as BNum;
use lurk::circuit::gadgets::data::GlobalAllocations;
use lurk::proof::nova::{NovaProver, public_params};
// use bellperson::gadgets::Assignment;
use lurk::tag::{ExprTag, Tag};
use pasta_curves::pallas::Scalar as Fr;
use sha2::{Digest, Sha256};

use lurk::proof::Prover;
use lurk::circuit::gadgets::pointer::{AllocatedContPtr, AllocatedPtr};
use lurk::coprocessor::{CoCircuit, Coprocessor};
use lurk::eval::{empty_sym_env, lang::Lang, Evaluator, IO};
use lurk::field::LurkField;
// use lurk::num::Num;
use lurk::store::{Ptr, Store};
use lurk::sym::Sym;
// use lurk::uint::UInt;
// use lurk::writer::Write;

#[derive(Clone, Debug)]
pub(crate) struct Sha256Coprocessor<F: LurkField> {
    n: usize,
    pub(crate) _p: PhantomData<F>,
}

impl<F: LurkField> CoCircuit<F> for Sha256Coprocessor<F> {
    fn arity(&self) -> usize {
        0
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        g: &GlobalAllocations<F>,
        store: &Store<F>,
        _input_exprs: &[AllocatedPtr<F>],
        input_env: &AllocatedPtr<F>,
        input_cont: &AllocatedContPtr<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        
        // TODO: Maybe fix this
        let false_bool = Boolean::from(AllocatedBit::alloc(cs.namespace(|| "false"), Some(false))?);
        
        let preimage = vec![false_bool; self.n * 8];

        let mut bits = sha256(cs.namespace(|| "SHAhash"), &preimage)?;

        bits.reverse();

        let num1 = make_u64_from_bits(&mut cs.namespace(|| "num1"), &bits[0..64])?;
        let num2 = make_u64_from_bits(&mut cs.namespace(|| "num2"), &bits[64..128])?;
        let num3 = make_u64_from_bits(&mut cs.namespace(|| "num3"), &bits[128..192])?;
        let num4 = make_u64_from_bits(&mut cs.namespace(|| "num4"), &bits[192..256])?;

        // dbg!(num1.fetch_and_write_str(store), num2.fetch_and_write_str(store), num3.fetch_and_write_str(store), num4.fetch_and_write_str(store));

        let result_ptr: &AllocatedPtr<F> = &g.nil_ptr;

        let result_ptr1 = AllocatedPtr::construct_cons(cs.namespace(|| "limb_1"), g, store, &num1, &result_ptr)?;
        let result_ptr2 = AllocatedPtr::construct_cons(cs.namespace(|| "limb_2"), g, store, &num2, &result_ptr1)?;
        let result_ptr3 = AllocatedPtr::construct_cons(cs.namespace(|| "limb_3"), g, store, &num3, &result_ptr2)?;
        let result_ptr4 = AllocatedPtr::construct_cons(cs.namespace(|| "limb_4"), g, store, &num4, &result_ptr3)?;

        Ok((result_ptr4, input_env.clone(), input_cont.clone()))
    }
}

impl<F: LurkField> Coprocessor<F> for Sha256Coprocessor<F> {
    fn eval_arity(&self) -> usize {
        0
    }

    fn simple_evaluate(&self, s: &mut Store<F>, _args: &[Ptr<F>]) -> Ptr<F> {
        let mut hasher = Sha256::new();

        let input = vec![0u8; self.n];

        hasher.update(input);
        let result = hasher.finalize();

        let mut array = [0u8; 8];
        array.copy_from_slice(&result[0..8]);
        let a = u64::from_be_bytes(array);

        array.copy_from_slice(&result[8..16]);
        let b = u64::from_be_bytes(array);

        array.copy_from_slice(&result[16..24]);
        let c = u64::from_be_bytes(array);

        array.copy_from_slice(&result[24..]);
        let d = u64::from_be_bytes(array);

        // println!("{} {} {} {}", a, b, c, d);
        return s.list(&[a, b, c, d].map(|x| s.get_u64(x)));
    }
}

impl<F: LurkField> Sha256Coprocessor<F> {
    pub(crate) fn new(n: usize) -> Self {
        Self {
            n,
            _p: Default::default(),
        }
    }
}

#[derive(Clone, Debug)]
enum Sha256Coproc<F: LurkField> {
    SC(Sha256Coprocessor<F>),
}

impl<F: LurkField> Coprocessor<F> for Sha256Coproc<F> {
    fn eval_arity(&self) -> usize {
        match self {
            Self::SC(c) => c.eval_arity(),
        }
    }

    fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
        match self {
            Self::SC(c) => c.simple_evaluate(s, args),
        }
    }
}

impl<F: LurkField> CoCircuit<F> for Sha256Coproc<F> {
    fn arity(&self) -> usize {
        match self {
            Self::SC(c) => c.arity(),
        }
    }
    fn synthesize<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            g: &GlobalAllocations<F>,
            store: &Store<F>,
            input_exprs: &[AllocatedPtr<F>],
            input_env: &AllocatedPtr<F>,
            input_cont: &AllocatedContPtr<F>,
        ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        match self {
            Self::SC(c) => c.synthesize(cs, g, store, input_exprs, input_env, input_cont)
        }
    }
}

// cargo run --example sha256 1 f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b false
fn main() {
    let args: Vec<String> = env::args().collect();

    let num_of_64_bytes = args[1].parse::<usize>().unwrap();
    let expect = hex::decode(args[2].parse::<String>().unwrap()).unwrap();
    let _setup_only = args[3].parse::<bool>().unwrap();

    let input_size = 64 * num_of_64_bytes;
    let _input_str = vec![0u8; input_size];

    let store = &mut Store::<Fr>::new();
    let mut lang = Lang::<Fr, Sha256Coproc<Fr>>::new();
    let sym_str = format!(".sha256.hash-{}-zero-bytes", input_size).to_string();
    let name = Sym::new(sym_str.clone());
    let coprocessor: Sha256Coprocessor<Fr> = Sha256Coprocessor::<Fr>::new(input_size);
    let coproc = Sha256Coproc::SC(coprocessor);

    lang.add_coprocessor(name, coproc, store);

    let coproc_expr = format!("({})", sym_str);

    let u1: u64 = u64::from_be_bytes(expect[0..8].try_into().unwrap());
    let u2: u64 = u64::from_be_bytes(expect[8..16].try_into().unwrap());
    let u3: u64 = u64::from_be_bytes(expect[16..24].try_into().unwrap());
    let u4: u64 = u64::from_be_bytes(expect[24..32].try_into().unwrap());
    let result_expr = format!("({}u64 {}u64 {}u64 {}u64)", u1, u2, u3, u4);

    let expr = format!("(emit (eq {coproc_expr} (quote {result_expr})))");
    let ptr = store.read(&expr).unwrap();
    
    let reduction_count = 10;
    
    let nova_prover = NovaProver::<Fr, Sha256Coproc<Fr>>::new(reduction_count, lang.clone());

    println!("Setting up public parameters...");

    let pp_start = Instant::now();
    let pp = public_params(reduction_count, &lang);
    let pp_end = pp_start.elapsed();

    println!("Public parameters took {:?}", pp_end);

    println!("Beginning proof step...");

    let proof_start = Instant::now();
    let (proof, z0, zi, num_steps) = nova_prover.evaluate_and_prove(&pp, ptr, empty_sym_env(store), store, 10000, &lang).unwrap();
    let proof_end = proof_start.elapsed();

    println!("Proofs took {:?}", proof_end);
    
    println!("Verifying proof...");

    let verify_start = Instant::now();
    let res = proof.verify(&pp, num_steps, z0.clone(), &zi).unwrap();
    let verify_end = verify_start.elapsed();

    println!("Verify took {:?}", verify_end);
    
    if res {
        println!("Congratulations! You proved and verified a SHA256 hash calculation in {:?} time!", pp_end + proof_end + verify_end);
    }
}

fn make_u64_from_bits<F, CS>(mut cs: CS, bits: &[Boolean]) -> Result<AllocatedPtr<F>, SynthesisError>
where
    F: LurkField,
    CS: ConstraintSystem<F>
{
    let mut num = BNum::<F>::zero();
    let mut coeff = F::one();

    for bit in bits {
        num = num.add_bool_with_coeff(CS::one(), bit, coeff);

        coeff = coeff.double();
    }

    let allocated_num = AllocatedNum::alloc(&mut cs.namespace(|| "chunk"), || num.get_value().ok_or(SynthesisError::AssignmentMissing))?;
    // num * 1 = input
    cs.enforce(
        || "packing constraint",
        |_| num.lc(F::one()),
        |lc| lc + CS::one(),
        |lc| lc + allocated_num.get_variable(),
    );

    AllocatedPtr::alloc_tag(&mut cs, ExprTag::U64.to_field(), allocated_num)
}
