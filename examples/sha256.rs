use std::env;
use std::marker::PhantomData;

use bellperson::{ConstraintSystem, SynthesisError};
use pasta_curves::pallas::Scalar as Fr;
use sha2::{Digest, Sha256};

use lurk::circuit::gadgets::pointer::{AllocatedContPtr, AllocatedPtr};
use lurk::coprocessor::{CoCircuit, Coprocessor};
use lurk::eval::{empty_sym_env, lang::Lang, Evaluator, IO};
use lurk::field::LurkField;
use lurk::num::Num;
use lurk::store::{Ptr, Store};
use lurk::sym::Sym;
use lurk::writer::Write;

#[derive(Clone, Debug)]
pub(crate) struct Sha256Coprocessor<F: LurkField> {
    n: usize,
    pub(crate) _p: PhantomData<F>,
}

impl<F: LurkField> CoCircuit<F> for Sha256Coprocessor<F> {}

impl<F: LurkField> Coprocessor<F> for Sha256Coprocessor<F> {
    fn eval_arity(&self) -> usize {
        0
    }

    fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
        let mut hasher = Sha256::new();

        let input = vec![0u8; self.n];

        hasher.update(input);
        let mut result = hasher.finalize();

        result.reverse();
        dbg!(&result);
        // This could actually overflow. To be completely correct, we need to
        // return more than one field element, or a Lurk commitment to the value.
        let f = LurkField::from_bytes(result.as_slice()).unwrap();
        let x = s.intern_num(Num::Scalar(f));
        println!("{}", x.fmt_to_string(s));

        return x;
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
        0
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _store: &Store<F>,
        input_exprs: &[AllocatedPtr<F>],
        input_env: &AllocatedPtr<F>,
        input_cont: &AllocatedContPtr<F>,
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        todo!()
    }
}

// cargo run --example sha256 1 f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b false
fn main() {
    let args: Vec<String> = env::args().collect();
    println!("{}", args[1]);
    let num_of_64_bytes = args[1].parse::<usize>().unwrap();
    let expect = hex::decode(args[2].parse::<String>().unwrap()).unwrap();
    let setup_only = args[3].parse::<bool>().unwrap();

    let input_size = 64 * num_of_64_bytes;
    let input_str = vec![0u8; input_size];

    let s = &mut Store::<Fr>::new();
    let mut lang = Lang::<Fr, Sha256Coproc<Fr>>::new();
    let sym_str = format!(".sha256.hash-{}-zero-bytes", input_size).to_string();
    let name = Sym::new(sym_str.clone());
    let coprocessor: Sha256Coprocessor<Fr> = Sha256Coprocessor::<Fr>::new(input_size);
    let coproc = Sha256Coproc::SC(coprocessor);

    lang.add_coprocessor(name, coproc, s);

    let expr = format!("({})", sym_str);
    let ptr = s.read(&expr).unwrap();

    let limit = 100000;
    let env = empty_sym_env(s);
    let (
        IO {
            expr: new_expr,
            env: new_env,
            cont: new_cont,
        },
        iterations,
        emitted,
    ) = Evaluator::new(ptr, env, s, limit, &lang).eval().unwrap();

    // let circuit = Sha256Circuit {
    //     data: input_str,
    //     expect: expect.clone(),
    // };

    println!("Yo");
}
