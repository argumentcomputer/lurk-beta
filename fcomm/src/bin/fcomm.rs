use std::env;
use std::fs::read_to_string;
use std::io::{self};
use std::path::{Path, PathBuf};

use blstrs::Scalar;
use ff::PrimeField;
use pairing_lib::{Engine, MultiMillerLoop};
use serde::{Deserialize, Serialize};
use structopt::StructOpt;

use lurk::eval::IO;
use lurk::store::{Ptr, Store};

use fcomm::{
    self, evaluate, Claim, Commitment, Error, Evaluation, FileStore, Function, Opening, Proof,
};

macro_rules! prl {
    ($($arg:expr),*) => { if *fcomm::VERBOSE.get().expect("verbose flag uninitialized") {
        println!($($arg),*) } };
}

#[derive(StructOpt)]
#[structopt(about = "Functional commitments")]
struct Opt {
    command: String,

    #[structopt(short("f"), long("function"), help("Path to function source"))]
    function: Option<Option<String>>,

    #[structopt(short("x"), long("expression"), help("Path to expression source"))]
    expression: Option<Option<String>>,

    #[structopt(
        long("claim"),
        help("Wrap evaluation result in a claim and write to path")
    )]
    claim: Option<Option<String>>,

    #[structopt(short("c"), long("commitment"), help("Path to functional commitment"))]
    commitment: Option<Option<String>>,

    #[structopt(short("i"), long("input"), help("Path to function input"))]
    input: Option<Option<String>>,

    #[structopt(short("p"), long("proof"), help("Path to proof input"))]
    proof: Option<Option<String>>,

    #[structopt(
        long("eval-input"),
        help("Evaluate inputs before passing to function (outside the proof) when opening. Otherwise inputs are unevaluated.")
    )]
    eval_input: bool,
    #[structopt(
        long("quote-input"),
        help("Quote input before passing to function when opening. Otherwise input will be passed unevaluated and unquoted. --quote-input and --eval-input would cancel each other out if used in conjunction, so is probably not what is desired.")
    )]
    quote_input: bool,

    #[structopt(
        short("l"),
        long("limit"),
        default_value("1000"),
        help("Iteration limit")
    )]
    limit: usize,

    #[structopt(
        short("e"),
        long("error"),
        help("Exit with error on failed verification")
    )]
    error: bool,

    #[structopt(long("chain"), help("Chain commitment openings. Opening includes commitment to new function along with output."))]
    chain: bool,

    #[structopt(short("v"), long("verbose"), help("Be verbose"))]
    verbose: bool,
}

struct FComm {
    opt: Opt,
}

impl FComm {
    fn read_from_path<P: AsRef<Path>, F: PrimeField + Serialize>(
        &self,
        store: &mut Store<F>,
        path: P,
    ) -> Result<Ptr<F>, Error> {
        let path = env::current_dir()?.join(path);

        let input = read_to_string(path)?;

        let src = store.read(&input).unwrap();
        Ok(src)
    }

    fn read_eval_from_path<P: AsRef<Path>, F: PrimeField + Serialize>(
        &self,
        store: &mut Store<F>,
        path: P,
    ) -> Result<(Ptr<F>, Ptr<F>), Error> {
        let src = self.read_from_path(store, path)?;
        let (
            IO {
                expr,
                env: _,
                cont: _,
            },
            _iterations,
        ) = evaluate(store, src, self.opt.limit);

        Ok((expr, src))
    }

    fn read_no_eval_from_path<P: AsRef<Path>, F: PrimeField + Serialize>(
        &self,
        store: &mut Store<F>,
        path: P,
    ) -> Result<(Ptr<F>, Ptr<F>), Error> {
        let src = self.read_from_path(store, path)?;

        let quote = store.sym("quote");
        let quoted = store.list(&[quote, src]);
        Ok((quoted, src))
    }

    fn maybe_extract_path(path: &Option<Option<String>>) -> Option<PathBuf> {
        if let Some(Some(p)) = &path {
            Some(PathBuf::from(p.to_string()))
        } else {
            None
        }
    }
    fn extract_path(path: &Option<Option<String>>, name: &str) -> PathBuf {
        if let Some(p) = Self::maybe_extract_path(path) {
            p
        } else {
            panic!("path missing for {}", name);
        }
    }

    fn function_path(&self) -> PathBuf {
        Self::extract_path(&self.opt.function, "function")
    }
    fn commitment_path(&self) -> PathBuf {
        Self::extract_path(&self.opt.commitment, "commitment")
    }
    fn input_path(&self) -> PathBuf {
        Self::extract_path(&self.opt.input, "input")
    }
    fn expression_path(&self) -> PathBuf {
        Self::extract_path(&self.opt.expression, "expression")
    }
    fn proof_path(&self) -> PathBuf {
        Self::extract_path(&self.opt.proof, "proof")
    }
    fn claim_path(&self) -> PathBuf {
        Self::extract_path(&self.opt.claim, "claim")
    }
    fn path_successor(p: PathBuf) -> PathBuf {
        let new_index = if let Some(extension) = p.extension() {
            let index = if let Some(e) = extension.to_str() {
                e.to_string().parse::<usize>().unwrap_or(0) + 1
            } else {
                1
            };

            index
        } else {
            1
        };
        let mut new_path = p;
        new_path.set_extension(new_index.to_string());

        new_path
    }

    fn _lurk_function<F: PrimeField + Serialize>(
        &self,
        store: &mut Store<F>,
    ) -> Result<(Ptr<F>, Ptr<F>), Error> {
        let path = self.function_path();

        let (function, src) = self
            .read_eval_from_path(store, path)
            .expect("failed to read function");
        assert!(function.is_fun(), "FComm can only commit to functions.");

        Ok((function, src))
    }

    fn function<F: PrimeField + Serialize>(&self) -> Result<Function<F>, Error>
    where
        for<'de> F: Deserialize<'de>,
    {
        Function::read_from_path(self.function_path())
    }

    fn input<F: PrimeField + Serialize>(&self, store: &mut Store<F>) -> Result<Ptr<F>, Error> {
        let path = self.input_path();

        let input = if self.opt.eval_input {
            let (evaled_input, _src) = self.read_eval_from_path(store, path)?;
            evaled_input
        } else {
            let (quoted, src) = self.read_no_eval_from_path(store, path)?;
            if self.opt.quote_input {
                quoted
            } else {
                src
            }
        };

        Ok(input)
    }

    fn expression<F: PrimeField + Serialize>(&self, store: &mut Store<F>) -> Result<Ptr<F>, Error> {
        let path = self.expression_path();

        let input = self.read_from_path(store, path)?;

        Ok(input)
    }

    // Get proof from supplied path or else from stdin.
    fn proof<E: Engine + MultiMillerLoop>(&self) -> Result<Proof<E>, Error>
    where
        for<'de> <E as Engine>::Gt: blstrs::Compress + Serialize + Deserialize<'de>,
        for<'de> <E as Engine>::G1: Serialize + Deserialize<'de>,
        for<'de> <E as Engine>::G1Affine: Serialize + Deserialize<'de>,
        for<'de> <E as Engine>::G2Affine: Serialize + Deserialize<'de>,
        for<'de> <E as Engine>::Fr: Serialize + Deserialize<'de>,
        for<'de> <E as Engine>::Gt: blstrs::Compress + Serialize + Deserialize<'de>,
    {
        if self.opt.proof.is_some() {
            Proof::read_from_path(self.proof_path())
        } else {
            Proof::read_from_stdin()
        }
    }

    // Get claim from supplied path.
    fn claim<F: PrimeField + Serialize>(&self) -> Result<Claim<F>, Error>
    where
        for<'de> F: Deserialize<'de>,
    {
        if self.opt.claim.is_some() {
            Claim::read_from_path(self.claim_path())
        } else {
            panic!("whoops!");
        }
    }

    fn commit(&self) -> Result<(), Error> {
        let s = &mut Store::<Scalar>::default();

        let mut function = self.function()?;
        let fun_ptr = function.fun_ptr(s, self.opt.limit);
        let commitment = if let Some(secret) = function.secret {
            Commitment::from_ptr_and_secret(s, &fun_ptr, secret)
        } else {
            let (commitment, secret) = Commitment::from_ptr_with_hiding(s, &fun_ptr);
            function.secret = Some(secret);
            function.commitment = Some(commitment);

            function.write_to_path(self.function_path());

            commitment
        };
        let path = self.commitment_path();
        commitment.write_to_path(path);

        Ok(())
    }

    fn open(&self) -> Result<(), Error> {
        let mut s = Store::<Scalar>::default();

        let function = self.function()?;
        let input = self.input(&mut s)?;
        let out_path = self.proof_path();

        let chain = self.opt.chain;
        let chained_function_path = chain.then(|| Self::path_successor(self.function_path()));

        // Needed if we are creating a chained commitment.
        let commitment_path = Self::maybe_extract_path(&self.opt.commitment);

        let proof = Opening::open_and_prove(
            &mut s,
            input,
            function,
            self.opt.limit,
            chain,
            commitment_path,
            chained_function_path,
        )?;

        // Write first, so prover can debug if proof doesn't verify (it should).
        proof.write_to_path(out_path);
        proof.verify().expect("created opening doesn't verify");

        Ok(())
    }

    fn eval(&self) -> Result<(), Error> {
        let mut s = Store::<Scalar>::default();

        let expr = self.expression(&mut s)?;

        let evaluation = Evaluation::eval(&mut s, expr, self.opt.limit);

        if self.opt.claim.is_some() {
            let out_path = self.claim_path();

            let claim = Claim::<Scalar>::Evaluation(evaluation);
            claim.write_to_path(out_path);
        } else {
            serde_json::to_writer(io::stdout(), &evaluation)?;
        }
        Ok(())
    }

    fn prove(&self) -> Result<(), Error> {
        let mut s = Store::<Scalar>::default();
        let out_path = self.proof_path();

        let proof = if self.opt.claim.is_some() {
            let claim = self.claim()?;
            Proof::prove_claim(&mut s, claim, self.opt.limit, false)?
        } else {
            let expr = self.expression(&mut s)?;
            Proof::eval_and_prove(&mut s, expr, self.opt.limit, false)?
        };

        // Write first, so prover can debug if proof doesn't verify (it should).
        proof.write_to_path(out_path);
        proof.verify().expect("created proof doesn't verify");

        Ok(())
    }

    fn verify(&self) -> Result<(), Error> {
        let result = self.proof()?.verify()?;

        serde_json::to_writer(io::stdout(), &result)?;

        if result.verified {
            prl!("Verification succeeded.");
        } else if self.opt.error {
            serde_json::to_writer(io::stderr(), &result)?;
            std::process::exit(1);
        };

        Ok(())
    }
}

fn main() -> Result<(), Error> {
    pretty_env_logger::init();

    let opt = Opt::from_args();
    let command = opt.command.clone();

    fcomm::VERBOSE
        .set(opt.verbose)
        .expect("could not set verbose flag");

    let fcomm = FComm { opt };

    match command.to_uppercase().as_str() {
        "COMMIT" => fcomm.commit(),
        "OPEN" => fcomm.open(),
        "EVAL" => fcomm.eval(),
        "PROVE" => fcomm.prove(),
        "VERIFY" => fcomm.verify(),
        command => {
            eprintln!("Unsupported command: {}", command);
            std::process::exit(1);
        }
    }?;

    Ok(())
}
