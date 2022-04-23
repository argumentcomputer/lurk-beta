use log::info;
use std::env;
use std::fs::read_to_string;
use std::io;
use std::path::{Path, PathBuf};

use blstrs::Scalar;
use hex::FromHex;
use pairing_lib::{Engine, MultiMillerLoop};
use serde::{Deserialize, Serialize};

use lurk::eval::IO;
use lurk::field::LurkField;
use lurk::store::{Ptr, Store};

use clap::{AppSettings, Args, Parser, Subcommand};
use clap_verbosity_flag::{Verbosity, WarnLevel};

use fcomm::{
    self, committed_function_store, evaluate, Claim, Commitment, Error, Evaluation, FileStore,
    Function, Opening, Proof,
};

/// Functional commitments
#[derive(Parser, Debug)]
#[clap(version, about, long_about = None)]
#[clap(global_setting(AppSettings::DeriveDisplayOrder))]
struct Cli {
    /// Evaluate inputs before passing to function (outside the proof) when opening. Otherwise inputs are unevaluated.
    #[clap(long)]
    eval_input: bool,

    /// Quote input before passing to function when opening. Otherwise input will be passed unevaluated and unquoted. --quote-input and --eval-input would cancel each other out if used in conjunction, so is probably not what is desired.
    #[clap(long)]
    quote_input: bool,

    /// Iteration limit
    #[clap(short, long, default_value = "1000")]
    limit: usize,

    /// Exit with error on failed verification
    #[clap(short, long)]
    error: bool,

    /// Be verbose
    #[clap(flatten)]
    verbose: Verbosity<WarnLevel>,

    #[clap(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Creates a hiding commitment to a function
    Commit(Commit),

    /// Creates an opening
    Open(Open),

    /// Evaluates an expression
    Eval(Eval),

    /// Generates a proof for the given expression
    Prove(Prove),

    /// Verifies a proof
    Verify(Verify),
}

#[derive(Args, Debug)]
struct Commit {
    /// Path to function source
    #[clap(short, long, parse(from_os_str))]
    function: PathBuf,

    /// Path to functional commitment
    #[clap(short, long, parse(from_os_str))]
    commitment: Option<PathBuf>,
}

#[derive(Args, Debug)]
struct Open {
    // /// Path to function source
    // #[clap(short, long, parse(from_os_str))]
    // function: PathBuf,
    /// Path to function input
    #[clap(short, long, parse(from_os_str))]
    input: PathBuf,

    /// Path to proof input
    #[clap(short, long, parse(from_os_str))]
    proof: PathBuf,

    /// Commitment value (hex string)
    #[clap(short, long)]
    commitment: String,

    /// Chain commitment openings. Opening includes commitment to new function along with output.
    #[clap(long)]
    chain: bool,
}

#[derive(Args, Debug)]
struct Eval {
    /// Path to expression source
    #[clap(short = 'x', long, parse(from_os_str))]
    expression: PathBuf,

    /// Wrap evaluation result in a claim
    #[clap(long)]
    claim: Option<PathBuf>,
}

#[derive(Args, Debug)]
struct Prove {
    /// Path to expression source
    #[clap(short = 'x', long, parse(from_os_str))]
    expression: PathBuf,

    /// Path to proof input
    #[clap(short, long, parse(from_os_str))]
    proof: PathBuf,

    /// Wrap evaluation result in a claim
    #[clap(long)]
    claim: Option<PathBuf>,
}

#[derive(Args, Debug)]
struct Verify {
    /// Path to proof input
    #[clap(short, long, parse(from_os_str))]
    proof: PathBuf,
}

impl Commit {
    fn commit(&self, limit: usize) -> Result<(), Error> {
        let s = &mut Store::<Scalar>::default();

        let mut function = Function::read_from_path(&self.function)?;
        let fun_ptr = function.fun_ptr(s, limit);
        let function_map = committed_function_store();

        let commitment = if let Some(secret) = function.secret {
            let commitment = Commitment::from_ptr_and_secret(s, &fun_ptr, secret);

            function.commitment = Some(commitment);

            function_map.set(commitment, &function)?;
            function.write_to_path(&self.function);

            commitment
        } else {
            let (commitment, secret) = Commitment::from_ptr_with_hiding(s, &fun_ptr);
            function.secret = Some(secret);
            function.commitment = Some(commitment);

            function_map.set(commitment, &function)?;

            function.write_to_path(&self.function);

            commitment
        };
        if let Some(commitment_path) = &self.commitment {
            commitment.write_to_path(commitment_path);
        } else {
            serde_json::to_writer(io::stdout(), &commitment)?;
        }

        Ok(())
    }
}

impl Open {
    fn open(
        &self,
        chain: bool,
        limit: usize,
        eval_input: bool,
        quote_input: bool,
    ) -> Result<(), Error> {
        let mut s = Store::<Scalar>::default();
        let function_map = committed_function_store();
        let commitment =
            Commitment::from_hex(&self.commitment).map_err(|e| Error::CommitmentParseError(e))?;

        let function = function_map
            .get(commitment)
            .expect("committed function not found");
        let input = input(&mut s, &self.input, eval_input, limit, quote_input)?;
        let out_path = &self.proof;

        // // Needed if we are creating a chained commitment.
        // let chained_function_path = chain.then(|| path_successor(&self.function));

        let proof = Opening::open_and_prove(&mut s, input, function, limit, chain)?;

        // // Write first, so prover can debug if proof doesn't verify (it should).
        proof.write_to_path(out_path);
        proof.verify().expect("created opening doesn't verify");

        Ok(())
    }
}

impl Eval {
    fn eval(&self, limit: usize) -> Result<(), Error> {
        let mut s = Store::<Scalar>::default();

        let expr = expression(&mut s, &self.expression)?;

        let evaluation = Evaluation::eval(&mut s, expr, limit);

        match &self.claim {
            Some(out_path) => {
                let claim = Claim::<Scalar>::Evaluation(evaluation);
                claim.write_to_path(out_path);
            }
            None => {
                serde_json::to_writer(io::stdout(), &evaluation)?;
            }
        }

        Ok(())
    }
}

impl Prove {
    fn prove(&self, limit: usize) -> Result<(), Error> {
        let mut s = Store::<Scalar>::default();

        let expr = expression(&mut s, &self.expression)?;

        let proof = match &self.claim {
            Some(claim) => Proof::prove_claim(&mut s, Claim::read_from_path(claim)?, limit, false)?,
            None => Proof::eval_and_prove(&mut s, expr, limit, false)?,
        };

        // Write first, so prover can debug if proof doesn't verify (it should).
        proof.write_to_path(&self.proof);
        proof.verify().expect("created proof doesn't verify");

        Ok(())
    }
}

impl Verify {
    fn verify(&self, cli_error: bool) -> Result<(), Error> {
        let result = proof(Some(&self.proof))?.verify()?;

        serde_json::to_writer(io::stdout(), &result)?;

        if result.verified {
            info!("Verification succeeded.");
        } else if cli_error {
            serde_json::to_writer(io::stderr(), &result)?;
            std::process::exit(1);
        };

        Ok(())
    }
}

fn read_from_path<P: AsRef<Path>, F: LurkField + Serialize>(
    store: &mut Store<F>,
    path: P,
) -> Result<Ptr<F>, Error> {
    let path = env::current_dir()?.join(path);
    let input = read_to_string(path)?;
    let src = store.read(&input).unwrap();

    Ok(src)
}

fn read_eval_from_path<P: AsRef<Path>, F: LurkField + Serialize>(
    store: &mut Store<F>,
    path: P,
    limit: usize,
) -> Result<(Ptr<F>, Ptr<F>), Error> {
    let src = read_from_path(store, path)?;
    let (
        IO {
            expr,
            env: _,
            cont: _,
        },
        _iterations,
    ) = evaluate(store, src, limit);

    Ok((expr, src))
}

fn read_no_eval_from_path<P: AsRef<Path>, F: LurkField + Serialize>(
    store: &mut Store<F>,
    path: P,
) -> Result<(Ptr<F>, Ptr<F>), Error> {
    let src = read_from_path(store, path)?;

    let quote = store.sym("quote");
    let quoted = store.list(&[quote, src]);
    Ok((quoted, src))
}

fn _lurk_function<P: AsRef<Path>, F: LurkField + Serialize>(
    store: &mut Store<F>,
    function_path: P,
    limit: usize,
) -> Result<(Ptr<F>, Ptr<F>), Error> {
    let (function, src) =
        read_eval_from_path(store, function_path, limit).expect("failed to read function");
    assert!(function.is_fun(), "FComm can only commit to functions.");

    Ok((function, src))
}

fn input<P: AsRef<Path>, F: LurkField + Serialize>(
    store: &mut Store<F>,
    input_path: P,
    eval_input: bool,
    limit: usize,
    quote_input: bool,
) -> Result<Ptr<F>, Error> {
    let input = if eval_input {
        let (evaled_input, _src) = read_eval_from_path(store, input_path, limit)?;
        evaled_input
    } else {
        let (quoted, src) = read_no_eval_from_path(store, input_path)?;
        if quote_input {
            quoted
        } else {
            src
        }
    };

    Ok(input)
}

fn expression<P: AsRef<Path>, F: LurkField + Serialize>(
    store: &mut Store<F>,
    expression_path: P,
) -> Result<Ptr<F>, Error> {
    let input = read_from_path(store, expression_path)?;

    Ok(input)
}

// Get proof from supplied path or else from stdin.
fn proof<P: AsRef<Path>, E: Engine + MultiMillerLoop>(
    proof_path: Option<P>,
) -> Result<Proof<E>, Error>
where
    <E as Engine>::Fr: LurkField,
    for<'de> <E as Engine>::Gt: blstrs::Compress + Serialize + Deserialize<'de>,
    for<'de> <E as Engine>::G1: Serialize + Deserialize<'de>,
    for<'de> <E as Engine>::G1Affine: Serialize + Deserialize<'de>,
    for<'de> <E as Engine>::G2Affine: Serialize + Deserialize<'de>,
    for<'de> <E as Engine>::Fr: Serialize + Deserialize<'de>,
    for<'de> <E as Engine>::Gt: blstrs::Compress + Serialize + Deserialize<'de>,
{
    match proof_path {
        Some(path) => Proof::read_from_path(path),
        None => Proof::read_from_stdin(),
    }
}

fn main() -> Result<(), Error> {
    let cli = Cli::parse();

    pretty_env_logger::formatted_builder()
        .filter_level(cli.verbose.log_level_filter())
        .init();

    match &cli.command {
        Command::Commit(c) => c.commit(cli.limit),
        Command::Open(o) => o.open(o.chain, cli.limit, cli.eval_input, cli.quote_input),
        Command::Eval(e) => e.eval(cli.limit),
        Command::Prove(p) => p.prove(cli.limit),
        Command::Verify(v) => v.verify(cli.error),
    }
}
