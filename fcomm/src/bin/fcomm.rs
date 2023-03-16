use log::info;
use std::convert::TryFrom;
use std::env;
use std::fs::read_to_string;
use std::io;
use std::path::{Path, PathBuf};

use hex::FromHex;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use lurk::eval::IO;
use lurk::field::LurkField;
use lurk::proof::{nova::NovaProver, Prover};
use lurk::store::{Ptr, Store, TypePredicates};

use clap::{AppSettings, Args, Parser, Subcommand};
use clap_verbosity_flag::{Verbosity, WarnLevel};

use fcomm::{
    self, committed_expression_store, error::Error, evaluate, public_params, Claim, Commitment,
    CommittedExpression, Evaluation, Expression, FileStore, LurkPtr, Opening, OpeningRequest,
    Proof, ReductionCount, S1,
};

/// Functional commitments
#[derive(Parser, Debug)]
#[clap(version, about, long_about = None)]
#[clap(global_setting(AppSettings::DeriveDisplayOrder))]
struct Cli {
    /// Evaluate inputs before passing to function (outside the proof) when opening. Otherwise inputs are unevaluated.
    #[clap(long, value_parser)]
    eval_input: bool,

    /// Iteration limit
    #[allow(deprecated)]
    #[clap(short, long, default_value = "1000", value_parser)]
    limit: usize,

    /// Exit with error on failed verification
    #[clap(short, long, value_parser)]
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
    /// Path to function
    #[clap(short, long, value_parser)]
    function: PathBuf,

    /// Path to functional commitment
    #[clap(short, long, value_parser)]
    commitment: Option<PathBuf>,

    // Function is lurk source.
    #[clap(long, value_parser)]
    lurk: bool,
}

#[derive(Args, Debug)]
struct Open {
    /// Path to function input
    #[clap(short, long, value_parser)]
    input: Option<PathBuf>,

    /// Path to proof output if prove requested
    #[clap(short, long, value_parser)]
    proof: Option<PathBuf>,

    /// Number of circuit reductions per step
    #[clap(short = 'r', long, default_value = "1", value_parser)]
    reduction_count: usize,

    /// Optional commitment value (hex string). Function will be looked-up by commitment if supplied.
    #[clap(short, long, value_parser)]
    commitment: Option<String>,

    /// Optional path to function used if commitment is not supplied.
    #[clap(short, long, value_parser)]
    function: Option<PathBuf>,

    /// Optional path to OpeningRequest -- which subsumes commitment, function, and input if supplied.
    #[clap(long, value_parser)]
    request: Option<PathBuf>,

    /// Function is lurk source.
    #[clap(long, value_parser)]
    lurk: bool,

    /// Chain commitment openings. Opening includes commitment to new function along with output.
    #[clap(long, value_parser)]
    chain: bool,

    /// Quote input before passing to function when opening. Otherwise input will be passed unevaluated and unquoted. --quote-input and --eval-input would cancel each other out if used in conjunction, so is probably not what is desired.
    #[clap(long, value_parser)]
    quote_input: bool,
}

#[derive(Args, Debug)]
struct Eval {
    /// Path to expression source
    #[clap(short = 'x', long, value_parser)]
    expression: PathBuf,

    /// Wrap evaluation result in a claim
    #[clap(long, value_parser)]
    claim: Option<PathBuf>,

    // Expression is lurk source.
    #[clap(long, value_parser)]
    lurk: bool,
}

#[derive(Args, Debug)]
struct Prove {
    /// Path to expression source
    #[clap(short = 'x', long, value_parser)]
    expression: Option<PathBuf>,

    /// Path to proof input
    #[clap(short, long, value_parser)]
    proof: PathBuf,

    /// Number of circuit reductions per step
    #[clap(short = 'r', long, default_value = "1", value_parser)]
    reduction_count: usize,

    /// Path to claim to prove
    #[clap(long, value_parser)]
    claim: Option<PathBuf>,

    // Expression is lurk source.
    #[clap(long, value_parser)]
    lurk: bool,
}

#[derive(Args, Debug)]
struct Verify {
    /// Path to proof input
    #[clap(short, long, value_parser)]
    proof: PathBuf,
}

impl Commit {
    fn commit(&self, limit: usize) {
        let s = &mut Store::<S1>::default();

        let mut function = if self.lurk {
            let path = env::current_dir().unwrap().join(&self.function);
            let src = read_to_string(path).unwrap();

            CommittedExpression {
                expr: LurkPtr::Source(src),
                secret: None,
                commitment: None,
            }
        } else {
            CommittedExpression::read_from_path(&self.function).unwrap()
        };
        let fun_ptr = function.expr_ptr(s, limit).unwrap();
        let function_map = committed_expression_store();

        let commitment = if let Some(secret) = function.secret {
            let commitment = Commitment::from_ptr_and_secret(s, &fun_ptr, secret);

            function.commitment = Some(commitment);

            function_map.set(commitment, &function).unwrap();
            function.write_to_path(&self.function);

            commitment
        } else {
            let (commitment, secret) = Commitment::from_ptr_with_hiding(s, &fun_ptr);
            function.secret = Some(secret);
            function.commitment = Some(commitment);

            function_map.set(commitment, &function).unwrap();

            function.write_to_path(&self.function);

            commitment
        };
        if let Some(commitment_path) = &self.commitment {
            commitment.write_to_path(commitment_path);
        } else {
            serde_json::to_writer(io::stdout(), &commitment).unwrap();
        }
    }
}

impl Open {
    fn open(&self, limit: usize, eval_input: bool) {
        assert!(
            !(self.commitment.is_some() && self.function.is_some()),
            "commitment and function must not both be supplied"
        );

        let s = &mut Store::<S1>::default();
        let rc = ReductionCount::try_from(self.reduction_count).unwrap();
        let prover = NovaProver::<S1>::new(rc.count());
        let pp = public_params(rc.count()).unwrap();
        let function_map = committed_expression_store();

        let handle_proof = |out_path, proof: Proof<S1>| {
            proof.write_to_path(out_path);
            proof.verify(&pp).expect("created opening doesn't verify");
        };

        let handle_claim = |claim: Claim<S1>| serde_json::to_writer(io::stdout(), &claim);

        if let Some(request_path) = &self.request {
            assert!(!self.chain, "chain and request may not both be specified");
            let request = opening_request(request_path).expect("failed to read opening request");

            if let Some(out_path) = &self.proof {
                let proof =
                    Opening::open_and_prove(s, request, limit, false, &prover, &pp).unwrap();

                handle_proof(out_path, proof);
            } else {
                let function = function_map
                    .get(&request.commitment)
                    .expect("committed function not found");
                let input = request.input.eval(s, limit).unwrap();

                let claim = Opening::apply(s, input, function, limit, self.chain).unwrap();
                handle_claim(claim).unwrap();
            }
        } else {
            let function = if let Some(comm_string) = &self.commitment {
                let commitment = Commitment::from_hex(comm_string)
                    .map_err(Error::CommitmentParseError)
                    .unwrap();

                function_map
                    .get(&commitment)
                    .expect("committed function not found")
            } else {
                let function_path = self.function.as_ref().expect("function missing");
                if self.lurk {
                    let path = env::current_dir().unwrap().join(function_path);
                    let src = read_to_string(path).unwrap();
                    CommittedExpression {
                        expr: LurkPtr::Source(src),
                        secret: None,
                        commitment: None,
                    }
                } else {
                    CommittedExpression::read_from_path(function_path).unwrap()
                }
            };

            let input_path = self.input.as_ref().expect("input missing");
            let input = input(s, input_path, eval_input, limit, self.quote_input).unwrap();

            if let Some(out_path) = &self.proof {
                let proof = Opening::apply_and_prove(
                    s, input, function, limit, self.chain, false, &prover, &pp,
                )
                .unwrap();

                handle_proof(out_path, proof);
            } else {
                let claim = Opening::apply(s, input, function, limit, self.chain).unwrap();

                handle_claim(claim).unwrap();
            }
        };
    }
}

impl Eval {
    fn eval(&self, limit: usize) {
        let s = &mut Store::<S1>::default();

        let expr = expression(s, &self.expression, self.lurk, limit).unwrap();

        let evaluation = Evaluation::eval(s, expr, limit).unwrap();

        match &self.claim {
            Some(out_path) => {
                let claim = Claim::<S1>::Evaluation(evaluation);
                claim.write_to_path(out_path);
            }
            None => {
                serde_json::to_writer(io::stdout(), &evaluation).unwrap();
            }
        }
    }
}

impl Prove {
    fn prove(&self, limit: usize) {
        let s = &mut Store::<S1>::default();
        let rc = ReductionCount::try_from(self.reduction_count).unwrap();
        let prover = NovaProver::<S1>::new(rc.count());
        let pp = public_params(rc.count()).unwrap();

        let proof = match &self.claim {
            Some(claim) => {
                assert!(
                    self.expression.is_none(),
                    "claim and expression must not both be supplied"
                );
                Proof::prove_claim(
                    s,
                    &Claim::read_from_path(claim).unwrap(),
                    limit,
                    false,
                    &prover,
                    &pp,
                )
                .unwrap()
            }

            None => {
                let expr = expression(
                    s,
                    self.expression.as_ref().expect("expression missing"),
                    self.lurk,
                    limit,
                )
                .unwrap();

                Proof::eval_and_prove(s, expr, limit, false, &prover, &pp).unwrap()
            }
        };

        // Write first, so prover can debug if proof doesn't verify (it should).
        proof.write_to_path(&self.proof);
        proof.verify(&pp).expect("created proof doesn't verify");
    }
}

impl Verify {
    fn verify(&self, cli_error: bool) {
        let proof = proof(Some(&self.proof)).unwrap();
        let pp = public_params(proof.reduction_count.count()).unwrap();
        let result = proof.verify(&pp).unwrap();

        serde_json::to_writer(io::stdout(), &result).unwrap();

        if result.verified {
            info!("Verification succeeded.");
        } else if cli_error {
            serde_json::to_writer(io::stderr(), &result).unwrap();
            std::process::exit(1);
        };
    }
}

fn read_from_path<P: AsRef<Path>, F: LurkField + Serialize>(
    store: &mut Store<F>,
    path: P,
) -> Result<Ptr<F>, Error> {
    let path = env::current_dir().unwrap().join(path);
    let input = read_to_string(path).unwrap();
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
    ) = evaluate(store, src, limit)?;

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

fn expression<P: AsRef<Path>, F: LurkField + Serialize + DeserializeOwned>(
    store: &mut Store<F>,
    expression_path: P,
    lurk: bool,
    limit: usize,
) -> Result<Ptr<F>, Error> {
    if lurk {
        read_from_path(store, expression_path)
    } else {
        let expression = Expression::read_from_path(expression_path)?;
        let expr = expression.expr.ptr(store, limit);
        Ok(expr)
    }
}

fn opening_request<P: AsRef<Path>, F: LurkField + Serialize + DeserializeOwned>(
    request_path: P,
) -> Result<OpeningRequest<F>, Error> {
    OpeningRequest::read_from_path(request_path)
}

// Get proof from supplied path or else from stdin.
fn proof<'a, P: AsRef<Path>, F: LurkField>(proof_path: Option<P>) -> Result<Proof<'a, F>, Error>
where
    F: Serialize + for<'de> Deserialize<'de>,
{
    match proof_path {
        Some(path) => Proof::read_from_path(path),
        None => Proof::read_from_stdin(),
    }
}

fn main() {
    let cli = Cli::parse();

    pretty_env_logger::formatted_builder()
        .filter_level(cli.verbose.log_level_filter())
        .init();

    match &cli.command {
        Command::Commit(c) => c.commit(cli.limit),
        Command::Open(o) => o.open(cli.limit, cli.eval_input),
        Command::Eval(e) => e.eval(cli.limit),
        Command::Prove(p) => p.prove(cli.limit),
        Command::Verify(v) => v.verify(cli.error),
    }
}
