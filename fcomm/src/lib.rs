use log::info;
use std::convert::TryFrom;
use std::fs::{self, File};
use std::io::{self, BufReader};
use std::path::Path;

use bellperson::{groth16, SynthesisError};
use blstrs::{Bls12, Scalar};

use ff::PrimeField;
use hex::FromHex;
use libipld::{
    json::DagJsonCodec,
    multihash::{Code, MultihashDigest},
    prelude::Codec,
    serde::to_ipld,
    Cid,
};
use lurk::circuit::ToInputs;
use lurk::eval::{empty_sym_env, Evaluable, Evaluator, Status, IO};
use lurk::field::LurkField;
use lurk::proof::{
    self,
    groth16::{Groth16, Groth16Prover, INNER_PRODUCT_SRS},
};
use lurk::store::{Pointer, Ptr, ScalarPointer, Store, Tag};
use lurk::writer::Write;
use lurk::Num;
use once_cell::sync::OnceCell;
use pairing_lib::{Engine, MultiMillerLoop};
use rand::rngs::OsRng;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

mod file_map;

use file_map::FileMap;

pub const DEFAULT_REDUCTION_COUNT: ReductionCount = ReductionCount::One;
pub static VERBOSE: OnceCell<bool> = OnceCell::new();

fn bls12_proof_cache() -> FileMap<Proof<Bls12>> {
    FileMap::<Proof<Bls12>>::new("bls12_proofs").unwrap()
}

fn get_pvk(rc: ReductionCount) -> groth16::PreparedVerifyingKey<Bls12> {
    let groth_prover = Groth16Prover::new(rc.reduction_frame_count());

    info!("Getting Parameters");
    let groth_params = groth_prover.groth_params().unwrap();

    info!("Preparing verifying key");
    groth16::prepare_verifying_key(&groth_params.vk)
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReductionCount {
    One,
    Five,
    Ten,
}

#[derive(Serialize, Deserialize, Clone, Debug, Default, PartialEq, Eq)]
pub struct Evaluation {
    pub expr: String,
    pub env: String,
    pub cont: String,
    pub expr_out: String,
    pub env_out: String,
    pub cont_out: String,
    pub status: Status,
    pub iterations: Option<usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Commitment<F: LurkField> {
    pub comm: F,
}

impl<F: LurkField> Serialize for Commitment<F> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        hex::serde::serialize(self.comm.to_repr().as_ref(), serializer)
    }
}

impl<'de, F: LurkField> Deserialize<'de> for Commitment<F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        hex::serde::deserialize(deserializer)
    }
}

impl<F: LurkField> FromHex for Commitment<F> {
    type Error = hex::FromHexError;

    fn from_hex<T>(s: T) -> Result<Self, <Self as FromHex>::Error>
    where
        T: AsRef<[u8]>,
    {
        let v = Vec::from_hex(s)?;
        let mut repr = <F as PrimeField>::Repr::default();
        repr.as_mut()[..32].copy_from_slice(&v[..]);

        Ok(Commitment {
            comm: F::from_repr(repr).unwrap(),
        })
    }
}
#[derive(Serialize, Deserialize, Clone)]
pub struct Expression {
    pub source: String,
}

#[derive(Debug, Serialize, Deserialize, Clone, Eq, PartialEq)]
pub struct Opening<F: LurkField> {
    pub input: String,
    pub output: String,
    pub status: Status,
    pub commitment: Commitment<F>,
    pub new_commitment: Option<Commitment<F>>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct Function<F: LurkField + Serialize> {
    pub source: String,
    #[serde(bound(serialize = "F: Serialize", deserialize = "F: Deserialize<'de>"))]
    pub secret: Option<F>,
    pub commitment: Option<Commitment<F>>,
}

#[derive(Serialize, Deserialize)]
pub struct VerificationResult {
    pub verified: bool,
}

#[derive(Serialize, Deserialize)]
pub struct Proof<E: Engine + MultiMillerLoop>
where
    <E as Engine>::Gt: blstrs::Compress + Serialize,
    <E as Engine>::G1: Serialize,
    <E as Engine>::G1Affine: Serialize,
    <E as Engine>::G2Affine: Serialize,
    <E as Engine>::Fr: Serialize + LurkField,
    <E as Engine>::Gt: blstrs::Compress + Serialize,
{
    #[serde(bound(
        serialize = "Claim<E::Fr>: Serialize",
        deserialize = "Claim<E::Fr>: Deserialize<'de>"
    ))]
    pub claim: Claim<E::Fr>,
    #[serde(bound(
        serialize = "proof::groth16::Proof<E>: Serialize",
        deserialize = "proof::groth16::Proof<E>: Deserialize<'de>"
    ))]
    pub proof: proof::groth16::Proof<E>,
    pub reduction_count: ReductionCount,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum Claim<F: LurkField> {
    Evaluation(Evaluation),
    #[serde(bound(
        serialize = "Opening<F>: Serialize",
        deserialize = "Opening<F>: Deserialize<'de>"
    ))]
    Opening(Opening<F>),
}

// This is just a rough idea, mostly here so we can plumb it elsewhere. The idea is that a verifier can sign an
// attestation that a given claim's proof was verified. It motivates the use of an online verifier for demo purposes.
// Although real proofs should be fast to verify, they will still be large relative to a small (auditable) bundle like
// this. Even if not entirely realistic, something with this general *shape* is likely to play a role in a recursive
// system where the ability to aggregate proof verification more soundly is possible.
#[derive(Serialize, Deserialize)]
pub struct Cert {
    pub claim_cid: Cid,
    pub proof_cid: Cid,
    pub verified: VerificationResult,
    pub verifier_id: String,
    pub signature: String,
}

#[allow(dead_code)]
impl<F: LurkField> Claim<F> {
    pub fn is_evaluation(&self) -> bool {
        self.evaluation().is_some()
    }
    pub fn is_opening(&self) -> bool {
        self.opening().is_some()
    }
    pub fn evaluation(&self) -> Option<Evaluation> {
        match self {
            Self::Evaluation(e) => Some(e.clone()),
            _ => None,
        }
    }
    pub fn opening(&self) -> Option<Opening<F>> {
        match self {
            Self::Opening(o) => Some(o.clone()),
            _ => None,
        }
    }
}

type E = Error;
impl TryFrom<usize> for ReductionCount {
    type Error = E;

    fn try_from(count: usize) -> Result<Self, <Self as TryFrom<usize>>::Error> {
        match count {
            1 => Ok(ReductionCount::One),
            5 => Ok(ReductionCount::Five),
            10 => Ok(ReductionCount::Ten),
            c => Err(Error::UnsupportedReductionCount(c)),
        }
    }
}
impl ReductionCount {
    fn reduction_frame_count(&self) -> usize {
        match self {
            Self::One => 1,
            Self::Five => 5,
            Self::Ten => 10,
        }
    }
}

#[derive(Debug)]
pub enum Error {
    VerificationError(String),
    UnsupportedReductionCount(usize),
    IOError(io::Error),
    JsonError(serde_json::Error),
    SynthesisError(SynthesisError),
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::IOError(err)
    }
}
impl From<serde_json::Error> for Error {
    fn from(err: serde_json::Error) -> Error {
        Error::JsonError(err)
    }
}
impl From<SynthesisError> for Error {
    fn from(err: SynthesisError) -> Error {
        Error::SynthesisError(err)
    }
}

pub trait Id
where
    Self: Sized,
{
    fn id(&self) -> String;
    fn cid(&self) -> Cid;
    fn has_id(&self, id: String) -> bool;
}

pub trait Key
where
    Self: Sized,
{
    fn key(&self) -> Cid;
}

impl<T: Serialize> Id for T
where
    for<'de> T: Deserialize<'de>,
{
    fn cid(&self) -> Cid {
        let ipld = to_ipld(self).unwrap();
        let dag_json = DagJsonCodec.encode(&ipld).unwrap();

        let digest = Code::Blake3_256.digest(&dag_json);
        Cid::new_v1(0x55, digest)
    }

    fn id(&self) -> String {
        self.cid().to_string()
    }

    fn has_id(&self, id: String) -> bool {
        self.id() == id
    }
}

pub trait FileStore
where
    Self: Sized,
{
    fn write_to_path<P: AsRef<Path>>(&self, path: P);
    fn read_from_path<P: AsRef<Path>>(path: P) -> Result<Self, Error>;
    fn read_from_stdin() -> Result<Self, Error>;
}

impl<T: Serialize> FileStore for T
where
    for<'de> T: Deserialize<'de>,
{
    fn write_to_path<P: AsRef<Path>>(&self, path: P) {
        fs::write(path, serde_json::to_string(self).unwrap()).expect("failed to write file");
    }
    fn read_from_path<P: AsRef<Path>>(path: P) -> Result<Self, Error> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        Ok(serde_json::from_reader(reader).expect("failed to read file"))
    }
    fn read_from_stdin() -> Result<Self, Error> {
        let reader = BufReader::new(io::stdin());
        Ok(serde_json::from_reader(reader).expect("failed to read from stdin"))
    }
}

impl Evaluation {
    fn new<F: LurkField>(
        s: &mut Store<F>,
        input: IO<F>,
        output: IO<F>,
        iterations: Option<usize>, // This might be padded, so is not quite 'iterations' in the sense of number of actual reduction steps required
                                   // to evaluate.
    ) -> Self {
        let status: Status = output.cont.into();
        let terminal = status.is_terminal();

        // For now, conservatively hide all outputs unless output is terminal. TODO: let evaluator configure this in a
        // more fine-grained way, including no hiding.
        // NOTE: If anything is hidden, a proof won't be possible.
        macro_rules! maybe_hide {
            ($x:expr) => {
                if terminal {
                    $x
                } else {
                    "".to_string()
                }
            };
        }

        let expr = input.expr.fmt_to_string(s);
        let env = input.env.fmt_to_string(s);
        let cont = input.cont.fmt_to_string(s);

        let expr_out = maybe_hide!(output.expr.fmt_to_string(s));
        let env_out = maybe_hide!(output.env.fmt_to_string(s));
        let cont_out = maybe_hide!(output.cont.fmt_to_string(s));

        Self {
            expr,
            env,
            cont,
            expr_out,
            env_out,
            cont_out,
            status,
            iterations,
        }
    }

    pub fn eval<F: LurkField + Serialize>(
        store: &mut Store<F>,
        expr: Ptr<F>,
        limit: usize,
    ) -> Self {
        let env = empty_sym_env(store);
        let mut evaluator = Evaluator::new(expr, env, store, limit);

        let input = evaluator.initial();

        let (output, iterations) = evaluator.eval();

        Self::new(store, input, output, Some(iterations))
    }
}

impl<F: LurkField + Serialize> Commitment<F> {
    pub fn from_cons(s: &mut Store<F>, ptr: &Ptr<F>) -> Self {
        let digest = *s.hash_expr(ptr).expect("couldn't hash ptr").value();

        assert_eq!(Tag::Cons, ptr.tag());

        Commitment { comm: digest }
    }

    pub fn ptr(&self, s: &mut Store<F>) -> Ptr<F> {
        s.intern_opaque_cons(self.comm)
    }

    pub fn from_ptr_with_hiding(s: &mut Store<F>, function_ptr: &Ptr<F>) -> (Self, F) {
        let secret = F::random(OsRng);

        let commitment = Self::from_ptr_and_secret(s, function_ptr, secret);

        (commitment, secret)
    }

    pub fn from_ptr_and_secret(s: &mut Store<F>, function_ptr: &Ptr<F>, secret: F) -> Self {
        let secret_num = Num::from_scalar(secret);
        let secret_ptr = s.intern_num(secret_num);

        let hidden = s.cons(secret_ptr, *function_ptr);

        Self::from_cons(s, &hidden)
    }

    fn construct_with_fun_application(
        s: &mut Store<F>,
        function: Function<F>,
        input: Ptr<F>,
        limit: usize,
    ) -> (Self, Ptr<F>) {
        let cdr = s.sym("cdr");
        let quote = s.sym("quote");

        let fun_ptr = function.fun_ptr(s, limit);
        let secret = function.secret.expect("Function secret missing");

        let commitment = Self::from_ptr_and_secret(s, &fun_ptr, secret);

        let secret_ptr = s.num(Num::from_scalar(secret));
        let comm_ptr = s.cons(secret_ptr, fun_ptr);

        let quoted_comm_ptr = s.list(&[quote, comm_ptr]);

        // (cdr <commitment>)
        let fun_expr = s.list(&[cdr, quoted_comm_ptr]);

        // ((cdr <commitment>) input)
        let expression = s.list(&[fun_expr, input]);

        (commitment, expression)
    }

    fn fun_application(&self, s: &mut Store<F>, input: Ptr<F>) -> Ptr<F> {
        let cdr = s.sym("cdr");
        let quote = s.sym("quote");

        let comm_ptr = self.ptr(s);
        let quoted_comm_ptr = s.list(&[quote, comm_ptr]);

        // <commitment> is (fun-expr . secret)

        // (cdr <commitment>)
        let fun_expr = s.list(&[cdr, quoted_comm_ptr]);

        // ((cdr commitment) input)
        s.list(&[fun_expr, input])
    }
}

impl<F: LurkField + Serialize> Function<F> {
    pub fn fun_ptr(&self, s: &mut Store<F>, limit: usize) -> Ptr<F> {
        let source_ptr = s.read(&self.source).expect("could not read source");

        // Evaluate the source to get an actual function.
        let (output, _iterations) = evaluate(s, source_ptr, limit);

        output.expr
    }
}

impl Opening<Scalar> {
    pub fn open_and_prove<P: AsRef<Path>>(
        s: &mut Store<<Bls12 as Engine>::Fr>,
        input: Ptr<<Bls12 as Engine>::Fr>,
        function: Function<<Bls12 as Engine>::Fr>,
        limit: usize,
        chain: bool,
        commitment_path: Option<P>,
        chained_function_path: Option<std::path::PathBuf>,
    ) -> Result<Proof<Bls12>, Error> {
        let rng = OsRng;

        let (commitment, expression) =
            Commitment::construct_with_fun_application(s, function, input, limit);

        info!("Getting Parameters");

        let reduction_count = DEFAULT_REDUCTION_COUNT;
        let groth_prover = Groth16Prover::new(reduction_count.reduction_frame_count());
        let groth_params = groth_prover.groth_params().unwrap();

        info!("Starting Proving");

        let (groth_proof, _public_input, public_output) = groth_prover
            .outer_prove(
                groth_params,
                &INNER_PRODUCT_SRS,
                expression,
                empty_sym_env(s),
                s,
                limit,
                rng,
            )
            .unwrap();

        assert!(public_output.is_complete());

        let status = public_output.status();

        let input_string = input.fmt_to_string(s);

        // FIXME: Chaining won't actually work until we can read a literal function. This can be through
        // non-writer/reader serialization/deserialize but it must be implemented.
        let (new_commitment, output_expr) = if chain {
            let cons = public_output.expr;
            let output_expr = s.car(&cons);
            let new_function = s.cdr(&cons);
            let (new_commitment, new_secret) = Commitment::from_ptr_with_hiding(s, &new_function);

            let f = Function::<<Bls12 as Engine>::Fr> {
                source: new_function.fmt_to_string(s),
                secret: Some(new_secret),
                commitment: Some(new_commitment),
            };

            if let Some(p) = chained_function_path {
                f.write_to_path(p);
            };
            (Some(new_commitment), output_expr)
        } else {
            (None, public_output.expr)
        };

        let output_string = if status.is_terminal() {
            // Only actual output if result is terminal.
            output_expr.fmt_to_string(s)
        } else {
            // We don't want to leak any internal information in the case of incomplete computations.
            // Provers might want to expose results in the case of explicit errors.
            // For now, don't -- but consider allowing it as an option.
            "".to_string()
        };

        if let Some(ref c) = new_commitment {
            if let Some(path) = commitment_path {
                c.write_to_path(path);
            } else {
                panic!("commitment path missing");
            }
        }

        let proof = Proof {
            claim: Claim::Opening(Opening {
                commitment,
                new_commitment,
                input: input_string,
                output: output_string,
                status,
            }),
            reduction_count,
            proof: groth_proof,
        };

        Ok(proof)
    }
}

impl Proof<Bls12> {
    pub fn eval_and_prove(
        s: &mut Store<<Bls12 as Engine>::Fr>,
        expr: Ptr<<Bls12 as Engine>::Fr>,
        limit: usize,
        only_use_cached_proofs: bool,
    ) -> Result<Self, Error> {
        let env = empty_sym_env(s);
        let cont = s.intern_cont_outermost();
        let input = IO { expr, env, cont };

        let (public_output, _iterations) = evaluate(s, expr, limit);
        let evaluation = Evaluation::new(s, input, public_output, None);
        let claim = Claim::Evaluation(evaluation);

        Self::prove_claim(s, claim, limit, only_use_cached_proofs)
    }

    pub fn prove_claim(
        s: &mut Store<<Bls12 as Engine>::Fr>,
        claim: Claim<Scalar>,
        limit: usize,
        only_use_cached_proofs: bool,
    ) -> Result<Self, Error> {
        let rng = OsRng;
        let proof_map = bls12_proof_cache();

        if let Some(proof) = proof_map.get(claim.cid()) {
            dbg!("found cached proof!");
            return Ok(proof);
        }

        if only_use_cached_proofs {
            // FIXME: Error handling.
            panic!("no cached proof");
        }

        let reduction_count = DEFAULT_REDUCTION_COUNT;

        info!("Getting Parameters");
        let groth_prover = Groth16Prover::new(reduction_count.reduction_frame_count());
        let groth_params = groth_prover.groth_params().unwrap();

        info!("Starting Proving");

        let (expr, env) = match &claim {
            Claim::Evaluation(e) => (
                s.read(&e.expr).expect("bad expression"),
                s.read(&e.env).expect("bad env"),
            ),
            _ => todo!(),
        };

        let (groth_proof, _public_input, public_output) = groth_prover
            .outer_prove(groth_params, &INNER_PRODUCT_SRS, expr, env, s, limit, rng)
            .expect("Groth proving failed");

        assert!(public_output.is_complete());

        let proof = Proof {
            claim: claim.clone(),
            reduction_count,
            proof: groth_proof,
        };

        proof_map.set(claim.cid(), &proof).unwrap();

        Ok(proof)
    }
    pub fn verify(&self) -> Result<VerificationResult, Error> {
        let (public_inputs, public_outputs) = match self.claim {
            Claim::Evaluation(_) => self.verify_evaluation(),
            Claim::Opening(_) => self.verify_opening(),
        }?;
        let mut rng = OsRng;

        info!("Getting Parameters");

        let count = self.proof.proof_count;
        let rc = self.reduction_count;
        let pvk = get_pvk(rc);

        info!("Specializing SRS for {} sub-proofs.", count);
        let srs_vk = INNER_PRODUCT_SRS.specialize_vk(count);
        info!("Starting Verification");

        let verified = Groth16Prover::verify(
            &pvk,
            &srs_vk,
            &public_inputs,
            &public_outputs,
            &self.proof.proof,
            &mut rng,
        )
        .expect("error verifying");

        let result = VerificationResult::new(verified);

        Ok(result)
    }

    pub fn verify_evaluation(&self) -> Result<(Vec<Scalar>, Vec<Scalar>), Error> {
        let mut s = Store::<Scalar>::default();

        let evaluation = &self.claim.evaluation().expect("expected evaluation claim");

        let input_io = {
            let expr = s
                .read(&evaluation.expr)
                .ok_or_else(|| Error::VerificationError("failed to read expr".into()))?;
            let env = s
                .read(&evaluation.env)
                .ok_or_else(|| Error::VerificationError("failed to read env".into()))?;

            // FIXME: We ignore cont and assume Outermost, since we can't read a Cont.
            let cont = s.intern_cont_outermost();

            IO::<Scalar> { expr, env, cont }
        };

        let public_inputs = input_io.to_inputs(&s);

        let output_io = {
            let expr = s
                .read(&evaluation.expr_out)
                .ok_or_else(|| Error::VerificationError("failed to read expr_out".into()))?;
            let env = s.read(&evaluation.env_out).expect("failed to read env_out");
            let cont = evaluation
                .status
                .to_cont(&mut s)
                .ok_or_else(|| Error::VerificationError("continuation cannot be proved".into()))?;

            IO::<Scalar> { expr, env, cont }
        };

        let public_outputs = output_io.to_inputs(&s);

        Ok((public_inputs, public_outputs))
    }

    pub fn verify_opening(&self) -> Result<(Vec<Scalar>, Vec<Scalar>), Error> {
        let mut s = Store::<Scalar>::default();

        assert!(self.claim.is_opening());

        let opening = self.claim.opening().expect("expected opening claim");
        let output = s.read(&opening.output).expect("could not read output");
        let input = s.read(&opening.input).expect("could not read input");

        let expression = opening.commitment.fun_application(&mut s, input);
        let expr = s
            .hash_expr(&expression)
            .expect("failed to hash input expression");

        let empty_env = s.hash_expr(&empty_sym_env(&s)).unwrap();
        let outermost = s.intern_cont_outermost();
        let cont = s.hash_cont(&outermost).unwrap();

        let public_inputs = vec![
            *expr.tag(),
            *expr.value(),
            *empty_env.tag(),
            *empty_env.value(),
            *cont.tag(),
            *cont.value(),
        ];

        let output_io = IO::<Scalar> {
            expr: output,
            env: empty_sym_env(&s),
            cont: s.intern_cont_terminal(),
        };

        let public_outputs = output_io.to_inputs(&s);

        Ok((public_inputs, public_outputs))
    }
}

impl Key for Proof<Bls12> {
    fn key(&self) -> Cid {
        self.claim.cid()
    }
}

impl VerificationResult {
    fn new(verified: bool) -> Self {
        Self { verified }
    }
}

pub fn evaluate<F: LurkField + Serialize>(
    store: &mut Store<F>,
    expr: Ptr<F>,
    limit: usize,
) -> (IO<F>, usize) {
    let env = empty_sym_env(store);
    let mut evaluator = Evaluator::new(expr, env, store, limit);

    let (io, iterations) = evaluator.eval();

    assert!(io.is_terminal());
    (io, iterations)
}
