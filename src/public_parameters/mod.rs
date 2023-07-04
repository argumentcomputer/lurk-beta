use log::info;
use std::convert::TryFrom;
use std::fs::File;
use std::io::{self, BufReader, BufWriter};
use std::path::Path;
use std::sync::Arc;

#[cfg(not(target_arch = "wasm32"))]
use proptest::prelude::*;
#[cfg(not(target_arch = "wasm32"))]
use proptest_derive::Arbitrary;

use crate::coprocessor::Coprocessor;
use crate::error::ReductionError;
#[cfg(not(target_arch = "wasm32"))]
use crate::field::FWrap;
use crate::{
    circuit::ToInputs,
    eval::{
        empty_sym_env,
        lang::{Coproc, Lang},
        Evaluable, Evaluator, Status, Witness, IO,
    },
    field::LurkField,
    hash::PoseidonCache,
    proof::nova::{self, NovaProver, PublicParams},
    proof::Prover,
    ptr::{ContPtr, Ptr},
    store::Store,
    tag::ExprTag,
    writer::Write,
    z_expr::ZExpr,
    z_ptr::ZExprPtr,
    z_store::ZStore,
};
use ff::PrimeField;
use hex::FromHex;
use once_cell::sync::OnceCell;
use pasta_curves::pallas;
use rand::rngs::OsRng;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

pub mod error;
mod file_map;
mod registry;

use error::Error;
use file_map::FileMap;

pub const DEFAULT_REDUCTION_COUNT: ReductionCount = ReductionCount::Ten;
pub static VERBOSE: OnceCell<bool> = OnceCell::new();

pub type S1 = pallas::Scalar;

mod base64 {
    use serde::{Deserialize, Serialize};
    use serde::{Deserializer, Serializer};

    pub(crate) fn serialize<S: Serializer>(v: &Vec<u8>, s: S) -> Result<S::Ok, S::Error> {
        let base64 = base64::encode(v);
        String::serialize(&base64, s)
    }

    pub(crate) fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Vec<u8>, D::Error> {
        let base64 = String::deserialize(d)?;
        base64::decode(base64.as_bytes()).map_err(serde::de::Error::custom)
    }
}

pub type NovaProofCache = FileMap<String, Proof<'static, S1>>;
pub fn nova_proof_cache(reduction_count: usize) -> NovaProofCache {
    FileMap::<String, Proof<'_, S1>>::new(format!("nova_proofs.{}", reduction_count)).unwrap()
}

pub type CommittedExpressionMap = FileMap<Commitment<S1>, CommittedExpression<S1>>;
pub fn committed_expression_store() -> CommittedExpressionMap {
    FileMap::<Commitment<S1>, CommittedExpression<S1>>::new("committed_expressions").unwrap()
}

pub fn public_params<C: Coprocessor<S1> + Serialize + DeserializeOwned + 'static>(
    rc: usize,
    lang: Arc<Lang<S1, C>>,
) -> Result<Arc<PublicParams<'static, C>>, Error> {
    let f = |lang: Arc<Lang<S1, C>>| Arc::new(nova::public_params(rc, lang));
    registry::CACHE_REG.get_coprocessor_or_update_with(rc, f, lang)
}

// Number of circuit reductions per step, equivalent to `chunk_frame_count`
#[derive(Clone, Copy, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReductionCount {
    One,
    Five,
    Ten,
    OneHundred,
}

#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
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

#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
#[derive(Serialize, Deserialize, Clone, Debug, Default, PartialEq, Eq)]
pub struct PtrEvaluation<F: LurkField> {
    pub expr: LurkPtr<F>,
    pub env: LurkPtr<F>,
    pub cont: LurkCont,
    pub expr_out: LurkPtr<F>,
    pub env_out: LurkPtr<F>,
    pub cont_out: LurkCont,
    pub status: Status,
    pub iterations: Option<usize>,
}

#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Commitment<F: LurkField> {
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(strategy = "any::<FWrap<F>>().prop_map(|x| x.0)")
    )]
    pub comm: F,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct OpeningRequest<F: LurkField> {
    pub commitment: Commitment<F>,
    pub input: Expression<F>,
    pub chain: bool,
}

impl<F: LurkField> ToString for Commitment<F> {
    fn to_string(&self) -> String {
        let s = serde_json::to_string(&self).unwrap();
        // Remove quotation marks. Yes, dumb hacks are happening.
        s[1..s.len() - 1].to_string()
    }
}

impl<F: LurkField> Serialize for Commitment<F> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // Use be_bytes for consistency with PrimeField printed representation.
        let be_bytes: Vec<u8> = self
            .comm
            .to_repr()
            .as_ref()
            .iter()
            .rev()
            .map(|x| x.to_owned())
            .collect();

        hex::serde::serialize(be_bytes, serializer)
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
        let mut v = Vec::from_hex(s)?;
        v.reverse();
        let mut repr = <F as PrimeField>::Repr::default();
        repr.as_mut()[..32].copy_from_slice(&v[..]);

        Ok(Commitment {
            comm: F::from_repr(repr).unwrap(),
        })
    }
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct Expression<F: LurkField> {
    pub expr: LurkPtr<F>,
}

#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
#[derive(Debug, Serialize, Deserialize, Clone, Eq, PartialEq)]
pub struct Opening<F: LurkField> {
    pub input: String,
    pub output: String,
    pub status: Status,
    pub commitment: Commitment<F>,
    pub new_commitment: Option<Commitment<F>>,
}

#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq)]
pub struct ZBytes {
    #[serde(with = "base64")]
    z_store: Vec<u8>,
    #[serde(with = "base64")]
    z_ptr: Vec<u8>, // can also be a scalar_cont_ptr
}

#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct ZStorePtr<F: LurkField> {
    z_store: ZStore<F>,
    z_ptr: ZExprPtr<F>,
}

#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub enum LurkPtr<F: LurkField> {
    Source(String),
    ZStorePtr(ZStorePtr<F>),
}

#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[derive(Serialize, Deserialize, Clone, Debug, Default, PartialEq, Eq)]
pub enum LurkCont {
    #[default]
    Outermost,
    Terminal,
    Error,
}

impl<F: LurkField> Default for LurkPtr<F> {
    fn default() -> Self {
        Self::Source("nil".to_string())
    }
}

impl<F: LurkField> Eq for LurkPtr<F> {}

#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct CommittedExpression<F: LurkField + Serialize> {
    pub expr: LurkPtr<F>,
    #[cfg_attr(
        not(target_arch = "wasm32"),
        proptest(strategy = "any::<FWrap<F>>().prop_map(|x| Some(x.0))")
    )]
    pub secret: Option<F>,
    pub commitment: Option<Commitment<F>>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VerificationResult {
    pub verified: bool,
}

#[derive(Serialize, Deserialize)]
pub struct Proof<'a, F: LurkField> {
    pub claim: Claim<F>,
    pub proof: nova::Proof<'a, Coproc<S1>>,
    pub num_steps: usize,
    pub reduction_count: ReductionCount,
}

#[cfg_attr(not(target_arch = "wasm32"), derive(Arbitrary))]
#[cfg_attr(not(target_arch = "wasm32"), proptest(no_bound))]
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum Claim<F: LurkField> {
    Evaluation(Evaluation),
    // TODO: Add Expression type
    PtrEvaluation(PtrEvaluation<F>),
    Opening(Opening<F>),
}

impl<F: LurkField + Serialize + for<'de> Deserialize<'de>> Claim<F> {
    /// Returns the ZPtr corresponding to the claim
    pub fn proof_key(&self) -> Result<ZExprPtr<F>, Error> {
        match self {
            Claim::Evaluation(eval) => {
                // Only keying on input and output for now
                let expr_in = ZExprPtr::<F>::from_lurk_str(&eval.expr)?;
                let expr_out = ZExprPtr::<F>::from_lurk_str(&eval.expr_out)?;
                let expr = ZExpr::Cons(expr_in, expr_out);
                Ok(expr.z_ptr(&PoseidonCache::default()))
            }
            Claim::PtrEvaluation(ptr_eval) => {
                let expr_in: ZExprPtr<F> = match &ptr_eval.expr {
                    LurkPtr::Source(source) => ZExprPtr::<F>::from_lurk_str(source)?,
                    LurkPtr::ZStorePtr(zsp) => zsp.z_ptr,
                };
                let expr_out = match &ptr_eval.expr_out {
                    LurkPtr::Source(source) => ZExprPtr::<F>::from_lurk_str(source)?,
                    LurkPtr::ZStorePtr(zsp) => zsp.z_ptr,
                };
                let expr = ZExpr::Cons(expr_in, expr_out);
                Ok(expr.z_ptr(&PoseidonCache::default()))
            }
            // TODO: Is this an appropriate key for commitments?
            Claim::Opening(open) => {
                let expr_in = ZExprPtr::<F>::from_lurk_str(&open.input)?;
                let expr_out = ZExprPtr::<F>::from_lurk_str(&open.output)?;
                let expr = ZExpr::Cons(expr_in, expr_out);
                Ok(expr.z_ptr(&PoseidonCache::default()))
            }
        }
    }
}

// This is just a rough idea, mostly here so we can plumb it elsewhere. The idea is that a verifier can sign an
// attestation that a given claim's proof was verified. It motivates the use of an online verifier for demo purposes.
// Although real proofs should be fast to verify, they will still be large relative to a small (auditable) bundle like
// this. Even if not entirely realistic, something with this general *shape* is likely to play a role in a recursive
// system where the ability to aggregate proof verification more soundly is possible.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct Cert<F: LurkField> {
    pub claim_cid: ZExprPtr<F>,
    pub proof_cid: ZExprPtr<F>,
    pub verified: bool,
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
    pub fn ptr_evaluation(&self) -> Option<PtrEvaluation<F>> {
        match self {
            Self::PtrEvaluation(e) => Some(e.clone()),
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
            100 => Ok(ReductionCount::OneHundred),
            c => Err(Error::UnsupportedReductionCount(c)),
        }
    }
}
impl ReductionCount {
    pub fn count(&self) -> usize {
        match self {
            Self::One => 1,
            Self::Five => 5,
            Self::Ten => 10,
            Self::OneHundred => 100,
        }
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
        let file = File::create(path).expect("failed to create file");
        let writer = BufWriter::new(&file);

        bincode::serialize_into(writer, &self).expect("failed to write file");
    }

    fn read_from_path<P: AsRef<Path>>(path: P) -> Result<Self, Error> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        bincode::deserialize_from(reader)
            .map_err(|e| Error::CacheError(format!("Cache deserialization error: {}", e)))
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
    ) -> Result<Self, Error> {
        let env = empty_sym_env(store);
        let lang = &Lang::<F, Coproc<F>>::new();
        let mut evaluator = Evaluator::new(expr, env, store, limit, lang);

        let input = evaluator.initial();

        let (output, iterations, _) = evaluator.eval().map_err(Error::EvaluationFailure)?;

        Ok(Self::new(store, input, output, Some(iterations)))
    }
}

impl<F: LurkField + Serialize + DeserializeOwned> PtrEvaluation<F> {
    fn new(
        s: &mut Store<F>,
        input: IO<F>,
        output: IO<F>,
        iterations: Option<usize>, // This might be padded, so is not quite 'iterations' in the sense of number of actual reduction steps required
                                   // to evaluate.
    ) -> Self {
        let status: Status = output.cont.into();

        // NOTE: We do not implement the `maybe_hide!` logic found in `Evaluation::new()`. That was a speculative design
        // unsupported by this patch. In ny case, `Evaluation` and `PtrEvaluation` should be unified in the future, and
        // an appropriate hiding mechanism/configuration can be added then.
        Self {
            expr: LurkPtr::from_ptr(s, &input.expr),
            env: LurkPtr::from_ptr(s, &input.env),
            cont: LurkCont::from_cont_ptr(s, &input.cont),
            expr_out: LurkPtr::from_ptr(s, &output.expr),
            env_out: LurkPtr::from_ptr(s, &output.env),
            cont_out: LurkCont::from_cont_ptr(s, &output.cont),
            status,
            iterations,
        }
    }
}

impl<F: LurkField + Serialize + DeserializeOwned> Commitment<F> {
    pub fn from_comm(s: &mut Store<F>, ptr: &Ptr<F>) -> Result<Self, Error> {
        assert_eq!(ExprTag::Comm, ptr.tag);

        let digest = *s
            .hash_expr(ptr)
            .ok_or_else(|| Error::UnknownCommitment)?
            .value();

        Ok(Commitment { comm: digest })
    }

    pub fn ptr(&self, s: &mut Store<F>) -> Ptr<F> {
        s.intern_opaque_comm(self.comm)
    }

    pub fn from_ptr_with_hiding(s: &mut Store<F>, ptr: &Ptr<F>) -> Result<(Self, F), Error> {
        let secret = F::random(OsRng);

        let commitment = Self::from_ptr_and_secret(s, ptr, secret)?;

        Ok((commitment, secret))
    }

    pub fn from_ptr_and_secret(s: &mut Store<F>, ptr: &Ptr<F>, secret: F) -> Result<Self, Error> {
        let hidden = s.hide(secret, *ptr);

        Self::from_comm(s, &hidden)
    }

    // Importantly, this ensures the function and secret are in the Store, s.
    fn construct_with_fun_application(
        s: &mut Store<F>,
        function: CommittedExpression<F>,
        input: Ptr<F>,
        limit: usize,
        lang: &Lang<F, Coproc<F>>,
    ) -> Result<(Self, Ptr<F>), Error> {
        let fun_ptr = function.expr_ptr(s, limit, lang)?;
        let secret = function.secret.expect("CommittedExpression secret missing");

        let commitment = Self::from_ptr_and_secret(s, &fun_ptr, secret)?;

        let open = s.lurk_sym("open");
        let comm_ptr = s.hide(secret, fun_ptr);

        // (open <commitment>)
        let fun_expr = s.list(&[open, comm_ptr]);

        // ((open <commitment>) input)
        let expression = s.list(&[fun_expr, input]);

        Ok((commitment, expression))
    }

    fn fun_application(&self, s: &mut Store<F>, input: Ptr<F>) -> Ptr<F> {
        let open = s.lurk_sym("open");
        let comm_ptr = self.ptr(s);

        // (open <commitment>)
        let fun_expr = s.list(&[open, comm_ptr]);

        // ((open commitment) input)
        s.list(&[fun_expr, input])
    }
}

impl<F: LurkField + Serialize + DeserializeOwned> CommittedExpression<F> {
    pub fn expr_ptr(
        &self,
        s: &mut Store<F>,
        limit: usize,
        lang: &Lang<F, Coproc<F>>,
    ) -> Result<Ptr<F>, Error> {
        let source_ptr = self.expr.ptr(s, limit, lang);

        Ok(source_ptr)
    }
}

impl<F: LurkField + Serialize + DeserializeOwned> LurkPtr<F> {
    pub fn ptr(&self, s: &mut Store<F>, limit: usize, lang: &Lang<F, Coproc<F>>) -> Ptr<F> {
        match self {
            LurkPtr::Source(source) => {
                let ptr = s.read(source).expect("could not read source");
                assert!(!ptr.raw.is_opaque());
                let (out, _) = evaluate(s, ptr, None, limit, lang).unwrap();

                out.expr
            }
            LurkPtr::ZStorePtr(z_store_ptr) => {
                let z_store = &z_store_ptr.z_store;
                let z_ptr = z_store_ptr.z_ptr;
                s.intern_z_expr_ptr(z_ptr, z_store)
                    .expect("failed to intern z_ptr")
            }
        }
    }

    pub fn from_ptr(s: &mut Store<F>, ptr: &Ptr<F>) -> Self {
        let (z_store, z_ptr) = ZStore::new_with_expr(s, ptr);
        let z_ptr = z_ptr.unwrap();
        Self::ZStorePtr(ZStorePtr { z_store, z_ptr })
    }
}

impl LurkCont {
    pub fn cont_ptr<F: LurkField + Serialize + DeserializeOwned>(
        &self,
        s: &mut Store<F>,
    ) -> ContPtr<F> {
        match self {
            Self::Outermost => s.get_cont_outermost(),
            Self::Terminal => s.get_cont_terminal(),
            Self::Error => s.get_cont_error(),
        }
    }

    pub fn from_cont_ptr<F: LurkField + Serialize>(
        _s: &mut Store<F>,
        cont_ptr: &ContPtr<F>,
    ) -> Self {
        use crate::tag::ContTag;

        match cont_ptr.tag {
            ContTag::Outermost => Self::Outermost,
            ContTag::Terminal => Self::Terminal,
            ContTag::Error => Self::Error,
            _ => panic!("unsupported continuation"),
        }
    }
}

impl<F: LurkField + Serialize + DeserializeOwned> Expression<F> {
    pub fn eval(
        &self,
        s: &mut Store<F>,
        limit: usize,
        lang: &Lang<F, Coproc<F>>,
    ) -> Result<Ptr<F>, Error> {
        let expr = self.expr.ptr(s, limit, lang);
        let (io, _iterations) = evaluate(s, expr, None, limit, lang)?;

        Ok(io.expr)
    }
}

impl<'a> Opening<S1> {
    #[allow(clippy::too_many_arguments)]
    pub fn apply_and_prove(
        s: &'a mut Store<S1>,
        input: Ptr<S1>,
        function: CommittedExpression<S1>,
        limit: usize,
        chain: bool,
        only_use_cached_proofs: bool,
        nova_prover: &'a NovaProver<S1, Coproc<S1>>,
        pp: &'a PublicParams<'_, Coproc<S1>>,
        lang: Arc<Lang<S1, Coproc<S1>>>,
    ) -> Result<Proof<'a, S1>, Error> {
        let claim = Self::apply(s, input, function, limit, chain, &lang)?;
        Proof::prove_claim(
            s,
            &claim,
            limit,
            only_use_cached_proofs,
            nova_prover,
            pp,
            lang,
        )
    }

    pub fn open_and_prove(
        s: &'a mut Store<S1>,
        request: OpeningRequest<S1>,
        limit: usize,
        only_use_cached_proofs: bool,
        nova_prover: &'a NovaProver<S1, Coproc<S1>>,
        pp: &'a PublicParams<'_, Coproc<S1>>,
        lang: Arc<Lang<S1, Coproc<S1>>>,
    ) -> Result<Proof<'a, S1>, Error> {
        let input = request.input.expr.ptr(s, limit, &lang);
        let commitment = request.commitment;

        let function_map = committed_expression_store();
        let function = function_map
            .get(&commitment)
            .ok_or(Error::UnknownCommitment)?;

        Self::apply_and_prove(
            s,
            input,
            function,
            limit,
            request.chain,
            only_use_cached_proofs,
            nova_prover,
            pp,
            lang,
        )
    }

    pub fn open(
        s: &mut Store<S1>,
        request: OpeningRequest<S1>,
        limit: usize,
        chain: bool,
        lang: &Lang<S1, Coproc<S1>>,
    ) -> Result<Claim<S1>, Error> {
        let input = request.input.expr.ptr(s, limit, lang);
        let commitment = request.commitment;

        let function_map = committed_expression_store();
        let function = function_map
            .get(&commitment)
            .ok_or(Error::UnknownCommitment)?;

        Self::apply(s, input, function, limit, chain, lang)
    }

    fn _is_chained(&self) -> bool {
        self.new_commitment.is_some()
    }

    fn public_output_expression(&self, s: &mut Store<S1>) -> Ptr<S1> {
        let result = s.read(&self.output).expect("unreadable result");

        if let Some(commitment) = self.new_commitment {
            let c = commitment.ptr(s);

            s.cons(result, c)
        } else {
            result
        }
    }

    pub fn apply(
        s: &mut Store<S1>,
        input: Ptr<S1>,
        function: CommittedExpression<S1>,
        limit: usize,
        chain: bool,
        lang: &Lang<S1, Coproc<S1>>,
    ) -> Result<Claim<S1>, Error> {
        let (commitment, expression) =
            Commitment::construct_with_fun_application(s, function, input, limit, lang)?;
        let (public_output, _iterations) = evaluate(s, expression, None, limit, lang)?;

        let (new_commitment, output_expr) = if chain {
            let cons = public_output.expr;
            let result_expr = s.car(&cons)?;
            let new_comm = s.cdr(&cons)?;

            let new_secret0 = s.secret(new_comm).expect("secret missing");
            let new_secret = *s.hash_expr(&new_secret0).expect("hash missing").value();

            let (_, new_fun) = s.open(new_comm).expect("opening missing");
            let new_commitment = Commitment::from_comm(s, &new_comm)?;

            s.hydrate_scalar_cache();

            let expr = LurkPtr::from_ptr(s, &new_fun);

            let new_function = CommittedExpression::<S1> {
                expr,
                secret: Some(new_secret),
                commitment: Some(new_commitment),
            };

            let function_map = committed_expression_store();
            function_map.set(new_commitment, &new_function)?;
            assert_eq!(new_function, function_map.get(&new_commitment).unwrap());

            (Some(new_commitment), result_expr)
        } else {
            (None, public_output.expr)
        };

        let input_string = input.fmt_to_string(s);
        let status =
            <crate::eval::IO<S1> as Evaluable<S1, Witness<S1>, Coproc<S1>>>::status(&public_output);
        let output_string = if status.is_terminal() {
            // Only actual output if result is terminal.
            output_expr.fmt_to_string(s)
        } else {
            // We don't want to leak any internal information in the case of incomplete computations.
            // Provers might want to expose results in the case of explicit errors.
            // For now, don't -- but consider allowing it as an option.
            "".to_string()
        };

        let claim = Claim::Opening(Opening {
            commitment,
            new_commitment,
            input: input_string,
            output: output_string,
            status,
        });

        Ok(claim)
    }
}

impl<'a> Proof<'a, S1> {
    #[allow(clippy::too_many_arguments)]
    pub fn eval_and_prove(
        s: &'a mut Store<S1>,
        expr: Ptr<S1>,
        supplied_env: Option<Ptr<S1>>,
        limit: usize,
        only_use_cached_proofs: bool,
        nova_prover: &'a NovaProver<S1, Coproc<S1>>,
        pp: &'a PublicParams<'_, Coproc<S1>>,
        lang: Arc<Lang<S1, Coproc<S1>>>,
    ) -> Result<Self, Error> {
        let env = supplied_env.unwrap_or_else(|| empty_sym_env(s));
        let cont = s.intern_cont_outermost();
        let input = IO { expr, env, cont };

        // TODO: It's a little silly that we evaluate here, but evaluation is also repeated in `NovaProver::evaluate_and_prove()`.
        // Refactor to avoid that.
        let (public_output, _iterations) = evaluate(s, expr, supplied_env, limit, &lang)?;

        let claim = if supplied_env.is_some() {
            // This is a bit of a hack, but the idea is that if the env was supplied it's likely to contain a literal function,
            // which we will not be able to read. Therefore, we should not produce a string-based claim.
            let ptr_evaluation = PtrEvaluation::new(s, input, public_output, None);
            Claim::PtrEvaluation(ptr_evaluation)
        } else {
            let evaluation = Evaluation::new(s, input, public_output, None);
            Claim::Evaluation(evaluation)
        };

        Self::prove_claim(
            s,
            &claim,
            limit,
            only_use_cached_proofs,
            nova_prover,
            pp,
            lang,
        )
    }

    pub fn prove_claim(
        s: &'a mut Store<S1>,
        claim: &Claim<S1>,
        limit: usize,
        only_use_cached_proofs: bool,
        nova_prover: &'a NovaProver<S1, Coproc<S1>>,
        pp: &'a PublicParams<'_, Coproc<S1>>,
        lang: Arc<Lang<S1, Coproc<S1>>>,
    ) -> Result<Self, Error> {
        let reduction_count = nova_prover.reduction_count();

        let proof_map = nova_proof_cache(reduction_count);
        let function_map = committed_expression_store();

        let key = claim.proof_key()?.to_base32();

        if let Some(proof) = proof_map.get(&key) {
            return Ok(proof);
        }

        if only_use_cached_proofs {
            // FIXME: Error handling.
            panic!("no cached proof");
        }

        info!("Starting Proving");

        let (expr, env) = match &claim {
            Claim::Evaluation(e) => (
                s.read(&e.expr).expect("bad expression"),
                s.read(&e.env).expect("bad env"),
            ),
            Claim::PtrEvaluation(e) => (e.expr.ptr(s, limit, &lang), e.env.ptr(s, limit, &lang)),
            Claim::Opening(o) => {
                let commitment = o.commitment;

                // In order to prove the opening, we need access to the original function.
                let function = function_map
                    .get(&commitment)
                    .expect("function for commitment missing");

                let input = s.read(&o.input).expect("bad expression");
                let (c, expression) =
                    Commitment::construct_with_fun_application(s, function, input, limit, &lang)?;

                assert_eq!(commitment, c);
                (expression, empty_sym_env(s))
            }
        };

        let (proof, _public_input, _public_output, num_steps) = nova_prover
            .evaluate_and_prove(pp, expr, env, s, limit, lang.clone())
            .expect("Nova proof failed");

        let proof = Self {
            claim: claim.clone(),
            proof,
            num_steps,
            reduction_count: ReductionCount::try_from(reduction_count)?,
        };

        match &claim {
            Claim::Opening(o) => {
                if o.status != Status::Terminal {
                    return Err(Error::OpeningFailure("Claim status is not Terminal".into()));
                };
            }
            Claim::Evaluation(e) => {
                if e.status != Status::Terminal {
                    return Err(Error::EvaluationFailure(ReductionError::Misc(
                        "nonterminal status".into(),
                    )));
                };
            }
            Claim::PtrEvaluation(e) => {
                if e.status != Status::Terminal {
                    return Err(Error::EvaluationFailure(ReductionError::Misc(
                        "nonterminal status".into(),
                    )));
                }
            }
        };

        proof.verify(pp, &lang).expect("Nova verification failed");

        proof_map.set(key, &proof).unwrap();

        Ok(proof)
    }

    pub fn verify(
        &self,
        pp: &PublicParams<'_, Coproc<S1>>,
        lang: &Lang<S1, Coproc<S1>>,
    ) -> Result<VerificationResult, Error> {
        let (public_inputs, public_outputs) = self.io_vecs(lang)?;

        let claim_iterations_and_num_steps_are_consistent = if let Claim::Evaluation(Evaluation {
            iterations: Some(iterations),
            ..
        }) = self.claim
        {
            // Currently, claims created by fcomm don't include the iteration count. If they do, then it should be
            // possible to verify correctness. This may require making the iteration count explicit in the public
            // output. That will allow maintaining iteration count without incrementing during frames added as
            // padding; and it will also allow explicitly masking the count when desired for zero-knowledge.
            // Meanwhile, since Nova currently requires the number of steps to be provided by the verifier, we have
            // to provide it. For now, we should at least be able to calculate this value based on number of real
            // iterations and number of frames per circuit. This is untested and mostly a placeholder to remind us
            // that all of this will need to be handled in a more principled way eventually. (#282)

            let num_steps = self.num_steps;

            let chunk_frame_count = self.reduction_count.count();
            let expected_steps =
                (iterations / chunk_frame_count) + (iterations % chunk_frame_count != 0) as usize;

            expected_steps == num_steps
        } else {
            true
        };

        let verified = claim_iterations_and_num_steps_are_consistent
            && self
                .proof
                .verify(pp, self.num_steps, public_inputs, &public_outputs)
                .expect("error verifying");

        let result = VerificationResult::new(verified);

        Ok(result)
    }

    pub fn evaluation_io(&self, s: &mut Store<S1>) -> Result<(IO<S1>, IO<S1>), Error> {
        let evaluation = &self.claim.evaluation().expect("expected evaluation claim");

        let input_io = {
            let expr = s
                .read(&evaluation.expr)
                .map_err(|_| Error::VerificationError("failed to read expr".into()))?;

            let env = s
                .read(&evaluation.env)
                .map_err(|_| Error::VerificationError("failed to read env".into()))?;

            // FIXME: We ignore cont and assume Outermost, since we can't read a Cont.
            let cont = s.intern_cont_outermost();

            IO::<S1> { expr, env, cont }
        };

        let output_io = {
            let expr = s
                .read(&evaluation.expr_out)
                .map_err(|_| Error::VerificationError("failed to read expr out".into()))?;

            let env = s
                .read(&evaluation.env_out)
                .map_err(|_| Error::VerificationError("failed to read env out".into()))?;
            let cont = evaluation
                .status
                .to_cont(s)
                .ok_or_else(|| Error::VerificationError("continuation cannot be proved".into()))?;

            IO::<S1> { expr, env, cont }
        };

        Ok((input_io, output_io))
    }

    pub fn ptr_evaluation_io(
        &self,
        s: &mut Store<S1>,
        lang: &Lang<S1, Coproc<S1>>,
    ) -> Result<(IO<S1>, IO<S1>), Error> {
        let ptr_evaluation = &self
            .claim
            .ptr_evaluation()
            .expect("expected PtrEvaluation claim");

        let input_io = {
            let expr = ptr_evaluation.expr.ptr(s, 0, lang); // limit is unneeded because we will not eval. we already have the ptr.
            let env = ptr_evaluation.env.ptr(s, 0, lang);
            let cont = ptr_evaluation.cont.cont_ptr(s);

            IO::<S1> { expr, env, cont }
        };

        let output_io = {
            let expr = ptr_evaluation.expr_out.ptr(s, 0, lang);
            let env = ptr_evaluation.env_out.ptr(s, 0, lang);
            let cont = ptr_evaluation.cont_out.cont_ptr(s);

            IO::<S1> { expr, env, cont }
        };

        Ok((input_io, output_io))
    }

    pub fn opening_io(&self, s: &mut Store<S1>) -> Result<(IO<S1>, IO<S1>), Error> {
        assert!(self.claim.is_opening());

        let opening = self.claim.opening().expect("expected opening claim");
        let output = opening.public_output_expression(s);
        let input = s.read(&opening.input).expect("could not read input");

        let expression = opening.commitment.fun_application(s, input);
        let outermost = s.intern_cont_outermost();

        let input_io = IO::<S1> {
            expr: expression,
            env: empty_sym_env(s),
            cont: outermost,
        };

        let output_io = IO::<S1> {
            expr: output,
            env: empty_sym_env(s),
            cont: s.intern_cont_terminal(),
        };

        Ok((input_io, output_io))
    }

    pub fn io(
        &self,
        s: &mut Store<S1>,
        lang: &Lang<S1, Coproc<S1>>,
    ) -> Result<(IO<S1>, IO<S1>), Error> {
        match self.claim {
            Claim::Evaluation(_) => self.evaluation_io(s),
            Claim::PtrEvaluation(_) => self.ptr_evaluation_io(s, lang),
            Claim::Opening(_) => self.opening_io(s),
        }
    }

    fn io_vecs(&self, lang: &Lang<S1, Coproc<S1>>) -> Result<(Vec<S1>, Vec<S1>), Error> {
        let s = &mut Store::<S1>::default();

        self.io(s, lang)
            .map(|(i, o)| (i.to_inputs(s), o.to_inputs(s)))
    }
}

impl VerificationResult {
    fn new(verified: bool) -> Self {
        Self { verified }
    }
}

pub fn evaluate<F: LurkField>(
    store: &mut Store<F>,
    expr: Ptr<F>,
    supplied_env: Option<Ptr<F>>,
    limit: usize,
    lang: &Lang<F, Coproc<F>>,
) -> Result<(IO<F>, usize), Error> {
    let env = supplied_env.unwrap_or_else(|| empty_sym_env(store));
    let mut evaluator = Evaluator::new(expr, env, store, limit, lang);

    let (io, iterations, _) = evaluator.eval().map_err(Error::EvaluationFailure)?;

    assert!(<crate::eval::IO<F> as Evaluable<
        F,
        Witness<F>,
        Coproc<F>,
    >>::is_terminal(&io));
    Ok((io, iterations))
}

#[cfg(test)]
mod test {
    use super::*;
    use std::path::Path;
    use std::sync::Arc;
    use tempfile::Builder;

    use crate::eval::lang::{Coproc, Lang};
    use crate::proof::{nova::NovaProver, Prover};
    use crate::z_data::{from_z_data, to_z_data};

    #[test]
    fn test_cert_serialization() {
        use serde_json::json;

        let c = Commitment {
            comm: S1::from(123),
        };

        let cid = ZExprPtr::from_parts(ExprTag::Comm, c.comm);
        let cert = Cert {
            claim_cid: cid,
            proof_cid: cid,
            verified: true,
            verifier_id: "asdf".to_string(),
            signature: "fdsa".to_string(),
        };
        let json = json!(cert);

        let string = json.to_string();

        let cert_again: Cert<S1> = serde_json::from_str(&string).unwrap();
        assert_eq!(cert, cert_again);
    }

    // Minimal chained functional commitment test
    #[test]
    fn lurk_chained_functional_commitment() {
        let fcomm_path_key = "FCOMM_DATA_PATH";
        let tmp_dir = Builder::new().prefix("tmp").tempdir().expect("tmp dir");
        let tmp_dir_path = Path::new(tmp_dir.path());
        let fcomm_path_val = tmp_dir_path.join("fcomm_data");
        std::env::set_var(fcomm_path_key, fcomm_path_val.clone());
        assert_eq!(
            std::env::var(fcomm_path_key),
            Ok(fcomm_path_val.into_os_string().into_string().unwrap())
        );

        let function_source = "(letrec ((secret 12345) (a (lambda (acc x) (let ((acc (+ acc x))) (cons acc (hide secret (a acc))))))) (a 0))";
        let expected_io = vec![("5", "5"), ("3", "8")];

        let mut function = CommittedExpression::<S1> {
            expr: LurkPtr::Source(function_source.into()),
            secret: None,
            commitment: None,
        };

        let limit = 1000;
        let lang = Lang::new();
        let lang_rc = Arc::new(lang.clone());
        let rc = ReductionCount::One;
        let pp = public_params(rc.count(), lang_rc.clone()).expect("public params");
        let chained = true;
        let s = &mut Store::<S1>::default();

        let io = expected_io.iter();

        let fun_ptr = function.expr_ptr(s, limit, &lang).expect("fun_ptr");

        let (mut commitment, secret) = Commitment::from_ptr_with_hiding(s, &fun_ptr).unwrap();

        function.secret = Some(secret);
        function.commitment = Some(commitment);

        let function_map = committed_expression_store();
        function_map
            .set(commitment, &function)
            .expect("function_map set");

        for (function_input, _expected_output) in io {
            let prover = NovaProver::<S1, Coproc<S1>>::new(rc.count(), lang.clone());

            let input = s.read(function_input).expect("Read error");

            let proof = Opening::apply_and_prove(
                s,
                input,
                function.clone(),
                limit,
                chained,
                false,
                &prover,
                &pp,
                lang_rc.clone(),
            )
            .expect("apply and prove");

            proof.verify(&pp, &lang_rc).expect("Failed to verify");

            let opening = proof.claim.opening().expect("expected opening claim");

            match opening.new_commitment {
                Some(c) => commitment = c,
                _ => panic!("new commitment missing"),
            }
            println!("Commitment: {:?}", commitment);
        }
    }
    proptest! {
      #[test]
      fn prop_z_bytes(x in any::<ZBytes>()) {
        let ser  = to_z_data(&x).expect("write ZBytes");
        let de: ZBytes = from_z_data(&ser).expect("read ZBytes");
        assert_eq!(x, de);

        let ser: Vec<u8> = bincode::serialize(&x).expect("write ZBytes");
        let de: ZBytes = bincode::deserialize(&ser).expect("read ZBytes");
        assert_eq!(x, de);

        let tmp_dir = Builder::new().prefix("tmp").tempdir().expect("tmp dir");
        let tmp_dir_path = Path::new(tmp_dir.path());
        let z_bytes_path = tmp_dir_path.join("zbytes.json");
      x.write_to_path(&z_bytes_path);
      assert_eq!(x, ZBytes::read_from_path(&z_bytes_path).unwrap());
      }
    }

    proptest! {
      #[test]
      fn prop_z_store_ptr(x in any::<ZStorePtr<S1>>()) {
        let ser = to_z_data(&x).expect("write ZStorePtr");
        let de: ZStorePtr<S1> = from_z_data(&ser).expect("read ZStorePtr");
        assert_eq!(x, de);

        let ser: Vec<u8> = bincode::serialize(&x).expect("write ZStorePtr");
        let de: ZStorePtr<S1> = bincode::deserialize(&ser).expect("read ZStorePtr");
        assert_eq!(x, de);

        let tmp_dir = Builder::new().prefix("tmp").tempdir().expect("tmp dir");
        let tmp_dir_path = Path::new(tmp_dir.path());
        let z_store_ptr_path = tmp_dir_path.join("zstoreptr.json");
      x.write_to_path(&z_store_ptr_path);
      assert_eq!(x, ZStorePtr::<S1>::read_from_path(&z_store_ptr_path).unwrap());
      }
    }

    proptest! {
      #[test]
      fn prop_lurk_ptr(x in any::<LurkPtr<S1>>()) {
        let ser = to_z_data(&x).expect("write LurkPtr");
        let de: LurkPtr<S1> = from_z_data(&ser).expect("read LurkPtr");
        assert_eq!(x, de);

        let ser: Vec<u8> = bincode::serialize(&x).expect("write LurkPtr");
        let de: LurkPtr<S1> = bincode::deserialize(&ser).expect("read LurkPtr");
        assert_eq!(x, de);

        let tmp_dir = Builder::new().prefix("tmp").tempdir().expect("tmp dir");
        let tmp_dir_path = Path::new(tmp_dir.path());
        let lurk_ptr_path = tmp_dir_path.join("lurkptr.json");
      x.write_to_path(&lurk_ptr_path);
      assert_eq!(x, LurkPtr::<S1>::read_from_path(&lurk_ptr_path).unwrap());
      }
    }

    proptest! {
      #[test]
      fn prop_ptr_evaluation(x in any::<PtrEvaluation<S1>>()) {
        let ser = to_z_data(&x).expect("write PtrEvaluation");
        let de: PtrEvaluation<S1> = from_z_data(&ser).expect("read PtrEvaluation");
        assert_eq!(x, de);

       let ser: Vec<u8> = bincode::serialize(&x).expect("write PtrEvalution");
       let de: PtrEvaluation<S1> = bincode::deserialize(&ser).expect("read PtrEvaluation");
       assert_eq!(x, de);

        let tmp_dir = Builder::new().prefix("tmp").tempdir().expect("tmp dir");
        let tmp_dir_path = Path::new(tmp_dir.path());
        let ptr_evaluation_path = tmp_dir_path.join("ptrevaluation.json");
      x.write_to_path(&ptr_evaluation_path);
      assert_eq!(x, PtrEvaluation::<S1>::read_from_path(&ptr_evaluation_path).unwrap());
      }
    }

    proptest! {
      #[test]
      fn prop_committed_expr(x in any::<CommittedExpression<S1>>()) {
        let ser = to_z_data(&x).expect("write CommittedExpression");
        let de: CommittedExpression<S1> = from_z_data(&ser).expect("read CommittedExpression");
        assert_eq!(x, de);

       let ser: Vec<u8> = bincode::serialize(&x).expect("write CommittedExpression");
       let de: CommittedExpression<S1> = bincode::deserialize(&ser).expect("read CommittedExpression");
        assert_eq!(x, de);

        let tmp_dir = Builder::new().prefix("tmp").tempdir().expect("tmp dir");
        let tmp_dir_path = Path::new(tmp_dir.path());
        let committed_expr_path = tmp_dir_path.join("committedexpr.json");
      x.write_to_path(&committed_expr_path);
      assert_eq!(x, CommittedExpression::<S1>::read_from_path(&committed_expr_path).unwrap());
      }
    }

    proptest! {
      #[test]
      fn prop_opening(x in any::<Opening<S1>>()) {
        let ser = to_z_data(&x).expect("write Opening");
        let de: Opening<S1> = from_z_data(&ser).expect("read Opening");
        assert_eq!(x, de);

       let ser: Vec<u8> = bincode::serialize(&x).expect("write Opening");
       let de: Opening<S1> = bincode::deserialize(&ser).expect("read Opening");
        assert_eq!(x, de);

        let tmp_dir = Builder::new().prefix("tmp").tempdir().expect("tmp dir");
        let tmp_dir_path = Path::new(tmp_dir.path());
        let opening_path = tmp_dir_path.join("opening.json");
      x.write_to_path(&opening_path);
      assert_eq!(x, Opening::<S1>::read_from_path(&opening_path).unwrap());
      }
    }

    proptest! {
      #[test]
      fn prop_claim(x in any::<Claim<S1>>()) {
        let ser = to_z_data(&x).expect("write Claim");
        let de: Claim<S1> = from_z_data(&ser).expect("read Claim");
        assert_eq!(x, de);

       let ser: Vec<u8> = bincode::serialize(&x).expect("write Claim");
       let de: Claim<S1> = bincode::deserialize(&ser).expect("read Claim");
        assert_eq!(x, de);

        let tmp_dir = Builder::new().prefix("tmp").tempdir().expect("tmp dir");
        let tmp_dir_path = Path::new(tmp_dir.path());
        let claim_path = tmp_dir_path.join("claim.json");
      x.write_to_path(&claim_path);
      assert_eq!(x, Claim::<S1>::read_from_path(&claim_path).unwrap());
      }
    }
}
