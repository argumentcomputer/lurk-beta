use log::info;
use std::convert::TryFrom;
use std::fs::File;
use std::io::{self, BufReader, BufWriter};
use std::path::Path;
use std::str::FromStr;
use std::sync::Arc;

use crate::coprocessor::Coprocessor;
use crate::{
    circuit::ToInputs,
    eval::{
        empty_sym_env,
        lang::{Coproc, Lang},
        Evaluable, Evaluator, Status, Witness, IO,
    },
    field::LurkField,
    proof::nova::{self, NovaProver, PublicParams},
    proof::Prover,
    ptr::{ContPtr, Ptr, ScalarPtr},
    scalar_store::ScalarStore,
    store::Store,
    tag::ExprTag,
    writer::Write,
};
use ff::PrimeField;
use hex::FromHex;
use libipld::{
    cbor::DagCborCodec,
    json::DagJsonCodec,
    multihash::{Code, MultihashDigest},
    prelude::Codec,
    serde::{from_ipld, to_ipld},
    Cid, Ipld,
};
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

pub type NovaProofCache = FileMap<Cid, Proof<'static, S1>>;
pub fn nova_proof_cache(reduction_count: usize) -> NovaProofCache {
    FileMap::<Cid, Proof<'_, S1>>::new(format!("nova_proofs.{}", reduction_count)).unwrap()
}

pub type CommittedExpressionMap = FileMap<Commitment<S1>, CommittedExpression<S1>>;
pub fn committed_expression_store() -> CommittedExpressionMap {
    FileMap::<Commitment<S1>, CommittedExpression<S1>>::new("committed_expressions").unwrap()
}

pub fn public_params<C, B, T>(rc: usize, quick: bool, lang: Arc<Lang<S1, C>>, bind: B) -> T
where
    C: Coprocessor<S1> + Serialize + DeserializeOwned + 'static,
    B: Fn(PublicParams<'static, C>) -> T,
{
    let f = |lang: Arc<Lang<S1, C>>| Arc::new(nova::public_params(rc, lang));
    registry::CACHE_REG.get_coprocessor_or_update_with(rc, quick, f, lang)
}

pub fn with_public_params<
    C: Coprocessor<S1> + Serialize + DeserializeOwned + 'static,
    T,
    F: FnOnce(&PublicParams<'static, C>) -> T,
>(
    rc: usize,
    lang: Arc<Lang<S1, C>>,
    f: F,
) {
}

pub fn public_params_quick<C: Coprocessor<S1> + Serialize + DeserializeOwned + 'static>(
    rc: usize,
    lang: Arc<Lang<S1, C>>,
) -> Result<PublicParams<'static, C>, Error> {
    let disk_cache = file_map::FileIndex::new("public_params").unwrap();
    // use the cached language key
    let lang_key = lang.key();
    // Sanity-check: we're about to use a lang-dependent disk cache, which should be specialized
    // for this lang/coprocessor.
    let key = format!("public-params-rc-{rc}-coproc-{lang_key}-quick");
    if let Some(mut bytes) =
        disk_cache.get_with_timing::<Vec<u8>>(&key, &"public params".to_string())
    {
        let (_, remaining) =
            unsafe { abomonation::decode::<PublicParams<'static, C>>(bytes.as_mut()).unwrap() };
        assert!(remaining.len() == 0);
        let pp = std::mem::ManuallyDrop::new(bytes);
        // this is extremely dangerous
        let pp = unsafe { std::mem::transmute_copy(&pp) };
        Ok(pp)
    } else {
        let pp = nova::public_params(rc, lang);
        let mut bytes = Vec::new();
        unsafe { abomonation::encode(&pp, &mut bytes)? };
        // maybe just directly write
        disk_cache
            .set_with_timing::<Vec<u8>>(&key, &bytes, &"public params".to_string())
            .map_err(|e| Error::CacheError(format!("Disk write error: {e}")))?;
        Ok(pp)
    }
}

// Number of circuit reductions per step, equivalent to `chunk_frame_count`
#[derive(Clone, Copy, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReductionCount {
    One,
    Five,
    Ten,
    OneHundred,
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

#[derive(Serialize, Deserialize, Clone, Debug, Default, PartialEq, Eq)]
pub struct PtrEvaluation {
    pub expr: LurkPtr,
    pub env: LurkPtr,
    pub cont: LurkCont,
    pub expr_out: LurkPtr,
    pub env_out: LurkPtr,
    pub cont_out: LurkCont,
    pub status: Status,
    pub iterations: Option<usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Commitment<F: LurkField> {
    pub comm: F,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct OpeningRequest<F: LurkField> {
    pub commitment: Commitment<F>,
    pub input: Expression,
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
pub struct Expression {
    pub expr: LurkPtr,
}

#[derive(Debug, Serialize, Deserialize, Clone, Eq, PartialEq)]
pub struct Opening<F: LurkField> {
    pub input: String,
    pub output: String,
    pub status: Status,
    pub commitment: Commitment<F>,
    pub new_commitment: Option<Commitment<F>>,
}

#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq)]
pub struct LurkScalarBytes {
    #[serde(with = "base64")]
    scalar_store: Vec<u8>,
    #[serde(with = "base64")]
    scalar_ptr: Vec<u8>, // can also be a scalar_cont_ptr
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct LurkScalarIpld {
    scalar_store: Ipld,
    scalar_ptr: Ipld,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub enum LurkPtr {
    Source(String),
    ScalarBytes(LurkScalarBytes),
    Ipld(LurkScalarIpld),
}

#[derive(Serialize, Deserialize, Clone, Debug, Default, PartialEq, Eq)]
pub enum LurkCont {
    #[default]
    Outermost,
    Terminal,
    Error,
}

impl Default for LurkPtr {
    fn default() -> Self {
        Self::Source("NIL".to_string())
    }
}

impl Eq for LurkPtr {}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct CommittedExpression<F: LurkField + Serialize> {
    pub expr: LurkPtr,
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

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum Claim<F: LurkField> {
    Evaluation(Evaluation),
    PtrEvaluation(PtrEvaluation),
    Opening(Opening<F>),
}

// This is just a rough idea, mostly here so we can plumb it elsewhere. The idea is that a verifier can sign an
// attestation that a given claim's proof was verified. It motivates the use of an online verifier for demo purposes.
// Although real proofs should be fast to verify, they will still be large relative to a small (auditable) bundle like
// this. Even if not entirely realistic, something with this general *shape* is likely to play a role in a recursive
// system where the ability to aggregate proof verification more soundly is possible.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct Cert {
    #[serde(serialize_with = "cid_string", deserialize_with = "string_cid")]
    pub claim_cid: Cid,
    #[serde(serialize_with = "cid_string", deserialize_with = "string_cid")]
    pub proof_cid: Cid,
    pub verified: bool,
    pub verifier_id: String,
    pub signature: String,
}

fn cid_string<S>(c: &Cid, s: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    s.serialize_str(&c.to_string())
}

pub fn string_cid<'de, D>(d: D) -> Result<Cid, D::Error>
where
    D: Deserializer<'de>,
{
    use serde::de::Error;

    let string = String::deserialize(d)?;

    Cid::from_str(&string).map_err(|e| D::Error::custom(e.to_string()))
}

pub fn cid_from_string(s: &str) -> Result<Cid, libipld::cid::Error> {
    Cid::from_str(s)
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
    pub fn ptr_evaluation(&self) -> Option<PtrEvaluation> {
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

pub trait Id
where
    Self: Sized,
{
    fn id(&self) -> String;
    fn cid(&self) -> Cid;
    fn has_id(&self, id: String) -> bool;
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
    for<'de> T: Deserialize<'de>, // + Decode<DagJsonCodec>,
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

        let (output, iterations, _) = evaluator.eval().map_err(|_| Error::EvaluationFailure)?;

        Ok(Self::new(store, input, output, Some(iterations)))
    }
}

impl PtrEvaluation {
    fn new<F: LurkField + Serialize>(
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
    pub fn from_comm(s: &mut Store<F>, ptr: &Ptr<F>) -> Self {
        let digest = *s.hash_expr(ptr).expect("couldn't hash ptr").value();

        assert_eq!(ExprTag::Comm, ptr.tag);

        Commitment { comm: digest }
    }

    pub fn ptr(&self, s: &mut Store<F>) -> Ptr<F> {
        s.intern_opaque_comm(self.comm)
    }

    pub fn from_ptr_with_hiding(s: &mut Store<F>, ptr: &Ptr<F>) -> (Self, F) {
        let secret = F::random(OsRng);

        let commitment = Self::from_ptr_and_secret(s, ptr, secret);

        (commitment, secret)
    }

    pub fn from_ptr_and_secret(s: &mut Store<F>, ptr: &Ptr<F>, secret: F) -> Self {
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

        let commitment = Self::from_ptr_and_secret(s, &fun_ptr, secret);

        let open = s.sym("open");
        let comm_ptr = s.hide(secret, fun_ptr);

        // (open <commitment>)
        let fun_expr = s.list(&[open, comm_ptr]);

        // ((open <commitment>) input)
        let expression = s.list(&[fun_expr, input]);

        Ok((commitment, expression))
    }

    fn fun_application(&self, s: &mut Store<F>, input: Ptr<F>) -> Ptr<F> {
        let open = s.sym("open");
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

impl LurkPtr {
    pub fn ptr<F: LurkField + Serialize + DeserializeOwned>(
        &self,
        s: &mut Store<F>,
        limit: usize,
        lang: &Lang<F, Coproc<F>>,
    ) -> Ptr<F> {
        match self {
            LurkPtr::Source(source) => {
                let ptr = s.read(source).expect("could not read source");
                let (out, _) = evaluate(s, ptr, None, limit, lang).unwrap();

                out.expr
            }
            LurkPtr::ScalarBytes(lurk_scalar_bytes) => {
                let scalar_store: Ipld = DagCborCodec
                    .decode(&lurk_scalar_bytes.scalar_store)
                    .expect("could not read opaque scalar store");
                let scalar_ptr: Ipld = DagCborCodec
                    .decode(&lurk_scalar_bytes.scalar_ptr)
                    .expect("could not read opaque scalar ptr");

                let lurk_ptr = LurkPtr::Ipld(LurkScalarIpld {
                    scalar_store,
                    scalar_ptr,
                });

                lurk_ptr.ptr(s, limit, lang)
            }
            LurkPtr::Ipld(lurk_scalar_ipld) => {
                // FIXME: put the scalar_store in a new field for the store.
                let fun_scalar_store: ScalarStore<F> =
                    from_ipld(lurk_scalar_ipld.scalar_store.clone()).unwrap();
                let fun_scalar_ptr: ScalarPtr<F> =
                    from_ipld(lurk_scalar_ipld.scalar_ptr.clone()).unwrap();
                s.intern_scalar_ptr(fun_scalar_ptr, &fun_scalar_store)
                    .expect("failed to intern scalar_ptr for fun")
            }
        }
    }

    pub fn from_ptr<F: LurkField + Serialize>(s: &mut Store<F>, ptr: &Ptr<F>) -> Self {
        let (scalar_store, scalar_ptr) = ScalarStore::new_with_expr(s, ptr);
        let scalar_ptr = scalar_ptr.unwrap();

        let scalar_store_ipld = to_ipld(scalar_store).unwrap();
        let new_fun_ipld = to_ipld(scalar_ptr).unwrap();

        let scalar_store_bytes = DagCborCodec.encode(&scalar_store_ipld).unwrap();
        let new_fun_bytes = DagCborCodec.encode(&new_fun_ipld).unwrap();

        let again = from_ipld(new_fun_ipld).unwrap();
        assert_eq!(&scalar_ptr, &again);

        Self::ScalarBytes(LurkScalarBytes {
            scalar_store: scalar_store_bytes,
            scalar_ptr: new_fun_bytes,
        })
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

impl Expression {
    pub fn eval<F: LurkField + Serialize + DeserializeOwned>(
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
            let new_secret = *s.get_expr_hash(&new_secret0).expect("hash missing").value();

            let (_, new_fun) = s.open(new_comm).expect("opening missing");
            let new_commitment = Commitment::from_comm(s, &new_comm);

            s.hydrate_scalar_cache();

            let expr = LurkPtr::from_ptr(s, &new_fun);

            let new_function = CommittedExpression::<S1> {
                expr,
                secret: Some(new_secret),
                commitment: Some(new_commitment),
            };

            let function_map = committed_expression_store();
            function_map.set(new_commitment, &new_function)?;

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

        let cid = claim.cid();

        if let Some(proof) = proof_map.get(&cid) {
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
                    return Err(Error::EvaluationFailure);
                };
            }
            Claim::PtrEvaluation(e) => {
                if e.status != Status::Terminal {
                    return Err(Error::EvaluationFailure);
                }
            }
        };

        proof.verify(pp, &lang).expect("Nova verification failed");

        proof_map.set(cid, &proof).unwrap();

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

    let (io, iterations, _) = evaluator.eval().map_err(|_| Error::EvaluationFailure)?;

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

    #[test]
    fn test_cert_serialization() {
        use serde_json::json;

        let c = Commitment {
            comm: S1::from(123),
        };

        let cid = c.cid();
        let cert = Cert {
            claim_cid: cid,
            proof_cid: cid,
            verified: true,
            verifier_id: "asdf".to_string(),
            signature: "fdsa".to_string(),
        };
        let json = json!(cert);

        let string = json.to_string();

        let cert_again: Cert = serde_json::from_str(&string).unwrap();
        assert_eq!(cert, cert_again);
    }
}
