use abomonation::Abomonation;
use anyhow::Result;
use camino::Utf8PathBuf;
use clap::{Args, Parser, Subcommand};
use halo2curves::bn256::Fr;
use nova::supernova::RecursiveSNARK;
use once_cell::sync::OnceCell;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::{
    net::{Ipv4Addr, SocketAddr, SocketAddrV4},
    sync::{Arc, Mutex},
};
use tonic::{transport::Server, Request, Response, Status};

use lurk::{
    cli::{
        field_data::{de, dump, load, ser, HasFieldModulus, LurkData},
        repl::fetch_comm,
        zstore::ZStore,
    },
    coprocessor::Coprocessor,
    dual_channel::{dummy_terminal, pair_terminals},
    lang::{Coproc, Lang},
    lem::{
        eval::{
            evaluate, make_cprocs_funcs_from_lang, make_eval_step_from_config, resume_stream,
            start_stream, EvalConfig,
        },
        pointers::{Ptr, ZPtr},
        store::Store,
        tag::Tag,
        Func,
    },
    proof::{
        nova::{CurveCycleEquipped, Dual, E1},
        supernova::{PublicParams, SuperNovaProver},
        Prover, RecursiveSNARKTrait,
    },
    public_parameters::{instance::Instance, supernova_public_params},
    tag::ContTag,
};

pub mod chain_prover {
    #![allow(unreachable_pub)]
    #![allow(clippy::derive_partial_eq_without_eq)]
    tonic::include_proto!("chain_prover");
}

use chain_prover::{
    chain_prover_server::{ChainProver, ChainProverServer},
    ChainRequest, ChainResponse, ConfigRequest, ConfigResponse,
};

use chain_server::{ChainRequestData, ChainResponseData, ConfigResponseData};

struct StandaloneService<F: CurveCycleEquipped, C: Coprocessor<F>> {
    callable: Arc<Mutex<Ptr>>,
    store: Arc<Store<F>>, // TODO: add the store to the state to allow memory cleansing
    limit: usize,
    lurk_step: Func,
    cprocs: Vec<Func>,
    prover: SuperNovaProver<F, C>,
    public_params: OnceCell<PublicParams<F>>,
    session: Option<Utf8PathBuf>,
}

impl<F: CurveCycleEquipped, C: Coprocessor<F>> StandaloneService<F, C> {
    fn new(
        callable: Ptr,
        store: Store<F>,
        limit: usize,
        lang: Lang<F, C>,
        rc: usize,
        session: Option<Utf8PathBuf>,
    ) -> Self {
        let eval_config = EvalConfig::new_nivc(&lang);
        let lurk_step = make_eval_step_from_config(&eval_config);
        let cprocs = make_cprocs_funcs_from_lang(&lang);
        let prover = SuperNovaProver::<_, C>::new(rc, Arc::new(lang));
        Self {
            callable: Arc::new(Mutex::new(callable)),
            store: Arc::new(store),
            limit,
            lurk_step,
            cprocs,
            prover,
            public_params: OnceCell::new(),
            session,
        }
    }
}

#[tonic::async_trait]
impl<
        F: CurveCycleEquipped + DeserializeOwned + Serialize,
        C: Coprocessor<F> + Serialize + DeserializeOwned + 'static,
    > ChainProver for StandaloneService<F, C>
where
    <F as ff::PrimeField>::Repr: Abomonation,
    <Dual<F> as ff::PrimeField>::Repr: Abomonation,
{
    async fn chain(
        &self,
        request: Request<ChainRequest>,
    ) -> Result<Response<ChainResponse>, Status> {
        // deserialize and intern the provided callable state and argument
        let ChainRequest { chain_request_data } = request.into_inner();
        let (callable, argument) = de::<ChainRequestData<F>>(&chain_request_data)
            .and_then(|d| d.interned(&self.store))
            .map_err(|e| Status::invalid_argument(e.to_string()))?;

        // retrieve callable state
        let mut callable_state = self
            .callable
            .lock()
            .map_err(|e| Status::aborted(e.to_string()))?;

        if !self.store.ptr_eq(&callable, &callable_state) {
            return Err(Status::invalid_argument("Invalid callable state provided"));
        }

        // assemble call expression
        let call_expr = self.store.list([callable, argument]);

        // evaluate to produce the frames
        let frames = evaluate(
            Some((&self.lurk_step, &self.cprocs, self.prover.lang())),
            call_expr,
            &self.store,
            self.limit,
            &dummy_terminal(),
        )
        .map_err(|e| Status::data_loss(e.to_string()))?;

        // retrieve the result of the call
        let Some((Some(expr_out), Some(cont_out))) = frames
            .last()
            .map(|frame| (frame.output.first(), frame.output.last()))
        else {
            return Err(Status::internal("Failed to get the evaluation result"));
        };

        // make sure that the evaluation terminated appropriatelly
        match cont_out.tag() {
            Tag::Cont(ContTag::Terminal) => {
                // get the car/cdr of the result to retrieve the chain result and
                // the next callable
                let (result, next_callable) = self.store.fetch_cons(expr_out).ok_or_else(|| {
                    Status::failed_precondition("Call didn't result in a cons expression")
                })?;

                // retrieve (or compute if needed) the public params for proving
                let pp = self
                    .public_params
                    .get_or_try_init(|| {
                        supernova_public_params(&Instance::new_supernova(&self.prover, true))
                    })
                    .map_err(|e| Status::internal(e.to_string()))?;

                // prove then compress the proof
                let (proof, ..) = self
                    .prover
                    .prove_from_frames(pp, &frames, &self.store, None)
                    .map_err(|e| Status::internal(e.to_string()))?;
                let compressed_proof = proof
                    .compress(pp)
                    .map_err(|e| Status::internal(e.to_string()))?;
                // the above compression operated on a recursive proof, so the following `into_owned()` should
                // not involve cloning
                let compressed_proof = compressed_proof
                    .into_owned()
                    .get_compressed()
                    .ok_or(Status::internal("Failed to retrieve the compressed SNARK"))?;

                // produce the data for the response
                let chain_response_data = ser(ChainResponseData::new(
                    result,
                    next_callable,
                    &self.store,
                    compressed_proof,
                ))
                .map_err(|e| Status::internal(e.to_string()))?;

                // save the session
                if let Some(session) = &self.session {
                    let session_data = SessionData::pack_standalone(self, next_callable);
                    dump(session_data, session).map_err(|e| Status::internal(e.to_string()))?;
                }

                // now it's safe to set the new callable state since no error
                // has occurred so far
                *callable_state = *next_callable;

                Ok(Response::new(ChainResponse {
                    chain_response_data,
                }))
            }
            Tag::Cont(ContTag::Error) => Err(Status::invalid_argument("Evaluation error")),
            Tag::Cont(_) => Err(Status::resource_exhausted("Unfinished evaluation")),
            _ => Err(Status::internal("Invalid continuation tag")),
        }
    }

    async fn config(&self, _: Request<ConfigRequest>) -> Result<Response<ConfigResponse>, Status> {
        let callable = self
            .callable
            .lock()
            .map_err(|e| Status::aborted(e.to_string()))?;
        let config_response_data = ser(ConfigResponseData::new(
            self.prover.reduction_count(),
            &callable,
            None,
            &self.store,
        ))
        .map_err(|e| Status::internal(e.to_string()))?;
        Ok(Response::new(ConfigResponse {
            config_response_data,
        }))
    }
}

struct StreamState<F: CurveCycleEquipped> {
    callable: Ptr,
    result_and_proof: Option<(Ptr, RecursiveSNARK<E1<F>>)>,
}

struct StreamService<F: CurveCycleEquipped, C: Coprocessor<F>> {
    state: Arc<Mutex<StreamState<F>>>,
    first_callable: Ptr,
    store: Arc<Store<F>>, // TODO: add the store to the state to allow memory cleansing
    limit: usize,
    lurk_step: Func,
    cprocs: Vec<Func>,
    prover: SuperNovaProver<F, C>,
    public_params: OnceCell<PublicParams<F>>,
    session: Option<Utf8PathBuf>,
}

impl<F: CurveCycleEquipped, C: Coprocessor<F>> StreamService<F, C> {
    fn new(
        callable: Ptr,
        first_callable: Ptr,
        result_and_proof: Option<(Ptr, RecursiveSNARK<E1<F>>)>,
        store: Store<F>,
        limit: usize,
        lang: Lang<F, C>,
        rc: usize,
        session: Option<Utf8PathBuf>,
    ) -> Self {
        let eval_config = EvalConfig::new_nivc(&lang);
        let lurk_step = make_eval_step_from_config(&eval_config);
        let cprocs = make_cprocs_funcs_from_lang(&lang);
        let prover = SuperNovaProver::<_, C>::new(rc, Arc::new(lang));
        Self {
            state: Arc::new(Mutex::new(StreamState {
                callable,
                result_and_proof,
            })),
            first_callable,
            store: Arc::new(store),
            limit,
            lurk_step,
            cprocs,
            prover,
            public_params: OnceCell::new(),
            session,
        }
    }
}

#[tonic::async_trait]
impl<
        F: CurveCycleEquipped + DeserializeOwned + Serialize,
        C: Coprocessor<F> + Serialize + DeserializeOwned + 'static,
    > ChainProver for StreamService<F, C>
where
    <F as ff::PrimeField>::Repr: Abomonation,
    <Dual<F> as ff::PrimeField>::Repr: Abomonation,
{
    async fn chain(
        &self,
        request: Request<ChainRequest>,
    ) -> Result<Response<ChainResponse>, Status> {
        // deserialize and intern the provided callable state and argument
        let ChainRequest { chain_request_data } = request.into_inner();
        let (callable, argument) = de::<ChainRequestData<F>>(&chain_request_data)
            .and_then(|d| d.interned(&self.store))
            .map_err(|e| Status::invalid_argument(e.to_string()))?;

        // retrieve callable state
        let mut state = self
            .state
            .lock()
            .map_err(|e| Status::aborted(e.to_string()))?;

        if !self.store.ptr_eq(&callable, &state.callable) {
            return Err(Status::invalid_argument("Invalid callable state provided"));
        }

        let (t1, t2) = pair_terminals();
        let lang_setup: Option<(_, &[_], &Lang<_, _>)> =
            Some((&self.lurk_step, &self.cprocs, self.prover.lang()));

        let frames = if let Some((result, _)) = &state.result_and_proof {
            // got a previous result we can use to resume the stream
            t2.send(self.store.intern_nil())
                .map_err(|e| Status::internal(e.to_string()))?;
            t2.send(argument)
                .map_err(|e| Status::internal(e.to_string()))?;
            let input = vec![
                self.store.cons(*result, callable),
                self.store.intern_empty_env(),
                self.store.cont_stream_pause(),
            ];
            resume_stream(lang_setup, input, &self.store, self.limit, &t1)
        } else {
            // no previous result so we start the stream
            t2.send(argument)
                .map_err(|e| Status::internal(e.to_string()))?;
            start_stream(lang_setup, callable, &self.store, self.limit, &t1)
        }
        .map_err(|e| Status::data_loss(e.to_string()))?;

        // retrieve the result of the call
        let Some((Some(expr_out), Some(cont_out))) = frames
            .last()
            .map(|frame| (frame.output.first(), frame.output.last()))
        else {
            return Err(Status::internal("Failed to get the evaluation result"));
        };

        // make sure that the evaluation terminated appropriatelly
        match cont_out.tag() {
            Tag::Cont(ContTag::StreamPause) => {
                // get the car/cdr of the result to retrieve the chain result and
                // the next callable
                let (result, next_callable) = self.store.fetch_cons(expr_out).ok_or_else(|| {
                    Status::failed_precondition("Call didn't result in a cons expression")
                })?;

                // retrieve (or compute if needed) the public params for proving
                let pp = self
                    .public_params
                    .get_or_try_init(|| {
                        supernova_public_params(&Instance::new_supernova(&self.prover, true))
                    })
                    .map_err(|e| Status::internal(e.to_string()))?;

                let previous_proof = state
                    .result_and_proof
                    .as_ref()
                    .map(|(_, proof)| proof.clone());

                // prove then compress the proof
                let (proof, ..) = self
                    .prover
                    .prove_from_frames(pp, &frames, &self.store, previous_proof)
                    .map_err(|e| Status::internal(e.to_string()))?;
                let compressed_proof = proof
                    .compress(pp)
                    .map_err(|e| Status::internal(e.to_string()))?;
                // the above compression operated on a recursive proof, so the following `into_owned()` should
                // not involve cloning
                let compressed_proof = compressed_proof
                    .into_owned()
                    .get_compressed()
                    .ok_or(Status::internal("Failed to retrieve the compressed SNARK"))?;

                let Some(recursive_proof) = proof.get_recursive() else {
                    return Err(Status::internal("Not a recursive proof"));
                };

                // produce the data for the response
                let chain_response_data = ser(ChainResponseData::new(
                    result,
                    next_callable,
                    &self.store,
                    compressed_proof,
                ))
                .map_err(|e| Status::internal(e.to_string()))?;

                // save the session
                if let Some(session) = &self.session {
                    let session_data = SessionData::pack_stream(
                        self,
                        next_callable,
                        Some((result, recursive_proof.clone())),
                    );
                    dump(session_data, session).map_err(|e| Status::internal(e.to_string()))?;
                }

                // now it's safe to set the new state since no error has occurred so far
                *state = StreamState {
                    callable: *next_callable,
                    result_and_proof: Some((*result, recursive_proof)),
                };

                Ok(Response::new(ChainResponse {
                    chain_response_data,
                }))
            }
            Tag::Cont(ContTag::Error) => Err(Status::invalid_argument("Evaluation error")),
            Tag::Cont(_) => Err(Status::resource_exhausted("Unfinished evaluation")),
            _ => Err(Status::internal("Invalid continuation tag")),
        }
    }

    async fn config(&self, _: Request<ConfigRequest>) -> Result<Response<ConfigResponse>, Status> {
        let state = self
            .state
            .lock()
            .map_err(|e| Status::aborted(e.to_string()))?;
        let config_response_data = ser(ConfigResponseData::new(
            self.prover.reduction_count(),
            &state.callable,
            Some(&self.first_callable),
            &self.store,
        ))
        .map_err(|e| Status::internal(e.to_string()))?;
        Ok(Response::new(ConfigResponse {
            config_response_data,
        }))
    }
}

#[derive(Serialize, Deserialize)]
struct StreamSessionData<F: CurveCycleEquipped> {
    first_callable: ZPtr<F>,
    result_and_proof: Option<(ZPtr<F>, RecursiveSNARK<E1<F>>)>,
}

/// Holds data from a cached session
#[derive(Serialize, Deserialize)]
struct SessionData<F: CurveCycleEquipped, S> {
    callable: ZPtr<F>,
    stream_session_data: Option<StreamSessionData<F>>,
    z_store: ZStore<F>,
    limit: usize,
    lang: Lang<F, S>,
    rc: usize,
}

enum ServiceWrapper<F: CurveCycleEquipped, C: Coprocessor<F>> {
    Standalone(StandaloneService<F, C>),
    Stream(StreamService<F, C>),
}

impl<F: CurveCycleEquipped, C: Coprocessor<F>> SessionData<F, C> {
    fn pack_standalone(svc: &StandaloneService<F, C>, callable: &Ptr) -> Self {
        let StandaloneService {
            store,
            limit,
            prover,
            ..
        } = svc;
        let (z_store, callable, _) = ZStore::from_store_and_ptr(store, callable);
        let limit = *limit;
        let lang = (*prover.lang().clone()).clone();
        let rc = prover.reduction_count();
        Self {
            callable,
            stream_session_data: None,
            z_store,
            limit,
            lang,
            rc,
        }
    }

    fn pack_stream(
        svc: &StreamService<F, C>,
        callable: &Ptr,
        result_and_proof: Option<(&Ptr, RecursiveSNARK<E1<F>>)>,
    ) -> Self {
        let StreamService {
            first_callable,
            store,
            limit,
            prover,
            ..
        } = svc;
        let (mut z_store, callable, mut cache) = ZStore::from_store_and_ptr(store, callable);
        let first_callable = z_store.populate_with(first_callable, store, &mut cache);
        let result_and_proof = result_and_proof
            .map(|(result, proof)| (z_store.populate_with(result, store, &mut cache), proof));
        let stream_session_data = Some(StreamSessionData {
            first_callable,
            result_and_proof,
        });
        let limit = *limit;
        let lang = (*prover.lang().clone()).clone();
        let rc = prover.reduction_count();
        Self {
            callable,
            stream_session_data,
            z_store,
            limit,
            lang,
            rc,
        }
    }

    fn unpack(self, session: Utf8PathBuf) -> Result<ServiceWrapper<F, C>> {
        let Self {
            callable,
            stream_session_data,
            z_store,
            limit,
            lang,
            rc,
        } = self;
        let (store, callable, mut cache) = z_store.to_store_and_ptr(&callable)?;
        if let Some(StreamSessionData {
            first_callable,
            result_and_proof,
        }) = stream_session_data
        {
            let first_callable = z_store.populate_store(&first_callable, &store, &mut cache)?;
            let result_and_proof = if let Some((result, proof)) = result_and_proof {
                Some((z_store.populate_store(&result, &store, &mut cache)?, proof))
            } else {
                None
            };
            Ok(ServiceWrapper::Stream(StreamService::new(
                callable,
                first_callable,
                result_and_proof,
                store,
                limit,
                lang,
                rc,
                Some(session),
            )))
        } else {
            Ok(ServiceWrapper::Standalone(StandaloneService::new(
                callable,
                store,
                limit,
                lang,
                rc,
                Some(session),
            )))
        }
    }
}

impl<F: CurveCycleEquipped, S> HasFieldModulus for SessionData<F, S> {
    fn field_modulus() -> String {
        F::MODULUS.to_string()
    }
}

/// An RPC server built on top of Lurk to create SNARKs of chaining callable
/// objects
///
/// A callable object is one of the following:
/// * A function
/// * A commitment to a function
/// * An expression that reduces to one of the above
///
/// Further, a callable object that can be chained, once called appropriatelly,
/// must return a pair whose second component is the next callable object (the
/// first component is application specific)
#[derive(Parser, Debug)]
#[clap(version)]
struct Cli {
    #[clap(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Initiates the server with fresh state and configurations
    Init(InitArgs),
    /// Starts the server by resuming a previously cached session
    Resume(ResumeArgs),
}

#[derive(Args, Debug)]
struct InitArgs {
    /// Callable state: either a commitment hash or a path to a Lurk data file
    #[clap(value_parser)]
    callable: String,

    /// Flag to start the server in stream mode
    #[arg(long)]
    stream: bool,

    /// Flag to use a persisted commitment as the callable state
    #[arg(long)]
    comm: bool,

    /// Port to listen to
    #[clap(long, value_parser)]
    port: u16,

    /// Reduction count used for proofs (defaults to 10)
    #[clap(long, value_parser)]
    rc: Option<usize>,

    /// Iterations allowed (defaults to 100_000_000; rounded up to the next multiple of rc)
    #[clap(long, value_parser)]
    limit: Option<usize>,

    #[clap(long, value_parser)]
    /// Path to the file where the session will be cached
    session: Option<Utf8PathBuf>,
}

impl InitArgs {
    #[inline]
    fn get_rc(&self) -> usize {
        self.rc.unwrap_or(10)
    }

    #[inline]
    fn get_limit(&self) -> usize {
        self.limit.unwrap_or(100_000_000)
    }
}

#[derive(Args, Debug)]
struct ResumeArgs {
    /// Path to the file contained the cached session
    #[clap(value_parser)]
    session: Utf8PathBuf,

    /// Port to listen to
    #[clap(long, value_parser)]
    port: u16,
}

fn get_service_and_address<
    F: CurveCycleEquipped + DeserializeOwned,
    C: Coprocessor<F> + DeserializeOwned,
>() -> Result<(ServiceWrapper<F, C>, SocketAddr), Box<dyn std::error::Error>> {
    let Cli { command } = Cli::parse();
    let local_ip = |port| SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), port));
    match command {
        Command::Init(init_args) => {
            // TODO: get lang from `init_args`
            let lang = Lang::<F, C>::new();
            let store = Store::<F>::default();
            let callable = if init_args.comm {
                let hash_ptr = store.read_with_default_state(&init_args.callable)?;
                let hash = store
                    .fetch_f_by_val(hash_ptr.val())
                    .ok_or("Failed to parse callable hash")?;
                fetch_comm(hash, &store)?;
                hash_ptr.cast(Tag::Expr(lurk::tag::ExprTag::Comm))
            } else {
                let LurkData::<F> { z_ptr, z_dag } = load(&Utf8PathBuf::from(&init_args.callable))?;
                z_dag.populate_store_simple(&z_ptr, &store)?
            };
            let svc = if init_args.stream {
                ServiceWrapper::Stream(StreamService::new(
                    callable,
                    callable,
                    None,
                    store,
                    init_args.get_limit(),
                    lang,
                    init_args.get_rc(),
                    init_args.session,
                ))
            } else {
                ServiceWrapper::Standalone(StandaloneService::new(
                    callable,
                    store,
                    init_args.get_limit(),
                    lang,
                    init_args.get_rc(),
                    init_args.session,
                ))
            };
            Ok((svc, local_ip(init_args.port)))
        }
        Command::Resume(resume_args) => {
            let session = resume_args.session;
            let svc = load::<SessionData<F, C>>(&session).and_then(|sd| sd.unpack(session))?;
            Ok((svc, local_ip(resume_args.port)))
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let (svc, addr) = get_service_and_address::<Fr, Coproc<Fr>>()?;
    macro_rules! serve {
        ($svc:expr) => {
            Server::builder()
                .add_service(ChainProverServer::new($svc))
                .serve(addr)
                .await?
        };
    }
    match svc {
        ServiceWrapper::Standalone(svc) => serve!(svc),
        ServiceWrapper::Stream(svc) => serve!(svc),
    }

    Ok(())
}
