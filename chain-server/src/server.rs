use abomonation::Abomonation;
use anyhow::Result;
use camino::Utf8PathBuf;
use clap::{Args, Parser, Subcommand};
use halo2curves::bn256::Fr;
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
    dual_channel::dummy_terminal,
    field::LurkField,
    lang::{Coproc, Lang},
    lem::{
        eval::{evaluate, make_cprocs_funcs_from_lang, make_eval_step_from_config, EvalConfig},
        pointers::{Ptr, ZPtr},
        store::Store,
        tag::Tag,
        Func,
    },
    proof::{
        nova::{CurveCycleEquipped, Dual},
        supernova::{PublicParams, SuperNovaProver},
        Prover, RecursiveSNARKTrait,
    },
    public_parameters::{instance::Instance, supernova_public_params},
    tag::ContTag,
};

pub mod chain_prover {
    #![allow(unreachable_pub)]
    tonic::include_proto!("chain_prover");
}

use chain_prover::{
    chain_prover_server::{ChainProver, ChainProverServer},
    ChainRequest, ChainResponse, ConfigRequest, ConfigResponse,
};

use chain_server::{ChainRequestData, ChainResponseData};

struct ChainProverService<'a, F: CurveCycleEquipped, C: Coprocessor<F>> {
    callable: Arc<Mutex<Ptr>>,
    store: Store<F>, // TODO: add the store to the state to allow memory cleansing
    limit: usize,
    lurk_step: Func,
    cprocs: Vec<Func>,
    prover: SuperNovaProver<'a, F, C>,
    public_params: OnceCell<PublicParams<F>>,
    session: Option<Utf8PathBuf>,
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F>> ChainProverService<'a, F, C> {
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
            store,
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
    > ChainProver for ChainProverService<'static, F, C>
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
        let call_expr = self.store.list([*callable_state, argument]);

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
                    .prove_from_frames(pp, &frames, &self.store)
                    .map_err(|e| Status::internal(e.to_string()))?;
                let proof = proof
                    .compress(pp)
                    .map_err(|e| Status::internal(e.to_string()))?;
                let proof = proof
                    .get_compressed()
                    .ok_or(Status::internal("Failed to retrieve the compressed SNARK"))?;

                // produce the data for the response
                let chain_response_data = ser(ChainResponseData::new(
                    &result,
                    &next_callable,
                    &self.store,
                    proof,
                ))
                .map_err(|e| Status::internal(e.to_string()))?;

                // save the session
                if let Some(session) = &self.session {
                    let session_data = SessionData::pack(self, &next_callable);
                    dump(session_data, session).map_err(|e| Status::internal(e.to_string()))?;
                }

                // now it's safe to set the new callable state since no error
                // has occurred so far
                *callable_state = next_callable;

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
        let rc = usize::try_into(self.prover.reduction_count())
            .map_err(|_e| Status::failed_precondition("Failed to convert rc to u32"))?;
        let callable = self
            .callable
            .lock()
            .map_err(|e| Status::aborted(e.to_string()))?;
        let callable = ser(LurkData::new(&callable, &self.store))
            .map_err(|e| Status::internal(e.to_string()))?;
        Ok(Response::new(ConfigResponse { rc, callable }))
    }
}

/// Holds data from a cached session
#[derive(Serialize, Deserialize)]
struct SessionData<F: LurkField, S> {
    callable: ZPtr<F>,
    z_store: ZStore<F>,
    limit: usize,
    lang: Lang<F, S>,
    rc: usize,
}

impl<'a, F: CurveCycleEquipped, C: Coprocessor<F>> SessionData<F, C> {
    fn pack(data: &ChainProverService<'a, F, C>, callable: &Ptr) -> Self {
        let ChainProverService {
            store,
            limit,
            prover,
            ..
        } = data;
        let (z_store, callable) = ZStore::from_store_and_ptr(store, callable);
        let limit = *limit;
        let lang = (*prover.lang().clone()).clone();
        let rc = prover.reduction_count();
        Self {
            callable,
            z_store,
            limit,
            lang,
            rc,
        }
    }

    fn unpack(self, session: Utf8PathBuf) -> Result<ChainProverService<'a, F, C>> {
        let Self {
            callable,
            z_store,
            limit,
            lang,
            rc,
        } = self;
        let (store, callable) = z_store.to_store_and_ptr(&callable)?;
        Ok(ChainProverService::new(
            callable,
            store,
            limit,
            lang,
            rc,
            Some(session),
        ))
    }
}

impl<F: LurkField, S> HasFieldModulus for SessionData<F, S> {
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
    'a,
    F: CurveCycleEquipped + DeserializeOwned,
    C: Coprocessor<F> + DeserializeOwned,
>() -> Result<(ChainProverService<'a, F, C>, SocketAddr), Box<dyn std::error::Error>> {
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
                    .fetch_f(&hash_ptr)
                    .ok_or("Failed to parse callable hash")?;
                fetch_comm(hash, &store)?;
                hash_ptr.cast(Tag::Expr(lurk::tag::ExprTag::Comm))
            } else {
                let LurkData::<F> { z_ptr, z_dag } = load(&Utf8PathBuf::from(&init_args.callable))?;
                z_dag.populate_store_simple(&z_ptr, &store)?
            };
            let svc = ChainProverService::new(
                callable,
                store,
                init_args.get_limit(),
                lang,
                init_args.get_rc(),
                init_args.session,
            );
            Ok((svc, local_ip(init_args.port)))
        }
        Command::Resume(resume_args) => {
            let session = resume_args.session;
            let session_data: SessionData<F, C> = load(&session)?;
            let svc = session_data.unpack(session)?;
            Ok((svc, local_ip(resume_args.port)))
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let (svc, addr) = get_service_and_address::<Fr, Coproc<Fr>>()?;

    Server::builder()
        .add_service(ChainProverServer::new(svc))
        .serve(addr)
        .await?;

    Ok(())
}
