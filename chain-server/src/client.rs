//! A demo client for illustrative purposes

use halo2curves::bn256::Fr;
use std::{
    env,
    io::{stdin, stdout, Write},
    sync::Arc,
};
use tonic::Request;

use lurk::{
    cli::field_data::{de, ser, LurkData},
    lang::{Coproc, Lang},
    lem::store::Store,
    proof::{nova::C1LEM, supernova::Proof, RecursiveSNARKTrait},
    public_parameters::{
        instance::{Instance, Kind},
        supernova_public_params,
    },
};

pub mod chain_prover {
    tonic::include_proto!("chain_prover");
}

use chain_prover::{
    chain_prover_client::ChainProverClient, ChainRequest, ChainResponse, ConfigRequest,
    ConfigResponse,
};

use chain_server::ChainData;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let port = env::args().collect::<Vec<_>>()[1].parse::<u16>()?;
    let mut client = ChainProverClient::connect(format!("http://127.0.0.1:{port}")).await?;

    let ConfigResponse { rc } = client
        .config(Request::new(ConfigRequest {}))
        .await?
        .into_inner();
    let rc = usize::try_from(rc)?;

    let store = Store::<Fr>::default();

    let empty_env = store.intern_empty_env();
    let cont_outermost = store.cont_outermost();
    let cont_terminal = store.cont_terminal();

    let instance = Instance::new(
        rc,
        Arc::new(Lang::<Fr, Coproc<Fr>>::new()),
        true,
        Kind::SuperNovaAuxParams,
    );
    let pp = supernova_public_params(&instance)?;

    let (stdin, mut stdout) = (stdin(), stdout());
    let input = &mut String::new();
    loop {
        print!("> ");
        stdout.flush()?;
        input.clear();
        stdin.read_line(input)?;

        let arg_ptr = store.read_with_default_state(input)?;
        let arg = ser(LurkData::new(&arg_ptr, &store))?;
        let request = Request::new(ChainRequest { arg });
        let ChainResponse { chain_data, proof } = client.chain(request).await?.into_inner();
        let chain_data: ChainData<Fr> = de(&chain_data)?;
        let proof: Proof<Fr, C1LEM<'_, Fr, Coproc<Fr>>> = de(&proof)?;

        let (current_callable, result, next_callable) = chain_data.extract(&store)?;

        let expr_in = store.list([current_callable, arg_ptr]);
        let expr_out = store.cons(result, next_callable);

        print!(
            "{}\n↳ {}",
            expr_in.fmt_to_string_simple(&store),
            expr_out.fmt_to_string_simple(&store)
        );
        stdout.flush()?;

        let public_inputs = store.to_scalar_vector(&[expr_in, empty_env, cont_outermost]);
        let public_outputs = store.to_scalar_vector(&[expr_out, empty_env, cont_terminal]);
        if proof.verify(&pp, &public_inputs, &public_outputs)? {
            println!(" ✓");
        } else {
            println!(" ✗");
        }
    }
}
