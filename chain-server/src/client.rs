//! A demo client for illustrative purposes

use halo2curves::bn256::Fr;
use nova::supernova::snark::CompressedSNARK;
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
    proof::{
        nova::{Dual, E1},
        supernova::{PublicParams, SS1, SS2},
    },
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

use chain_server::{ChainRequestData, ChainResponseData};

fn verify(
    proof: &CompressedSNARK<E1<Fr>, SS1<Fr>, SS2<Fr>>,
    pp: &PublicParams<Fr>,
    z0_primary: &[Fr],
    zi_primary: &[Fr],
) -> Result<bool, Box<dyn std::error::Error>> {
    let z0_secondary = vec![Dual::<Fr>::zero()];
    let zi_secondary = &z0_secondary;
    let (zi_primary_verified, zi_secondary_verified) =
        proof.verify(&pp.pp, pp.vk(), z0_primary, &z0_secondary)?;
    Ok(zi_primary == zi_primary_verified && zi_secondary == &zi_secondary_verified)
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let port = env::args().collect::<Vec<_>>()[1].parse::<u16>()?;
    let mut client = ChainProverClient::connect(format!("http://127.0.0.1:{port}")).await?;

    let ConfigResponse { rc, callable } = client
        .config(Request::new(ConfigRequest {}))
        .await?
        .into_inner();
    let rc = usize::try_from(rc)?;

    let store = Store::<Fr>::default();
    let mut callable = de::<LurkData<Fr>>(&callable).and_then(|ld| ld.interned(&store))?;

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

        let argument = store.read_with_default_state(input)?;
        let chain_request_data = ser(ChainRequestData::new(&callable, &argument, &store))?;
        let request = Request::new(ChainRequest { chain_request_data });

        let ChainResponse {
            chain_response_data,
        } = client.chain(request).await?.into_inner();
        let chain_response_data = de::<ChainResponseData<Fr>>(&chain_response_data)?;
        let (result, next_callable) = chain_response_data.interned(&store)?;
        let proof = chain_response_data.extract_proof();

        let expr_in = store.list([callable, argument]);
        let expr_out = store.cons(result, next_callable);

        print!(
            "{}\n↳ {}",
            expr_in.fmt_to_string_simple(&store),
            expr_out.fmt_to_string_simple(&store)
        );
        stdout.flush()?;

        let public_inputs = store.to_scalar_vector(&[expr_in, empty_env, cont_outermost]);
        let public_outputs = store.to_scalar_vector(&[expr_out, empty_env, cont_terminal]);
        if verify(&proof, &pp, &public_inputs, &public_outputs)? {
            println!(" ✓");
        } else {
            println!(" ✗");
            panic!("Server's proof didn't verify!")
        }

        callable = next_callable
    }
}
