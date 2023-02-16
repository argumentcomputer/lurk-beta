use std::io;
use std::path::{Path, PathBuf};
use clap::{AppSettings, Args, Parser, Subcommand};
use clap_verbosity_flag::{Verbosity, WarnLevel};
use lurk::{field::LurkField, proof::nova::public_params};
use serde_json;
use serde::{Deserialize, Serialize};
use log::info;

use lurk_verify::{LurkProof, VerifyError, S1};

#[derive(Parser, Debug)]
#[clap(version, about, long_about = None)]
#[clap(global_setting(AppSettings::DeriveDisplayOrder))]
struct Cli {
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
    /// Verifies a proof
    Verify(Verify),
}

#[derive(Args, Debug)]
struct Verify {
    /// Path to proof input
    #[clap(short, long, value_parser)]
    proof: PathBuf,
}

impl Verify {
    fn verify(&self, cli_error: bool) -> Result<(), VerifyError> {
        let proof = LurkProof::<S1>::read_from_path(&self.proof)?;
        let pp = public_params(proof.reduction_count.count());
        let result = proof.verify(&pp)?;

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

// Get proof from supplied path or else from stdin.
//fn proof<'a, P: AsRef<Path>, F: LurkField>(proof_path: Option<P>) -> Result<LurkProof<'a, F>, VerifyError>
//where
//    F: Serialize + for<'de> Deserialize<'de>,
//{
//    match proof_path {
//        Some(path) => LurkProof::<S1>::read_from_path::<S1>(path),
//        None => LurkProof::<S1>::read_from_stdin::<S1>(),
//    }
//}

fn main() -> Result<(), VerifyError> {
    let cli = Cli::parse();
    pretty_env_logger::formatted_builder()
        .filter_level(cli.verbose.log_level_filter())
        .init();
    match &cli.command {
        Command::Verify(v) => v.verify(cli.error),
    }
}
