use clap::Parser;
use clap_verbosity_flag::{Verbosity, WarnLevel};
use log::{error, info};
use lurk::proof::nova::public_params;
use std::io;
use std::path::PathBuf;

use lurk_verify::{LurkProof, VerifyError, S1};

#[derive(Parser, Debug)]
#[clap(version, about, long_about = None)]
struct Cli {
    /// Be verbose
    #[clap(flatten)]
    verbose: Verbosity<WarnLevel>,

    /// Path to proof to be verified
    #[clap(short, long)]
    proof: PathBuf,
}

impl Cli {
    fn verify(&self) -> Result<(), VerifyError> {
        let proof = LurkProof::<S1>::read_from_path(&self.proof)?;
        let pp = public_params(proof.reduction_count.count());
        let result = proof.verify(&pp)?;

        serde_json::to_writer(io::stdout(), &result)?;

        if result.verified {
            info!("Verification succeeded");
        } else {
            error!("Verification failed");
        };

        Ok(())
    }
}

fn main() -> Result<(), VerifyError> {
    let cli = Cli::parse();
    env_logger::Builder::new()
        .filter_level(cli.verbose.log_level_filter())
        .init();
    cli.verify()
}
