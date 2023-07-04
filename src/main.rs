use std::fs;
use std::path::PathBuf;
use std::sync::Arc;

use anyhow::{bail, Result};

use lurk::coprocessor::Coprocessor;
use lurk::eval::lang::{Coproc, Lang};
use lurk::field::{LanguageField, LurkField};
use lurk::ptr::Ptr;
use lurk::public_parameters::Claim;
use lurk::store::Store;
use lurk::z_data::{from_z_data, ZData};
use lurk::z_store::ZStore;
// use lurk::repl::{repl_cli, ReplState};
use pasta_curves::{pallas, vesta};

use clap::{Args, Parser, Subcommand};
use tap::TapOptional;

const DEFAULT_FIELD: LanguageField = LanguageField::Pallas;
const DEFAULT_LIMIT: usize = 100_000_000;

#[derive(Parser, Debug)]
#[clap(version, about, long_about = None)]
struct Cli {
    #[clap(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand, Debug)]
enum Command {
    Run(Run),
    Repl(Repl),
    Verify(Verify),
}

#[derive(Args, Debug)]
struct Run {
    #[clap(value_parser)]
    lurk_file: PathBuf,

    #[clap(long, value_parser)]
    zstore: Option<PathBuf>,

    #[clap(long, value_parser)]
    limit: Option<usize>,

    #[arg(long)]
    prove: bool,
}

#[derive(Args, Debug)]
struct Repl {
    #[clap(long, value_parser)]
    zstore: Option<PathBuf>,

    #[clap(long, value_parser)]
    limit: Option<usize>,
}

#[derive(Args, Debug)]
struct Verify {
    #[clap(value_parser)]
    proof_file: PathBuf,
}

struct ReplState<F: LurkField, C: Coprocessor<F>> {
    pub store: Store<F>,
    pub env: Ptr<F>,
    pub limit: usize,
    pub lang: Arc<Lang<F, C>>,
    pub last_claim: Option<Claim<F>>,
}

impl<F: LurkField, C: Coprocessor<F>> ReplState<F, C> {
    pub fn new(store: Store<F>, env: Ptr<F>, limit: usize) -> ReplState<F, C> {
        ReplState {
            store,
            env,
            limit,
            lang: Arc::new(Lang::<F, C>::new()),
            last_claim: None,
        }
    }

    pub fn repl(&mut self) -> Result<()> {
        Ok(())
    }

    pub fn load_file(&mut self, path: &PathBuf) -> Result<()> {
        Ok(())
    }

    pub fn prove_last_claim(&mut self) -> Result<()> {
        Ok(())
    }

    pub fn verify(&mut self, proof_id: String) -> Result<()> {
        Ok(())
    }
}

fn get_field() -> Result<LanguageField> {
    if let Ok(lurk_field) = std::env::var("LURK_FIELD") {
        match lurk_field.to_lowercase().as_str() {
            "bls12-381" => Ok(LanguageField::BLS12_381),
            "pallas" => Ok(LanguageField::Pallas),
            "vesta" => Ok(LanguageField::Vesta),
            _ => bail!("Field not supported: {lurk_field}"),
        }
    } else {
        Ok(DEFAULT_FIELD)
    }
}

fn get_store<F: LurkField + for<'a> serde::de::Deserialize<'a>>(
    zstore: &Option<PathBuf>,
) -> Store<F> {
    let received_z_store = zstore.is_some();
    zstore
        .as_ref()
        .and_then(|z_store_path| fs::read(z_store_path).ok())
        .and_then(|bytes| ZData::from_bytes(&bytes).ok())
        .and_then(|zd| from_z_data(&zd).ok())
        .map(|z_store: ZStore<F>| ZStore::to_store(&z_store))
        .tap_none(|| {
            if received_z_store {
                eprintln!("Failed to load ZStore. Starting with empty store.")
            }
        })
        .unwrap_or_default()
}

macro_rules! new_repl_state {
    ( $cmd: expr, $field: path ) => {{
        let limit = $cmd.limit.unwrap_or(DEFAULT_LIMIT);
        let mut store = get_store(&$cmd.zstore);
        let env = store.nil();
        let repl_state = ReplState::<$field, Coproc<$field>>::new(store, env, limit);
        repl_state
    }};
}

fn main() -> Result<()> {
    pretty_env_logger::init();

    let cli = Cli::parse();
    // TODO: `lurk file.lurk` isn't parsed. is there a proper way to support it?
    match cli.command {
        None => Ok(()),
        Some(Command::Repl(cmd)) => match get_field()? {
            LanguageField::Pallas => {
                let mut repl_state = new_repl_state!(&cmd, pallas::Scalar);
                repl_state.repl()
            }
            LanguageField::Vesta => {
                let mut repl_state = new_repl_state!(&cmd, vesta::Scalar);
                repl_state.repl()
            }
            LanguageField::BLS12_381 => {
                let mut repl_state = new_repl_state!(&cmd, blstrs::Scalar);
                repl_state.repl()
            }
        },
        Some(Command::Run(cmd)) => match get_field()? {
            LanguageField::Pallas => {
                let mut repl_state = new_repl_state!(&cmd, pallas::Scalar);
                repl_state.load_file(&cmd.lurk_file)?;
                if cmd.prove {
                    repl_state.prove_last_claim()?;
                }
                Ok(())
            }
            LanguageField::Vesta => {
                let mut repl_state = new_repl_state!(&cmd, vesta::Scalar);
                repl_state.load_file(&cmd.lurk_file)?;
                if cmd.prove {
                    repl_state.prove_last_claim()?;
                }
                Ok(())
            }
            LanguageField::BLS12_381 => {
                let mut repl_state = new_repl_state!(&cmd, blstrs::Scalar);
                repl_state.load_file(&cmd.lurk_file)?;
                if cmd.prove {
                    repl_state.prove_last_claim()?;
                }
                Ok(())
            }
        },
        Some(Command::Verify(verify)) => Ok(()),
    }
}
