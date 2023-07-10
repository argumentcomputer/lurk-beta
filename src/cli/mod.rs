mod paths;
mod prove_and_verify;
mod repl;

use std::fs;
use std::path::PathBuf;

use anyhow::{bail, Context, Result};

use log::info;
use lurk::eval::lang::Coproc;
use lurk::field::{LanguageField, LurkField};
use lurk::store::Store;
use lurk::z_data::{from_z_data, ZData};
use lurk::z_store::ZStore;
use pasta_curves::{pallas, vesta};

use clap::{Args, Parser, Subcommand};

// use self::prove_and_verify::verify_proof;
use self::repl::Repl;

const DEFAULT_FIELD: LanguageField = LanguageField::Pallas;
const DEFAULT_LIMIT: usize = 100_000_000;
const DEFAULT_RC: usize = 10;

#[derive(Parser, Debug)]
#[clap(version)]
struct Cli {
    #[clap(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Loads a file, processing forms sequentially ("load" can be elided)
    Load(LoadArgs),
    /// Enters Lurk's REPL environment ("repl" can be elided)
    Repl(ReplArgs),
    // /// Verifies a Lurk proof
    // Verify(VerifyArgs),
}

#[derive(Args, Debug)]
struct LoadArgs {
    /// The file to be loaded
    #[clap(value_parser)]
    lurk_file: PathBuf,

    /// ZStore to be preloaded before the loading the file
    #[clap(long, value_parser)]
    zstore: Option<PathBuf>,

    /// Maximum number of iterations allowed (defaults to 100_000_000)
    #[clap(long, value_parser)]
    limit: Option<usize>,
    // /// Reduction count used for proofs (defaults to 10)
    // #[clap(long, value_parser)]
    // rc: Option<usize>,

    // /// Flag to prove the last evaluation
    // #[arg(long)]
    // prove: bool,
}

#[derive(Parser, Debug)]
struct LoadCli {
    #[clap(value_parser)]
    lurk_file: PathBuf,

    #[clap(long, value_parser)]
    zstore: Option<PathBuf>,

    #[clap(long, value_parser)]
    limit: Option<usize>,
    // #[arg(long)]
    // prove: bool,

    // #[clap(long, value_parser)]
    // rc: Option<usize>,
}

impl LoadArgs {
    pub fn into_cli(self) -> LoadCli {
        LoadCli {
            lurk_file: self.lurk_file,
            zstore: self.zstore,
            limit: self.limit,
            // prove: self.prove,
            // rc: self.rc,
        }
    }
}

#[derive(Args, Debug)]
struct ReplArgs {
    /// ZStore to be preloaded before entering the REPL (and loading a file)
    #[clap(long, value_parser)]
    zstore: Option<PathBuf>,

    /// Optional file to be loaded before entering the REPL
    #[clap(long, value_parser)]
    load: Option<PathBuf>,

    /// Maximum number of iterations allowed (defaults to 100_000_000)
    #[clap(long, value_parser)]
    limit: Option<usize>,
    // /// Reduction count used for proofs (defaults to 10)
    // #[clap(long, value_parser)]
    // rc: Option<usize>,
}

#[derive(Parser, Debug)]
struct ReplCli {
    #[clap(long, value_parser)]
    load: Option<PathBuf>,

    #[clap(long, value_parser)]
    zstore: Option<PathBuf>,

    #[clap(long, value_parser)]
    limit: Option<usize>,
    // #[clap(long, value_parser)]
    // rc: Option<usize>,
}

impl ReplArgs {
    pub fn into_cli(self) -> ReplCli {
        ReplCli {
            load: self.load,
            zstore: self.zstore,
            limit: self.limit,
            // rc: self.rc,
        }
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
    zstore_path: &Option<PathBuf>,
) -> Result<Store<F>> {
    match zstore_path {
        None => Ok(Store::default()),
        Some(zstore_path) => {
            info!("Reading ZStore bytes");
            let bytes = fs::read(zstore_path)?;
            info!("Deserializing ZStore bytes into ZData");
            let zdata = ZData::from_bytes(&bytes)?;
            info!("Deserializing ZData into ZStore");
            let zstore: ZStore<F> = from_z_data(&zdata)?;
            info!("Converting ZStore into Store");
            let store = zstore.to_store();
            Ok(store)
        }
    }
}

macro_rules! new_repl {
    ( $cli: expr, $field: path ) => {{
        let limit = $cli.limit.unwrap_or(DEFAULT_LIMIT);
        // let rc = $cli.rc.unwrap_or(DEFAULT_RC);
        let mut store = get_store(&$cli.zstore).with_context(|| "reading store from file")?;
        let env = store.nil();
        // Repl::<$field, Coproc<$field>>::new(store, env, limit, rc)?
        Repl::<$field, Coproc<$field>>::new(store, env, limit, DEFAULT_RC)?
    }};
}

impl ReplCli {
    pub fn run(&self) -> Result<()> {
        macro_rules! repl {
            ( $field: path ) => {{
                let mut repl = new_repl!(self, $field);
                if let Some(lurk_file) = &self.load {
                    repl.load_file(lurk_file)?;
                }
                repl.start()
            }};
        }
        match get_field()? {
            LanguageField::Pallas => repl!(pallas::Scalar),
            LanguageField::Vesta => repl!(vesta::Scalar),
            LanguageField::BLS12_381 => repl!(blstrs::Scalar),
        }
    }
}

impl LoadCli {
    pub fn run(&self) -> Result<()> {
        macro_rules! load {
            ( $field: path ) => {{
                let mut repl = new_repl!(self, $field);
                repl.load_file(&self.lurk_file)?;
                // if self.prove {
                //     repl.prove_last_claim()?;
                // }
                Ok(())
            }};
        }
        match get_field()? {
            LanguageField::Pallas => load!(pallas::Scalar),
            LanguageField::Vesta => load!(vesta::Scalar),
            LanguageField::BLS12_381 => load!(blstrs::Scalar),
        }
    }
}

// #[derive(Args, Debug)]
// struct VerifyArgs {
//     #[clap(value_parser)]
//     proof_file: PathBuf,
// }

/// Parses CLI arguments and continues the program flow accordingly
pub fn parse_and_run() -> Result<()> {
    #[cfg(not(target_arch = "wasm32"))]
    paths::create_lurk_dir()?;
    if let Ok(repl_cli) = ReplCli::try_parse() {
        repl_cli.run()
    } else if let Ok(load_cli) = LoadCli::try_parse() {
        load_cli.run()
    } else {
        match Cli::parse().command {
            Command::Repl(repl_args) => repl_args.into_cli().run(),
            Command::Load(load_args) => load_args.into_cli().run(),
            // Command::Verify(verify_args) => verify_proof(&verify_args.proof_file),
        }
    }
}
