mod commitment;
mod field_data;
mod lurk_proof;
mod paths;
mod repl;

use anyhow::{bail, Context, Result};
use clap::{Args, Parser, Subcommand};
use config::{Config, Environment, File};
use pasta_curves::pallas;
use std::{collections::HashMap, fs, path::PathBuf};

use lurk::{
    field::{LanguageField, LurkField},
    store::Store,
    z_data::{from_z_data, ZData},
    z_store::ZStore,
};

use crate::cli::repl::validate_non_zero;

use self::repl::{Backend, Repl};

const DEFAULT_LIMIT: usize = 100_000_000;
const DEFAULT_RC: usize = 10;
const DEFAULT_BACKEND: Backend = Backend::Nova;

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
    /// Verifies a Lurk proof
    Verify(VerifyArgs),
}

#[derive(Args, Debug)]
struct LoadArgs {
    /// The file to be loaded
    #[clap(value_parser)]
    lurk_file: PathBuf,

    /// ZStore to be preloaded before the loading the file
    #[clap(long, value_parser)]
    zstore: Option<PathBuf>,

    /// Flag to prove the last evaluation
    #[arg(long)]
    prove: bool,

    /// Config file, containing the lowest precedence parameters
    #[clap(long, value_parser)]
    config: Option<PathBuf>,

    /// Maximum number of iterations allowed (defaults to 100_000_000)
    #[clap(long, value_parser)]
    limit: Option<usize>,

    /// Reduction count used for proofs (defaults to 10)
    #[clap(long, value_parser)]
    rc: Option<usize>,

    /// Prover backend (defaults to "Nova")
    #[clap(long, value_parser)]
    backend: Option<String>,

    /// Arithmetic field (defaults to the backend's standard field)
    #[clap(long, value_parser)]
    field: Option<String>,
}

#[derive(Parser, Debug)]
struct LoadCli {
    #[clap(value_parser)]
    lurk_file: PathBuf,

    #[clap(long, value_parser)]
    zstore: Option<PathBuf>,

    #[arg(long)]
    prove: bool,

    #[clap(long, value_parser)]
    config: Option<PathBuf>,

    #[clap(long, value_parser)]
    limit: Option<usize>,

    #[clap(long, value_parser)]
    rc: Option<usize>,

    #[clap(long, value_parser)]
    backend: Option<String>,

    #[clap(long, value_parser)]
    field: Option<String>,
}

impl LoadArgs {
    pub fn into_cli(self) -> LoadCli {
        LoadCli {
            lurk_file: self.lurk_file,
            zstore: self.zstore,
            prove: self.prove,
            config: self.config,
            limit: self.limit,
            rc: self.rc,
            backend: self.backend,
            field: self.field,
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

    /// Config file, containing the lowest precedence parameters
    #[clap(long, value_parser)]
    config: Option<PathBuf>,

    /// Maximum number of iterations allowed (defaults to 100_000_000)
    #[clap(long, value_parser)]
    limit: Option<usize>,

    /// Reduction count used for proofs (defaults to 10)
    #[clap(long, value_parser)]
    rc: Option<usize>,

    /// Prover backend (defaults to "Nova")
    #[clap(long, value_parser)]
    backend: Option<String>,

    /// Arithmetic field (defaults to the backend's standard field)
    #[clap(long, value_parser)]
    field: Option<String>,
}

#[derive(Parser, Debug)]
struct ReplCli {
    #[clap(long, value_parser)]
    load: Option<PathBuf>,

    #[clap(long, value_parser)]
    zstore: Option<PathBuf>,

    #[clap(long, value_parser)]
    config: Option<PathBuf>,

    #[clap(long, value_parser)]
    limit: Option<usize>,

    #[clap(long, value_parser)]
    rc: Option<usize>,

    #[clap(long, value_parser)]
    backend: Option<String>,

    #[clap(long, value_parser)]
    field: Option<String>,
}

impl ReplArgs {
    pub fn into_cli(self) -> ReplCli {
        ReplCli {
            load: self.load,
            zstore: self.zstore,
            config: self.config,
            limit: self.limit,
            rc: self.rc,
            backend: self.backend,
            field: self.field,
        }
    }
}

fn parse_backend(backend_str: &String) -> Result<Backend> {
    match backend_str.to_lowercase().as_str() {
        "nova" => Ok(Backend::Nova),
        "snarkpack+" => Ok(Backend::SnarkPackPlus),
        _ => bail!("Backend not supported: {backend_str}"),
    }
}

fn parse_field(field_str: &String) -> Result<LanguageField> {
    match field_str.to_lowercase().as_str() {
        "pallas" => Ok(LanguageField::Pallas),
        "vesta" => Ok(LanguageField::Vesta),
        "bls12-381" => Ok(LanguageField::BLS12_381),
        _ => bail!("Field not supported: {field_str}"),
    }
}

fn get_parsed_usize(
    param_name: &str,
    arg: &Option<usize>,
    config: &HashMap<String, String>,
    default: usize,
) -> Result<usize> {
    match arg {
        Some(arg) => Ok(*arg),
        None => match config.get(param_name) {
            None => Ok(default),
            Some(arg_str) => Ok(arg_str.parse::<usize>()?),
        },
    }
}

fn get_parsed<T>(
    param_name: &str,
    arg: &Option<String>,
    config: &HashMap<String, String>,
    parse_fn: fn(&String) -> Result<T>,
    default: T,
) -> Result<T> {
    match arg {
        Some(arg) => parse_fn(arg),
        None => match config.get(param_name) {
            None => Ok(default),
            Some(arg) => parse_fn(arg),
        },
    }
}

fn get_config(config_path: &Option<PathBuf>) -> Result<HashMap<String, String>> {
    // First load from the config file
    let builder = match config_path {
        Some(config_path) => Config::builder().add_source(File::from(config_path.to_owned())),
        None => Config::builder(),
    };
    // Then potentially overwrite with environment variables
    let builder = builder.add_source(Environment::with_prefix("LURK"));
    Ok(builder.build()?.try_deserialize()?)
}

fn get_store<F: LurkField + for<'a> serde::de::Deserialize<'a>>(
    zstore_path: &Option<PathBuf>,
) -> Result<Store<F>> {
    match zstore_path {
        None => Ok(Store::default()),
        Some(zstore_path) => {
            let bytes = fs::read(zstore_path)?;
            let zdata = ZData::from_bytes(&bytes)?;
            let zstore: ZStore<F> = from_z_data(&zdata)?;
            Ok(zstore.to_store())
        }
    }
}

macro_rules! new_repl {
    ( $cli: expr, $limit: expr, $rc: expr, $field: path, $backend: expr ) => {{
        let store = get_store(&$cli.zstore).with_context(|| "reading store from file")?;
        let env = store.nil_ptr();
        Repl::<$field>::new(store, env, $limit, $rc, $backend)
    }};
}

impl ReplCli {
    pub fn run(&self) -> Result<()> {
        macro_rules! repl {
            ( $limit: expr, $rc: expr, $field: path, $backend: expr ) => {{
                let mut repl = new_repl!(self, $limit, $rc, $field, $backend);
                if let Some(lurk_file) = &self.load {
                    repl.load_file(lurk_file)?;
                }
                repl.start()
            }};
        }
        let config = get_config(&self.config)?;
        let limit = get_parsed_usize("limit", &self.limit, &config, DEFAULT_LIMIT)?;
        let rc = get_parsed_usize("rc", &self.rc, &config, DEFAULT_RC)?;
        let backend = get_parsed(
            "backend",
            &self.backend,
            &config,
            parse_backend,
            DEFAULT_BACKEND,
        )?;
        let field = get_parsed(
            "field",
            &self.field,
            &config,
            parse_field,
            backend.default_field(),
        )?;
        validate_non_zero("limit", limit)?;
        validate_non_zero("rc", rc)?;
        backend.validate_field(&field)?;
        match field {
            LanguageField::Pallas => repl!(limit, rc, pallas::Scalar, backend),
            // LanguageField::Vesta => repl!(limit, rc, vesta::Scalar, backend),
            // LanguageField::BLS12_381 => repl!(limit, rc, blstrs::Scalar, backend),
            LanguageField::Vesta => todo!(),
            LanguageField::BLS12_381 => todo!(),
            LanguageField::BN256 => todo!(),
            LanguageField::Grumpkin => todo!(),
        }
    }
}

impl LoadCli {
    pub fn run(&self) -> Result<()> {
        macro_rules! load {
            ( $limit: expr, $rc: expr, $field: path, $backend: expr ) => {{
                let mut repl = new_repl!(self, $limit, $rc, $field, $backend);
                repl.load_file(&self.lurk_file)?;
                if self.prove {
                    #[cfg(not(target_arch = "wasm32"))]
                    repl.prove_last_frames()?;
                }
                Ok(())
            }};
        }
        let config = get_config(&self.config)?;
        let limit = get_parsed_usize("limit", &self.limit, &config, DEFAULT_LIMIT)?;
        let rc = get_parsed_usize("rc", &self.rc, &config, DEFAULT_RC)?;
        let backend = get_parsed(
            "backend",
            &self.backend,
            &config,
            parse_backend,
            DEFAULT_BACKEND,
        )?;
        let field = get_parsed(
            "field",
            &self.field,
            &config,
            parse_field,
            backend.default_field(),
        )?;
        validate_non_zero("limit", limit)?;
        validate_non_zero("rc", rc)?;
        backend.validate_field(&field)?;
        match field {
            LanguageField::Pallas => load!(limit, rc, pallas::Scalar, backend),
            // LanguageField::Vesta => load!(limit, rc, vesta::Scalar, backend),
            // LanguageField::BLS12_381 => load!(limit, rc, blstrs::Scalar, backend),
            LanguageField::Vesta => todo!(),
            LanguageField::BLS12_381 => todo!(),
            LanguageField::BN256 => todo!(),
            LanguageField::Grumpkin => todo!(),
        }
    }
}

#[derive(Args, Debug)]
struct VerifyArgs {
    /// ID of the proof to be verified
    #[clap(value_parser)]
    proof_id: String,
}

/// Parses CLI arguments and continues the program flow accordingly
pub fn parse_and_run() -> Result<()> {
    #[cfg(not(target_arch = "wasm32"))]
    paths::non_wasm::create_lurk_dirs()?;

    if let Ok(repl_cli) = ReplCli::try_parse() {
        repl_cli.run()
    } else if let Ok(load_cli) = LoadCli::try_parse() {
        load_cli.run()
    } else {
        match Cli::parse().command {
            Command::Repl(repl_args) => repl_args.into_cli().run(),
            Command::Load(load_args) => load_args.into_cli().run(),
            #[allow(unused_variables)]
            Command::Verify(verify_args) => {
                #[cfg(not(target_arch = "wasm32"))]
                {
                    use crate::cli::lurk_proof::LurkProof;
                    LurkProof::verify_proof(&verify_args.proof_id)?;
                }
                Ok(())
            }
        }
    }
}
