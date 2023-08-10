mod commitment;
mod field_data;
mod lurk_proof;
mod paths;
mod repl;

use anyhow::{bail, Context, Result};
use camino::Utf8PathBuf;
use clap::{Args, Parser, Subcommand};
use config::{Config, Environment, File};
use pasta_curves::pallas;

use std::{collections::HashMap, fs};

use crate::{
    field::{LanguageField, LurkField},
    store::Store,
    z_data::{from_z_data, ZData},
    z_store::ZStore,
};

use crate::cli::{
    paths::set_lurk_dirs,
    repl::{validate_non_zero, Backend, Repl},
};

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
    lurk_file: Utf8PathBuf,

    /// ZStore to be preloaded before the loading the file
    #[clap(long, value_parser)]
    zstore: Option<Utf8PathBuf>,

    /// Flag to prove the last evaluation
    #[arg(long)]
    prove: bool,

    /// Config file, containing the lowest precedence parameters
    #[clap(long, value_parser)]
    config: Option<Utf8PathBuf>,

    /// Reduction count used for proofs (defaults to 10)
    #[clap(long, value_parser)]
    rc: Option<usize>,

    /// Iterations allowed (defaults to 100_000_000; rounded up to the next multiple of rc)
    #[clap(long, value_parser)]
    limit: Option<usize>,

    /// Prover backend (defaults to "Nova")
    #[clap(long, value_parser)]
    backend: Option<String>,

    /// Arithmetic field (defaults to the backend's standard field)
    #[clap(long, value_parser)]
    field: Option<String>,

    /// Path to public parameters directory
    #[clap(long, value_parser)]
    public_params_dir: Option<Utf8PathBuf>,

    /// Path to proofs directory
    #[clap(long, value_parser)]
    proofs_dir: Option<Utf8PathBuf>,

    /// Path to commitments directory
    #[clap(long, value_parser)]
    commits_dir: Option<Utf8PathBuf>,
}

#[derive(Parser, Debug)]
struct LoadCli {
    #[clap(value_parser = parse_filename)]
    lurk_file: Utf8PathBuf,

    #[clap(long, value_parser)]
    zstore: Option<Utf8PathBuf>,

    #[arg(long)]
    prove: bool,

    #[clap(long, value_parser)]
    config: Option<Utf8PathBuf>,

    #[clap(long, value_parser)]
    rc: Option<usize>,

    #[clap(long, value_parser)]
    limit: Option<usize>,

    #[clap(long, value_parser)]
    backend: Option<String>,

    #[clap(long, value_parser)]
    field: Option<String>,

    #[clap(long, value_parser)]
    public_params_dir: Option<Utf8PathBuf>,

    #[clap(long, value_parser)]
    proofs_dir: Option<Utf8PathBuf>,

    #[clap(long, value_parser)]
    commits_dir: Option<Utf8PathBuf>,
}

impl LoadArgs {
    fn into_cli(self) -> LoadCli {
        LoadCli {
            lurk_file: self.lurk_file,
            zstore: self.zstore,
            prove: self.prove,
            config: self.config,
            rc: self.rc,
            limit: self.limit,
            backend: self.backend,
            field: self.field,
            public_params_dir: self.public_params_dir,
            proofs_dir: self.proofs_dir,
            commits_dir: self.commits_dir,
        }
    }
}

#[derive(Args, Debug)]
struct ReplArgs {
    /// ZStore to be preloaded before entering the REPL (and loading a file)
    #[clap(long, value_parser)]
    zstore: Option<Utf8PathBuf>,

    /// Optional file to be loaded before entering the REPL
    #[clap(long, value_parser)]
    load: Option<Utf8PathBuf>,

    /// Config file, containing the lowest precedence parameters
    #[clap(long, value_parser)]
    config: Option<Utf8PathBuf>,

    /// Reduction count used for proofs (defaults to 10)
    #[clap(long, value_parser)]
    rc: Option<usize>,

    /// Iterations allowed (defaults to 100_000_000; rounded up to the next multiple of rc)
    #[clap(long, value_parser)]
    limit: Option<usize>,

    /// Prover backend (defaults to "Nova")
    #[clap(long, value_parser)]
    backend: Option<String>,

    /// Arithmetic field (defaults to the backend's standard field)
    #[clap(long, value_parser)]
    field: Option<String>,

    /// Path to public parameters directory
    #[clap(long, value_parser)]
    public_params_dir: Option<Utf8PathBuf>,

    /// Path to proofs directory
    #[clap(long, value_parser)]
    proofs_dir: Option<Utf8PathBuf>,

    /// Path to commitments directory
    #[clap(long, value_parser)]
    commits_dir: Option<Utf8PathBuf>,
}

#[derive(Parser, Debug)]
struct ReplCli {
    #[clap(long, value_parser)]
    load: Option<Utf8PathBuf>,

    #[clap(long, value_parser)]
    zstore: Option<Utf8PathBuf>,

    #[clap(long, value_parser)]
    config: Option<Utf8PathBuf>,

    #[clap(long, value_parser)]
    rc: Option<usize>,

    #[clap(long, value_parser)]
    limit: Option<usize>,

    #[clap(long, value_parser)]
    backend: Option<String>,

    #[clap(long, value_parser)]
    field: Option<String>,

    #[clap(long, value_parser)]
    public_params_dir: Option<Utf8PathBuf>,

    #[clap(long, value_parser)]
    proofs_dir: Option<Utf8PathBuf>,

    #[clap(long, value_parser)]
    commits_dir: Option<Utf8PathBuf>,
}

impl ReplArgs {
    fn into_cli(self) -> ReplCli {
        ReplCli {
            load: self.load,
            zstore: self.zstore,
            config: self.config,
            rc: self.rc,
            limit: self.limit,
            backend: self.backend,
            field: self.field,
            public_params_dir: self.public_params_dir,
            proofs_dir: self.proofs_dir,
            commits_dir: self.commits_dir,
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

fn parse_filename(file: &str) -> Result<Utf8PathBuf> {
    if file == "help" {
        bail!("help is not a valid filename. printing help console instead");
    }
    let path: Utf8PathBuf = file.into();
    Ok(path)
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

pub fn get_config(config_path: &Option<Utf8PathBuf>) -> Result<HashMap<String, String>> {
    // First load from the config file
    let builder = match config_path {
        Some(config_path) if config_path.exists() => {
            Config::builder().add_source(File::with_name(config_path.as_str()))
        }
        _ => Config::builder(),
    };
    // Then potentially overwrite with environment variables
    let builder = builder.add_source(Environment::with_prefix("LURK"));
    Ok(builder.build()?.try_deserialize()?)
}

fn get_store<F: LurkField + for<'a> serde::de::Deserialize<'a>>(
    zstore_path: &Option<Utf8PathBuf>,
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
    ( $cli: expr, $rc: expr, $limit: expr, $field: path, $backend: expr ) => {{
        let mut store = get_store(&$cli.zstore).with_context(|| "reading store from file")?;
        let env = store.nil();
        Repl::<$field>::new(store, env, $rc, $limit, $backend)
    }};
}

impl ReplCli {
    fn run(&self) -> Result<()> {
        macro_rules! repl {
            ( $rc: expr, $limit: expr, $field: path, $backend: expr ) => {{
                let mut repl = new_repl!(self, $rc, $limit, $field, $backend);
                if let Some(lurk_file) = &self.load {
                    repl.load_file(lurk_file)?;
                }
                repl.start()
            }};
        }
        let config = get_config(&self.config)?;
        log::info!("Configured variables: {:?}", config);
        set_lurk_dirs(
            &config,
            &self.public_params_dir,
            &self.proofs_dir,
            &self.commits_dir,
        );
        let rc = get_parsed_usize("rc", &self.rc, &config, DEFAULT_RC)?;
        let limit = get_parsed_usize("limit", &self.limit, &config, DEFAULT_LIMIT)?;
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
        validate_non_zero("rc", rc)?;
        backend.validate_field(&field)?;
        match field {
            LanguageField::Pallas => repl!(rc, limit, pallas::Scalar, backend),
            // LanguageField::Vesta => repl!(rc, limit, vesta::Scalar, backend),
            // LanguageField::BLS12_381 => repl!(rc, limit, blstrs::Scalar, backend),
            LanguageField::Vesta => todo!(),
            LanguageField::BLS12_381 => todo!(),
            LanguageField::BN256 => todo!(),
            LanguageField::Grumpkin => todo!(),
        }
    }
}

impl LoadCli {
    fn run(&self) -> Result<()> {
        macro_rules! load {
            ( $rc: expr, $limit: expr, $field: path, $backend: expr ) => {{
                let mut repl = new_repl!(self, $rc, $limit, $field, $backend);
                repl.load_file(&self.lurk_file)?;
                if self.prove {
                    repl.prove_last_frames()?;
                }
                Ok(())
            }};
        }
        let config = get_config(&self.config)?;
        log::info!("Configured variables: {:?}", config);
        set_lurk_dirs(
            &config,
            &self.public_params_dir,
            &self.proofs_dir,
            &self.commits_dir,
        );
        let rc = get_parsed_usize("rc", &self.rc, &config, DEFAULT_RC)?;
        let limit = get_parsed_usize("limit", &self.limit, &config, DEFAULT_LIMIT)?;
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
        validate_non_zero("rc", rc)?;
        backend.validate_field(&field)?;
        match field {
            LanguageField::Pallas => load!(rc, limit, pallas::Scalar, backend),
            // LanguageField::Vesta => load!(rc, limit, vesta::Scalar, backend),
            // LanguageField::BLS12_381 => load!(rc, limit, blstrs::Scalar, backend),
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

    /// Config file, containing the lowest precedence parameters
    #[clap(long, value_parser)]
    config: Option<Utf8PathBuf>,

    /// Path to public parameters directory
    #[clap(long, value_parser)]
    public_params_dir: Option<Utf8PathBuf>,

    /// Path to proofs directory
    #[clap(long, value_parser)]
    proofs_dir: Option<Utf8PathBuf>,
}

impl Cli {
    fn run(self) -> Result<()> {
        match self.command {
            Command::Repl(repl_args) => repl_args.into_cli().run(),
            Command::Load(load_args) => load_args.into_cli().run(),
            #[allow(unused_variables)]
            Command::Verify(verify_args) => {
                use crate::cli::lurk_proof::LurkProof;
                let config = get_config(&verify_args.config)?;
                log::info!("Configured variables: {:?}", config);
                set_lurk_dirs(
                    &config,
                    &verify_args.public_params_dir,
                    &verify_args.proofs_dir,
                    &None,
                );
                LurkProof::verify_proof(&verify_args.proof_id)?;
                Ok(())
            }
        }
    }
}

/// Parses CLI arguments and continues the program flow accordingly
pub fn parse_and_run() -> Result<()> {
    if let Ok(cli) = Cli::try_parse() {
        cli.run()
    } else if let Ok(repl_cli) = ReplCli::try_parse() {
        repl_cli.run()
    } else if let Ok(load_cli) = LoadCli::try_parse() {
        load_cli.run()
    } else {
        // force printing help
        Cli::parse();
        Ok(())
    }
}
