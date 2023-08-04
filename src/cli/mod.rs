mod commitment;
mod field_data;
mod lurk_proof;
mod paths;
mod repl;

use anyhow::{bail, Context, Result};
use camino::Utf8PathBuf;
use clap::{Args, Parser, Subcommand};
use config::{Config, Environment, File};
use once_cell::sync::OnceCell;
use pasta_curves::pallas;

use std::{collections::HashMap, fs};

use lurk::{
    field::{LanguageField, LurkField},
    public_parameters::public_params_default_dir,
    store::Store,
    z_data::{from_z_data, ZData},
    z_store::ZStore,
};

use crate::cli::repl::validate_non_zero;

use self::repl::{Backend, Repl};

const DEFAULT_LIMIT: usize = 100_000_000;
const DEFAULT_RC: usize = 10;
const DEFAULT_BACKEND: Backend = Backend::Nova;

pub static PUBLIC_PARAMS_DIR: OnceCell<Utf8PathBuf> = OnceCell::new();
pub static COMMITS_DIR: OnceCell<Utf8PathBuf> = OnceCell::new();
pub static PROOFS_DIR: OnceCell<Utf8PathBuf> = OnceCell::new();

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

    /// Path to store public params on disk
    #[clap(long, value_parser)]
    public_params_dir: Option<Utf8PathBuf>,

    /// Path to store proofs on disk
    #[clap(long, value_parser)]
    proofs_dir: Option<Utf8PathBuf>,

    /// Path to store commitments on disk
    #[clap(long, value_parser)]
    commits_dir: Option<Utf8PathBuf>,
}

#[derive(Parser, Debug)]
struct LoadCli {
    #[clap(value_parser)]
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

    /// Path to store public params on disk
    #[clap(long, value_parser)]
    public_params_dir: Option<Utf8PathBuf>,

    /// Path to store proofs on disk
    #[clap(long, value_parser)]
    proofs_dir: Option<Utf8PathBuf>,

    /// Path to store commitments on disk
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

fn get_config(config_path: &Option<Utf8PathBuf>) -> Result<HashMap<String, String>> {
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

fn set_lurk_dirs(
    config: &HashMap<String, String>,
    public_params_dir: &Option<Utf8PathBuf>,
    proofs_dir: &Option<Utf8PathBuf>,
    commits_dir: &Option<Utf8PathBuf>,
) {
    let get_path = |given_path: &Option<Utf8PathBuf>, config_key: &str, default: Utf8PathBuf| {
        given_path.clone().unwrap_or_else(|| {
            config
                .get(config_key)
                .map_or_else(|| default, Utf8PathBuf::from)
        })
    };

    let public_params_dir = get_path(
        public_params_dir,
        "public_params",
        public_params_default_dir(),
    );
    let proofs_dir = get_path(proofs_dir, "proofs", Utf8PathBuf::from("proofs"));
    let commits_dir = get_path(commits_dir, "commits", Utf8PathBuf::from("commits"));

    PUBLIC_PARAMS_DIR.get_or_init(|| public_params_dir);
    PROOFS_DIR.get_or_init(|| proofs_dir);
    COMMITS_DIR.get_or_init(|| commits_dir);

    paths::create_lurk_dirs().unwrap();
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
    pub fn run(&self) -> Result<()> {
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
    pub fn run(&self) -> Result<()> {
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
}

impl Cli {
    fn run(self) -> Result<()> {
        match self.command {
            Command::Repl(repl_args) => repl_args.into_cli().run(),
            Command::Load(load_args) => load_args.into_cli().run(),
            #[allow(unused_variables)]
            Command::Verify(verify_args) => {
                use crate::cli::lurk_proof::LurkProof;
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

#[cfg(test)]
mod tests {
    use assert_cmd::Command;
    use camino::Utf8Path;
    use std::fs::File;
    use std::io::prelude::*;
    use tempfile::Builder;

    fn lurk_cmd() -> Command {
        Command::cargo_bin("lurk").unwrap()
    }

    #[test]
    fn test_bad_command() {
        let tmp_dir = Builder::new().prefix("tmp").tempdir().unwrap();
        let bad_file = tmp_dir.path().join("uiop");

        let mut cmd = lurk_cmd();
        cmd.arg(bad_file.to_str().unwrap());
        cmd.assert().failure();
    }

    #[test]
    fn test_config_file() {
        pretty_env_logger::formatted_builder()
            .is_test(true)
            .try_init()
            .unwrap();
        let tmp_dir = Builder::new().prefix("tmp").tempdir().unwrap();
        let tmp_dir = Utf8Path::from_path(tmp_dir.path()).unwrap();
        let config_dir = tmp_dir.join("lurk.toml");
        let public_params_dir = tmp_dir.join("public_params").into_string();
        let proofs_dir = tmp_dir.join("proofs").into_string();
        let commits_dir = tmp_dir.join("commits").into_string();

        let mut config_file = File::create(&config_dir).unwrap();
        config_file
            .write_all(format!("public_params = \"{}\"\n", public_params_dir).as_bytes())
            .unwrap();
        config_file
            .write_all(format!("proofs = \"{}\"\n", proofs_dir).as_bytes())
            .unwrap();
        config_file
            .write_all(format!("commits = \"{}\"\n", commits_dir).as_bytes())
            .unwrap();

        // Overwrite proof dir with env var
        let proofs_dir_env = tmp_dir.join("proofs_env").into_string();

        std::env::set_var("LURK_PROOFS", proofs_dir_env.clone());

        let config = crate::cli::get_config(&Some(config_dir)).unwrap();

        assert_eq!(config.get("public_params").unwrap(), &public_params_dir);
        assert_eq!(config.get("proofs").unwrap(), &proofs_dir_env);
        assert_eq!(config.get("commits").unwrap(), &commits_dir);
    }

    // TODO: Use a snapshot test for the proof ID and/or test the REPL process
    #[test]
    fn test_prove_and_verify() {
        let tmp_dir = Builder::new().prefix("tmp").tempdir().unwrap();
        let tmp_dir = Utf8Path::from_path(tmp_dir.path()).unwrap();
        let public_param_dir = tmp_dir.join("public_params");
        let proof_dir = tmp_dir.join("proofs");
        let commit_dir = tmp_dir.join("commits");
        let lurk_file = tmp_dir.join("prove_verify.lurk");

        let mut file = File::create(lurk_file.clone()).unwrap();
        file.write_all(b"!(prove (+ 1 1))\n").unwrap();
        file.write_all(b"!(verify \"Nova_Pallas_10_049abe0ff3b8c08c6022f44c3da7e27962b4a92af7c204a38976e52c94c9cea6\")\n").unwrap();

        let mut cmd = lurk_cmd();
        cmd.arg("load");
        cmd.arg(lurk_file.into_string());
        cmd.arg("--public-params-dir");
        cmd.arg(public_param_dir);
        cmd.arg("--proofs-dir");
        cmd.arg(proof_dir);
        cmd.arg("--commits-dir");
        cmd.arg(commit_dir);

        cmd.assert().success();
    }
}
