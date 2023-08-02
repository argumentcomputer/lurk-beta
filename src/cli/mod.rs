mod commitment;
mod field_data;
mod lurk_proof;
mod paths;
mod repl;

use anyhow::{bail, Context, Result};
use clap::{Args, Parser, Subcommand};
use config::{Config, Environment, File};
use pasta_curves::pallas;
#[cfg(not(target_arch = "wasm32"))]
use std::path::Path;
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

#[cfg(not(target_arch = "wasm32"))]
pub mod cache_dirs {
    use std::path::PathBuf;
    use std::sync::OnceLock;

    pub static PUBLIC_PARAM_DIR: OnceLock<PathBuf> = OnceLock::new();
    pub static COMMIT_DIR: OnceLock<PathBuf> = OnceLock::new();
    pub static PROOF_DIR: OnceLock<PathBuf> = OnceLock::new();
}

#[cfg(not(target_arch = "wasm32"))]
pub use cache_dirs::*;

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

    /// Path for cached public parameters
    #[clap(long, value_parser)]
    public_param_path: Option<PathBuf>,

    /// Path for cached proofs
    #[clap(long, value_parser)]
    proof_path: Option<PathBuf>,

    /// Path for cached commitments
    #[clap(long, value_parser)]
    commit_path: Option<PathBuf>,
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
    rc: Option<usize>,

    #[clap(long, value_parser)]
    limit: Option<usize>,

    #[clap(long, value_parser)]
    backend: Option<String>,

    #[clap(long, value_parser)]
    field: Option<String>,

    /// Path for cached public parameters
    #[clap(long, value_parser)]
    public_param_path: Option<PathBuf>,

    /// Path for cached proofs
    #[clap(long, value_parser)]
    proof_path: Option<PathBuf>,

    /// Path for cached commitments
    #[clap(long, value_parser)]
    commit_path: Option<PathBuf>,
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
            public_param_path: self.public_param_path,
            proof_path: self.proof_path,
            commit_path: self.commit_path,
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

    /// Path for cached public parameters
    #[clap(long, value_parser)]
    public_param_path: Option<PathBuf>,

    /// Path for cached proofs
    #[clap(long, value_parser)]
    proof_path: Option<PathBuf>,

    /// Path for cached commitments
    #[clap(long, value_parser)]
    commit_path: Option<PathBuf>,
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
    rc: Option<usize>,

    #[clap(long, value_parser)]
    limit: Option<usize>,

    #[clap(long, value_parser)]
    backend: Option<String>,

    #[clap(long, value_parser)]
    field: Option<String>,

    /// Path for cached public parameters
    #[clap(long, value_parser)]
    public_param_path: Option<PathBuf>,

    /// Path for cached proofs
    #[clap(long, value_parser)]
    proof_path: Option<PathBuf>,

    /// Path for cached commitments
    #[clap(long, value_parser)]
    commit_path: Option<PathBuf>,
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
            public_param_path: self.public_param_path,
            proof_path: self.proof_path,
            commit_path: self.commit_path,
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
        Some(config_path) if config_path.exists() => {
            Config::builder().add_source(File::from(config_path.to_owned()))
        }
        _ => Config::builder(),
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
        #[cfg(not(target_arch = "wasm32"))]
        self.set_lurk_dirs(&config);
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

    #[cfg(not(target_arch = "wasm32"))]
    fn set_lurk_dirs(&self, config: &HashMap<String, String>) {
        let public_param_path = if let Some(path) = &self.public_param_path {
            path.to_owned()
        } else {
            match config.get("public_params") {
                Some(dir) => PathBuf::from(dir),
                None => {
                    let home = home::home_dir().unwrap();
                    home.join(Path::new(".lurk/public_params"))
                }
            }
        };
        let proof_path = if let Some(path) = &self.proof_path {
            path.to_owned()
        } else {
            match config.get("proofs") {
                Some(dir) => PathBuf::from(dir),
                None => PathBuf::from("./proofs"),
            }
        };
        let commit_path = if let Some(path) = &self.commit_path {
            path.to_owned()
        } else {
            match config.get("commits") {
                Some(dir) => PathBuf::from(dir),
                None => PathBuf::from("./commits"),
            }
        };
        PUBLIC_PARAM_DIR.get_or_init(|| public_param_path);
        PROOF_DIR.get_or_init(|| proof_path);
        COMMIT_DIR.get_or_init(|| commit_path);

        paths::non_wasm::create_lurk_dirs().unwrap();
    }
}

impl LoadCli {
    pub fn run(&self) -> Result<()> {
        macro_rules! load {
            ( $rc: expr, $limit: expr, $field: path, $backend: expr ) => {{
                let mut repl = new_repl!(self, $rc, $limit, $field, $backend);
                repl.load_file(&self.lurk_file)?;
                if self.prove {
                    #[cfg(not(target_arch = "wasm32"))]
                    repl.prove_last_frames()?;
                }
                Ok(())
            }};
        }
        let config = get_config(&self.config)?;
        #[cfg(not(target_arch = "wasm32"))]
        self.set_lurk_dirs(&config);
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

    #[cfg(not(target_arch = "wasm32"))]
    fn set_lurk_dirs(&self, config: &HashMap<String, String>) {
        let public_param_path = if let Some(path) = &self.public_param_path {
            path.to_owned()
        } else {
            match config.get("public_params") {
                Some(dir) => PathBuf::from(dir),
                None => {
                    let home = home::home_dir().unwrap();
                    home.join(Path::new(".lurk/public_params"))
                }
            }
        };
        let proof_path = if let Some(path) = &self.proof_path {
            path.to_owned()
        } else {
            match config.get("proofs") {
                Some(dir) => PathBuf::from(dir),
                None => PathBuf::from("./proofs"),
            }
        };
        let commit_path = if let Some(path) = &self.commit_path {
            path.to_owned()
        } else {
            match config.get("commits") {
                Some(dir) => PathBuf::from(dir),
                None => PathBuf::from("./commits"),
            }
        };
        PUBLIC_PARAM_DIR.get_or_init(|| public_param_path);
        PROOF_DIR.get_or_init(|| proof_path);
        COMMIT_DIR.get_or_init(|| commit_path);

        paths::non_wasm::create_lurk_dirs().unwrap();
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
        let config_dir = tmp_dir.path().join("lurk.toml");
        let public_param_dir = tmp_dir.path().join("public_params");
        let proof_dir = tmp_dir.path().join("proofs");
        let commit_dir = tmp_dir.path().join("commits");

        let public_params = public_param_dir.to_str().unwrap();
        let proofs = proof_dir.to_str().unwrap();
        let commits = commit_dir.to_str().unwrap();

        let mut config_file = File::create(&config_dir).unwrap();
        config_file
            .write_all(format!("public_params = \"{}\"\n", public_params).as_bytes())
            .unwrap();
        config_file
            .write_all(format!("proofs = \"{}\"\n", proofs).as_bytes())
            .unwrap();
        config_file
            .write_all(format!("commits = \"{}\"\n", commits).as_bytes())
            .unwrap();

        // Overwrite proof dir with env var
        let proof_dir_env = tmp_dir.path().join("proofs_env");
        let proofs_env = proof_dir_env.to_str().unwrap();

        std::env::set_var("LURK_PROOFS", proofs_env);

        let config = crate::cli::get_config(&Some(config_dir)).unwrap();

        assert_eq!(config.get("public_params").unwrap(), public_params);
        assert_eq!(config.get("proofs").unwrap(), proofs_env);
        assert_eq!(config.get("commits").unwrap(), commits);
    }

    // TODO: Use a snapshot test for the proof ID and/or test the REPL process
    #[test]
    fn test_prove_and_verify() {
        let tmp_dir = Builder::new().prefix("tmp").tempdir().unwrap();
        let public_param_dir = tmp_dir.path().join("public_params");
        let proof_dir = tmp_dir.path().join("proofs");
        let commit_dir = tmp_dir.path().join("commits");
        let lurk_file = &tmp_dir.path().join("prove_verify.lurk");

        let mut file = File::create(lurk_file).unwrap();
        file.write_all(b"!(prove (+ 1 1))\n").unwrap();
        file.write_all(b"!(verify \"Nova_Pallas_10_049abe0ff3b8c08c6022f44c3da7e27962b4a92af7c204a38976e52c94c9cea6\")\n").unwrap();

        let mut cmd = lurk_cmd();
        cmd.arg("load");
        cmd.arg(lurk_file.to_str().unwrap());
        cmd.arg("--public-param-path");
        cmd.arg(public_param_dir);
        cmd.arg("--proof-path");
        cmd.arg(proof_dir);
        cmd.arg("--commit-path");
        cmd.arg(commit_dir);

        cmd.assert().success();
    }
}
