mod backend;
mod circom;
mod commitment;
mod config;
pub mod field_data;
pub mod lurk_proof;
pub mod paths;
mod repl;
mod zstore;

use anyhow::{bail, Context, Result};
use camino::Utf8PathBuf;
use clap::{Args, Parser, Subcommand};
use pasta_curves::pallas;

use std::{
    collections::HashMap,
    fs::{self, read_dir},
    io::BufReader,
    path::PathBuf,
};

use crate::{
    eval::lang::Coproc,
    field::{LanguageField, LurkField},
    lem::{multiframe::MultiFrame, store::Store},
    public_parameters::disk_cache::public_params_dir,
    public_parameters::instance::Metadata,
};

use crate::cli::{
    backend::Backend,
    config::cli_config,
    paths::create_lurk_dirs,
    repl::{validate_non_zero, Repl},
    zstore::ZStore,
};

use self::{field_data::load, lurk_proof::PackedLurkProof};

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
    /// Inspects a Lurk proof
    Inspect(InspectArgs),
    /// Instantiates a new circom gadget to interface with bellpepper.
    ///
    /// See `lurk circom --help` for more details
    #[command(verbatim_doc_comment)]
    Circom(CircomArgs),
    PublicParams(PublicParamArgs),
    /// Packs a proof on a file to be shared
    Pack(PackArgs),
    /// Unpacks a proof into Lurk's internal data storage
    Unpack(UnpackArgs),
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
    #[clap(long, value_enum)]
    backend: Option<Backend>,

    /// Arithmetic field (defaults to the backend's standard field)
    #[clap(long, value_enum)]
    field: Option<LanguageField>,

    /// Path to public parameters directory
    #[clap(long, value_parser)]
    public_params_dir: Option<Utf8PathBuf>,

    /// Path to proofs directory
    #[clap(long, value_parser)]
    proofs_dir: Option<Utf8PathBuf>,

    /// Path to commitments directory
    #[clap(long, value_parser)]
    commits_dir: Option<Utf8PathBuf>,

    /// Path to circom directory
    #[clap(long, value_parser)]
    circom_dir: Option<Utf8PathBuf>,

    /// Flag to load the file in demo mode
    #[arg(long)]
    demo: bool,
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

    #[clap(long, value_enum)]
    backend: Option<Backend>,

    #[clap(long, value_enum)]
    field: Option<LanguageField>,

    #[clap(long, value_parser)]
    public_params_dir: Option<Utf8PathBuf>,

    #[clap(long, value_parser)]
    proofs_dir: Option<Utf8PathBuf>,

    #[clap(long, value_parser)]
    commits_dir: Option<Utf8PathBuf>,

    #[clap(long, value_parser)]
    circom_dir: Option<Utf8PathBuf>,

    #[arg(long)]
    demo: bool,
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
            circom_dir: self.circom_dir,
            demo: self.demo,
        }
    }
}

#[derive(Args, Debug)]
struct ReplArgs {
    /// Optional file to be loaded before entering the REPL
    #[clap(long, value_parser)]
    load: Option<Utf8PathBuf>,

    /// ZStore to be preloaded before entering the REPL (and loading a file)
    #[clap(long, value_parser)]
    zstore: Option<Utf8PathBuf>,

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
    #[clap(long, value_enum)]
    backend: Option<Backend>,

    /// Arithmetic field (defaults to the backend's standard field)
    #[clap(long, value_enum)]
    field: Option<LanguageField>,

    /// Path to public parameters directory
    #[clap(long, value_parser)]
    public_params_dir: Option<Utf8PathBuf>,

    /// Path to proofs directory
    #[clap(long, value_parser)]
    proofs_dir: Option<Utf8PathBuf>,

    /// Path to commitments directory
    #[clap(long, value_parser)]
    commits_dir: Option<Utf8PathBuf>,

    /// Path to circom directory
    #[clap(long, value_parser)]
    circom_dir: Option<Utf8PathBuf>,
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

    #[clap(long, value_enum)]
    backend: Option<Backend>,

    #[clap(long, value_enum)]
    field: Option<LanguageField>,

    #[clap(long, value_parser)]
    public_params_dir: Option<Utf8PathBuf>,

    #[clap(long, value_parser)]
    proofs_dir: Option<Utf8PathBuf>,

    #[clap(long, value_parser)]
    commits_dir: Option<Utf8PathBuf>,

    #[clap(long, value_parser)]
    circom_dir: Option<Utf8PathBuf>,
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
            circom_dir: self.circom_dir,
        }
    }
}

fn parse_filename(file: &str) -> Result<Utf8PathBuf> {
    if file == "help" {
        bail!("help is not a valid filename. printing help console instead");
    }
    let path: Utf8PathBuf = file.into();
    Ok(path)
}

fn get_store<F: LurkField + for<'a> serde::de::Deserialize<'a>>(
    z_store_path: &Option<Utf8PathBuf>,
) -> Result<Store<F>> {
    match z_store_path {
        None => Ok(Store::default()),
        Some(z_store_path) => {
            let z_store: ZStore<F> = load(z_store_path)?;
            z_store.to_store()
        }
    }
}

macro_rules! new_repl {
    ( $cli: expr, $rc: expr, $limit: expr, $field: path, $backend: expr ) => {{
        let store = get_store(&$cli.zstore).with_context(|| "reading store from file")?;
        Repl::<$field>::new(store, $rc, $limit, $backend)
    }};
}

impl ReplCli {
    fn run(&self) -> Result<()> {
        macro_rules! repl {
            ( $rc: expr, $limit: expr, $field: path, $backend: expr ) => {{
                let mut repl = new_repl!(self, $rc, $limit, $field, $backend);
                if let Some(lurk_file) = &self.load {
                    repl.load_file(lurk_file, false)?;
                }
                repl.start()
            }};
        }
        macro_rules! map_insert {
            ( $map:expr, $( $field:ident ),* ) => {
                $(
                    if let Some(val) = &self.$field {
                       $map.insert(stringify!($field), val.to_string());
                    }
                )*
            };
        }
        let mut cli_settings: HashMap<&str, String> = HashMap::new();
        map_insert!(
            &mut cli_settings,
            public_params_dir,
            proofs_dir,
            commits_dir,
            circom_dir,
            backend,
            field,
            rc,
            limit
        );

        // Initializes CLI config with CLI arguments as overrides
        let config = cli_config(self.config.as_ref(), Some(&cli_settings));

        create_lurk_dirs().unwrap();

        let rc = config.rc;
        let limit = config.limit;
        let backend = &config.backend;
        let field = &config.field;
        validate_non_zero("rc", rc)?;
        backend.validate_field(field)?;
        match field {
            LanguageField::Pallas => repl!(rc, limit, pallas::Scalar, backend.clone()),
            LanguageField::Vesta => todo!(),
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
                repl.load_file(&self.lurk_file, self.demo)?;
                if self.prove {
                    repl.prove_last_frames()?;
                }
                Ok(())
            }};
        }
        macro_rules! map_insert {
            ( $map:expr, $( $field:ident ),* ) => {
                $(
                    if let Some(val) = &self.$field {
                       $map.insert(stringify!($field), val.to_string());
                    }
                )*
            };
        }
        let mut cli_settings: HashMap<&str, String> = HashMap::new();
        map_insert!(
            &mut cli_settings,
            public_params_dir,
            proofs_dir,
            commits_dir,
            circom_dir,
            backend,
            field,
            rc,
            limit
        );

        // Initializes CLI config with CLI arguments as overrides
        let config = cli_config(self.config.as_ref(), Some(&cli_settings));

        create_lurk_dirs()?;

        let rc = config.rc;
        let limit = config.limit;
        let backend = &config.backend;
        let field = &config.field;
        validate_non_zero("rc", rc)?;
        backend.validate_field(field)?;
        match field {
            LanguageField::Pallas => load!(rc, limit, pallas::Scalar, backend.clone()),
            LanguageField::Vesta => todo!(),
            LanguageField::BN256 => todo!(),
            LanguageField::Grumpkin => todo!(),
        }
    }
}

#[derive(Args, Debug)]
struct VerifyArgs {
    /// Key of the proof to be verified
    #[clap(value_parser)]
    proof_key: String,

    /// Path to public parameters directory
    #[clap(long, value_parser)]
    public_params_dir: Option<Utf8PathBuf>,

    /// Path to proofs directory
    #[clap(long, value_parser)]
    proofs_dir: Option<Utf8PathBuf>,

    /// Config file, containing the lowest precedence parameters
    #[clap(long, value_parser)]
    config: Option<Utf8PathBuf>,
}

#[derive(Args, Debug)]
struct InspectArgs {
    /// Key of the proof to be inspected
    #[clap(value_parser)]
    proof_key: String,

    /// Flag to show the entire proof meta-data
    #[arg(long)]
    full: bool,

    /// Path to proofs directory
    #[clap(long, value_parser)]
    proofs_dir: Option<Utf8PathBuf>,
}

/// To setup a new circom gadget `<NAME>`, place your circom files in a designated folder and
/// create a file called `<NAME>.circom`. `<CIRCOM_FOLDER>/<NAME>.circom` is the input file
/// for the `circom` binary; in this file you must declare your circom main component.
///
/// Then run `lurk circom --name <NAME> <CIRCOM_FOLDER>` to instantiate a new gadget `<NAME>`.
/// The new components are stored in `<CIRCOM_DIR>/<NAME>/*`.
#[derive(Args, Debug)]
struct CircomArgs {
    /// Path to the circom folder to be integrated.
    /// Lurk will look for `<CIRCOM_FOLDER>/<NAME>.circom`
    /// as the input file for the `circom` binary.
    #[clap(value_parser)]
    #[arg(verbatim_doc_comment)]
    circom_folder: Utf8PathBuf,

    /// The name of the circom gadget (the name cannot be `main`, see circom documentation)
    #[clap(long, value_parser)]
    name: String,

    /// Path to circom directory
    #[clap(long, value_parser)]
    circom_dir: Option<Utf8PathBuf>,

    /// Config file, containing the lowest precedence parameters
    #[clap(long, value_parser)]
    config: Option<Utf8PathBuf>,
}

#[derive(Args, Debug)]
struct PublicParamArgs {
    /// Lists all the cached params
    #[arg(long)]
    list: bool,

    /// Clears everything
    #[arg(long)]
    clean: bool,

    /// Remove specified params from cache
    #[clap(long, value_parser)]
    remove: Option<String>,

    /// Show specified params configurations
    #[clap(long, value_parser)]
    show: Option<String>,

    /// Path to public params directory
    #[clap(long, value_parser)]
    public_params_dir: Option<Utf8PathBuf>,

    /// Config file, containing the lowest precedence parameters
    #[clap(long, value_parser)]
    config: Option<Utf8PathBuf>,
}

impl PublicParamArgs {
    fn get_metadata(&self) -> Result<Vec<(PathBuf, Metadata)>> {
        let mut subdirs = Vec::new();

        for entry in read_dir(public_params_dir())? {
            let entry = entry?;
            let path = entry.path();
            if let Some(ex) = path.extension() {
                if ex == "json" {
                    let metadata_file = std::fs::File::open(&path)?;

                    let reader = BufReader::new(metadata_file);
                    let metadata: Metadata = serde_json::from_reader(reader)?;
                    subdirs.push((path, metadata));
                }
            }
        }

        subdirs.sort_by_key(|(_, data)| (data.lang.clone(), data.rc));
        Ok(subdirs)
    }

    fn clean(&self) -> Result<()> {
        for entry in read_dir(public_params_dir())? {
            fs::remove_file(entry?.path())?;
        }
        Ok(())
    }

    fn run(&self) -> Result<()> {
        if self.list {
            let metadata = self.get_metadata()?;
            for (_path, data) in metadata.iter() {
                println!(
                    "{: <9} {: >4} {: >6} {: >35}",
                    &data.cache_key[2..10],
                    data.rc,
                    data.abomonated,
                    data.lang
                );
            }
        }
        if let Some(key) = &self.remove {
            let metadata = self.get_metadata()?;
            if let Some((json_path, _)) = metadata
                .iter()
                .find(|(_, data)| &data.cache_key[2..10] == key)
            {
                let path = json_path.with_extension("");
                fs::remove_file(path)?;
                fs::remove_file(json_path)?;
                println!("cached param `{key}` removed");
            }
        }
        if let Some(key) = &self.show {
            let metadata = self.get_metadata()?;
            if let Some((json_path, data)) = metadata
                .iter()
                .find(|(_, data)| &data.cache_key[2..10] == key)
            {
                let path = json_path.with_extension("");
                println!("cached param `{path:?}`;");
                println!("{:?}", data);
            }
        }
        if self.clean {
            self.clean()?;
            println!("public param cache cleaned");
        }
        Ok(())
    }
}

#[derive(Args, Debug)]
struct PackArgs {
    /// Key of the proof to be packed
    #[clap(value_parser)]
    proof_key: String,

    /// Path to the packed proof output
    #[clap(long, short = 'o', value_parser)]
    output: Utf8PathBuf,

    /// Flag to exclude meta data
    #[arg(long)]
    exclude_meta: bool,

    /// Flag to include envs in the meta data. Irrelevant if exclude_meta is true
    #[arg(long)]
    include_envs: bool,

    /// Path to proofs directory
    #[clap(long, value_parser)]
    proofs_dir: Option<Utf8PathBuf>,

    /// Config file, containing the lowest precedence parameters
    #[clap(long, value_parser)]
    config: Option<Utf8PathBuf>,
}

#[derive(Args, Debug)]
struct UnpackArgs {
    /// Packed proof path
    #[clap(value_parser)]
    proof_path: Utf8PathBuf,

    /// Path to public parameters directory
    #[clap(long, value_parser)]
    public_params_dir: Option<Utf8PathBuf>,

    /// Path to proofs directory
    #[clap(long, value_parser)]
    proofs_dir: Option<Utf8PathBuf>,

    /// Config file, containing the lowest precedence parameters
    #[clap(long, value_parser)]
    config: Option<Utf8PathBuf>,
}

impl Cli {
    fn run(self) -> Result<()> {
        match self.command {
            Command::Repl(repl_args) => repl_args.into_cli().run(),
            Command::Load(load_args) => load_args.into_cli().run(),
            #[allow(unused_variables)]
            Command::Verify(verify_args) => {
                use crate::cli::lurk_proof::LurkProof;
                let mut cli_settings = HashMap::new();
                if let Some(dir) = verify_args.public_params_dir {
                    cli_settings.insert("public_params_dir", dir.to_string());
                }
                if let Some(dir) = verify_args.proofs_dir {
                    cli_settings.insert("proofs_dir", dir.to_string());
                }
                cli_config(verify_args.config.as_ref(), Some(&cli_settings));

                LurkProof::<_, _, MultiFrame<'_, _, Coproc<pallas::Scalar>>>::verify_proof(
                    &verify_args.proof_key,
                )
            }
            #[allow(unused_variables)]
            Command::Inspect(inspect_args) => {
                use crate::cli::lurk_proof::LurkProofMeta;
                let mut cli_settings = HashMap::new();
                if let Some(dir) = inspect_args.proofs_dir {
                    cli_settings.insert("proofs_dir", dir.to_string());
                }
                cli_config(None, Some(&cli_settings));

                LurkProofMeta::<pallas::Scalar>::inspect_proof(
                    &inspect_args.proof_key,
                    None,
                    inspect_args.full,
                )
            }
            Command::Circom(circom_args) => {
                use crate::cli::circom::create_circom_gadget;
                if circom_args.name == "main" {
                    bail!("Circom gadget name cannot be `main`, see circom documentation")
                }
                let mut cli_settings = HashMap::new();
                if let Some(dir) = circom_args.circom_dir {
                    cli_settings.insert("circom_dir", dir.to_string());
                }
                cli_config(circom_args.config.as_ref(), Some(&cli_settings));

                create_circom_gadget(&circom_args.circom_folder, &circom_args.name)
            }
            Command::PublicParams(public_params_args) => {
                let mut cli_settings = HashMap::new();
                if let Some(dir) = public_params_args.public_params_dir.clone() {
                    cli_settings.insert("public_params_dir", dir.to_string());
                }

                cli_config(public_params_args.config.as_ref(), Some(&cli_settings));

                create_lurk_dirs()?;
                public_params_args.run()
            }
            Command::Pack(pack_args) => {
                let mut cli_settings = HashMap::new();
                if let Some(dir) = pack_args.proofs_dir {
                    cli_settings.insert("proofs_dir", dir.to_string());
                }
                cli_config(pack_args.config.as_ref(), Some(&cli_settings));
                PackedLurkProof::<_, _, MultiFrame<'_, _, Coproc<pallas::Scalar>>>::pack(
                    pack_args.proof_key,
                    &pack_args.output,
                    pack_args.exclude_meta,
                    pack_args.include_envs,
                )
            }
            Command::Unpack(unpack_args) => {
                let mut cli_settings = HashMap::new();
                if let Some(dir) = unpack_args.public_params_dir {
                    cli_settings.insert("public_params_dir", dir.to_string());
                }
                if let Some(dir) = unpack_args.proofs_dir {
                    cli_settings.insert("proofs_dir", dir.to_string());
                }
                cli_config(unpack_args.config.as_ref(), Some(&cli_settings));
                create_lurk_dirs()?;
                PackedLurkProof::<_, _, MultiFrame<'_, _, Coproc<pallas::Scalar>>>::unpack(
                    &unpack_args.proof_path,
                )
            }
        }
    }
}

// TODO: deal with `clap_verbosity_flag` and set logger here instead?
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
