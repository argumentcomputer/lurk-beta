//! Global config for Lurk
//! Includes settings for cache locations, public parameters, and parallelism.
use std::collections::HashMap;

use camino::Utf8PathBuf;
use config::{Config, ConfigError, Environment, File};
use once_cell::sync::OnceCell;
use serde::Deserialize;

use crate::cli::paths::lurk_default_dir;

/// Global config variable for `Settings`
pub static LURK_CONFIG: OnceCell<Settings> = OnceCell::new();

/// Global path variable for configuration file
pub static LURK_CONFIG_FILE: OnceCell<Utf8PathBuf> = OnceCell::new();

/// Gets the `LURK_CONFIG` settings. If uninitialized, sets the global variable
/// in the following order (greatest to least precedence):
/// - `settings` map if provided, e.g. with key ("public_params_dir", "$HOME/lurk-rs/public_params")
/// - Env var per setting, e.g. `LURK_PUBLIC_PARAMS_DIR`
/// - Config file, which also has a configurable location (see `lurk_config_file()`),
///   and has the following syntax for e.g. TOML:
///   ```toml
///   public_params_dir = "/path/to/params"
///   ```
///   Other file formats are supported by the `config` crate, but only TOML is tested
/// - Default values, e.g. `$HOME/.lurk/public_params`
pub fn lurk_config(
    file: Option<&Utf8PathBuf>,
    settings: Option<&HashMap<&str, String>>,
) -> &'static Settings {
    LURK_CONFIG
        .get_or_init(|| Settings::from_config(lurk_config_file(file), settings).unwrap_or_default())
}

/// Gets the `LURK_CONFIG_FILE` path. If uninitialized, sets the global variable
/// in the following order (greatest to least precedence):
/// - `config_file` parameter if provided, e.g. "$HOME/lurk-rs/lurk-local.toml"
/// - `LURK_CONFIG_FILE` env var
/// - Default location at `$HOME/.lurk/lurk.toml` or `<current_dir>/.config/lurk.toml` on WASM.
pub fn lurk_config_file(config_file: Option<&Utf8PathBuf>) -> &'static Utf8PathBuf {
    LURK_CONFIG_FILE.get_or_init(|| {
        if let Some(file) = config_file {
            file.clone()
        } else if let Ok(file) = std::env::var("LURK_CONFIG_FILE") {
            Utf8PathBuf::from(file)
        } else {
            lurk_default_dir().join("lurk.toml")
        }
    })
}

/// Contains the Lurk config settings
/// The `public_params_dir` setting can also be overriden by a CLI arg if in use
#[derive(Debug, Deserialize, PartialEq, Eq)]
pub struct Settings {
    /// Public parameter disk cache location
    pub public_params_dir: Utf8PathBuf,

    /// Parallelism & witness gen configs
    pub perf: PerfConfig,
}

impl Settings {
    /// Loads config settings from a file or env vars
    /// The public parameter disk cache can also be overriden by a CLI arg if applicable
    pub fn from_config(
        config_file: &Utf8PathBuf,
        settings: Option<&HashMap<&str, String>>,
    ) -> Result<Self, ConfigError> {
        let public_params = "public_params_dir";
        // Settings are read first to last, in order of increasing precedence.
        // Hence, default values must come first so they are overriden by all other methods.
        Config::builder()
            // Default settings if unspecified in the config file
            .set_default(public_params, public_params_default_dir().to_string())?
            .set_default("perf", "fully-sequential".to_string())?
            .add_source(File::with_name(config_file.as_str()).required(false))
            // Then override with any `LURK` environment variables
            .add_source(Environment::with_prefix("LURK"))
            // Optionally override if settings were specified via CLI arg
            .set_override_option(public_params, settings.and_then(|s| s.get(public_params).map(|v| v.to_owned())))?
            .build()
            .and_then(|c| c.try_deserialize())
    }
}

impl Default for Settings {
    fn default() -> Self {
        Self {
            public_params_dir: public_params_default_dir(),
            perf: PerfConfig::default(),
        }
    }
}

pub fn public_params_default_dir() -> Utf8PathBuf {
    #[cfg(not(target_arch = "wasm32"))]
    let params_path = home_dir();
    #[cfg(target_arch = "wasm32")]
    let params_path = Utf8PathBuf::new();
    params_path.join(".lurk/public_params")
}

// TODO: Should we crash if the user has no home dir?
/// Returns the home directory used by `cargo`` and `rustup`
#[cfg(not(target_arch = "wasm32"))]
pub fn home_dir() -> Utf8PathBuf {
    Utf8PathBuf::from_path_buf(home::home_dir().expect("missing home directory"))
        .expect("path contains invalid Unicode")
}

/// Performance-related configuration settings
#[derive(Default, Debug, PartialEq, Eq, Deserialize)]
#[serde(from = "CannedConfig")]
pub struct PerfConfig {
    /// Parallelism settings
    pub parallelism: ParallelConfig,
    /// Witness generation settings
    pub witness_generation: WitnessGeneration,
}

impl PerfConfig {
    fn fully_sequential() -> Self {
        Self {
            parallelism: ParallelConfig {
                recursive_steps: Flow::Sequential,
                synthesis: Flow::Sequential,
                poseidon_witnesses: Flow::Sequential,
            },
            witness_generation: WitnessGeneration {
                precompute_neptune: false,
            },
        }
    }

    fn max_parallel_simple() -> Self {
        Self {
            parallelism: ParallelConfig {
                recursive_steps: Flow::Parallel,
                synthesis: Flow::Parallel,
                poseidon_witnesses: Flow::Parallel,
            },
            witness_generation: WitnessGeneration {
                precompute_neptune: true,
            },
        }
    }

    fn parallel_synthesis() -> Self {
        Self {
            parallelism: ParallelConfig {
                recursive_steps: Flow::Parallel,
                synthesis: Flow::Parallel,
                poseidon_witnesses: Flow::Sequential,
            },
            witness_generation: WitnessGeneration {
                precompute_neptune: true,
            },
        }
    }

    fn parallel_steps_only() -> Self {
        Self {
            parallelism: ParallelConfig {
                recursive_steps: Flow::Parallel,
                synthesis: Flow::Sequential,
                poseidon_witnesses: Flow::Sequential,
            },
            witness_generation: WitnessGeneration {
                precompute_neptune: true,
            },
        }
    }
}

/// Parallel configuration settings
#[derive(Default, Debug, PartialEq, Eq)]
pub struct ParallelConfig {
    /// Multiple `StepCircuit`s.
    pub recursive_steps: Flow,
    /// Synthesis (within one `StepCircuit`)
    pub synthesis: Flow,
    /// The poseidon witness part of synthesis.
    pub poseidon_witnesses: Flow,
}

/// Should we use optimized witness-generation when possible?
#[derive(Debug, Default, PartialEq, Eq)]
pub struct WitnessGeneration {
    /// NOTE: Neptune itself *will* do this transparently at the level of individual hashes, where possible.
    /// so this configuration is only required for higher-level decisions.
    pub precompute_neptune: bool,
}

/// The level of parallelism used when synthesizing the Lurk circuit
#[derive(Default, Debug, PartialEq, Eq)]
pub enum Flow {
    /// Runs without parallelism (default)
    #[default]
    Sequential,
    /// Try to be smart about thread management based on # of cpus
    Parallel,
    /// How many threads to use? (Advisory, might be ignored.)
    ParallelN(usize),
}

impl Flow {
    /// Returns `true` on `Flow::Sequential`
    pub fn is_sequential(&self) -> bool {
        matches!(self, Self::Sequential)
    }

    /// Returns `true` on `Flow::Parallel` or `Flow::ParallelN`
    pub fn is_parallel(&self) -> bool {
        !self.is_sequential()
    }

    /// Returns the number of parallel threads to run
    pub fn num_threads(&self) -> usize {
        match self {
            Self::Sequential => 1,
            Self::Parallel => num_cpus::get(),
            Self::ParallelN(threads) => *threads,
        }
    }
}

/// Shortcut to easily set `PerfConfig`
#[derive(Debug, Default, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum CannedConfig {
    #[default]
    FullySequential,
    MaxParallelSimple,
    ParallelStepsOnly,
    ParallelSynthesis,
}

impl From<CannedConfig> for PerfConfig {
    fn from(canned: CannedConfig) -> Self {
        match canned {
            CannedConfig::FullySequential => Self::fully_sequential(),
            CannedConfig::MaxParallelSimple => Self::max_parallel_simple(),
            CannedConfig::ParallelSynthesis => Self::parallel_synthesis(),
            CannedConfig::ParallelStepsOnly => Self::parallel_steps_only(),
        }
    }
}

#[cfg(test)]
mod tests {
    use camino::Utf8Path;
    use std::io::prelude::*;
    use std::{collections::HashMap, fs::File};
    use tempfile::Builder;

    use crate::config::{CannedConfig, PerfConfig, Settings};

    // Tests a generic config file with identical syntax to that used in `LURK_CONFIG`
    // Doesn't test `OnceCell` behavior as the tests seem to share memory
    #[test]
    fn test_config_lurk() {
        let tmp_dir = Builder::new().prefix("tmp").tempdir().unwrap();
        let tmp_dir = Utf8Path::from_path(tmp_dir.path()).unwrap();
        let config_dir = tmp_dir.join("lurk.toml");
        let public_params_dir = tmp_dir.join("public_params").into_string();
        let perf_config = PerfConfig::from(CannedConfig::MaxParallelSimple);

        let mut config_file = File::create(config_dir.clone()).unwrap();
        config_file
            .write_all(format!("public_params_dir = \"{public_params_dir}\"\n").as_bytes())
            .unwrap();
        config_file
            .write_all("perf = \"max-parallel-simple\"\n".as_bytes())
            .unwrap();

        let config = Settings::from_config(&config_dir, None).unwrap();

        assert_eq!(config.public_params_dir, public_params_dir);
        assert_eq!(config.perf, perf_config);
    }

    // Tests overwriting the config file and CLI argument
    // Doesn't test env var as it can overwrite other tests when run in parallel
    #[test]
    fn test_config_override() {
        let tmp_dir = Builder::new().prefix("tmp").tempdir().unwrap();
        let tmp_dir = Utf8Path::from_path(tmp_dir.path()).unwrap();
        let config_dir = tmp_dir.join("lurk.toml");
        let public_params_dir = tmp_dir.join("public_params").into_string();

        let mut config_file = File::create(config_dir.clone()).unwrap();
        config_file
            .write_all(format!("public_params_dir = \"{public_params_dir}\"\n").as_bytes())
            .unwrap();
        config_file
            .write_all("perf = \"parallel-steps-only\"\n".as_bytes())
            .unwrap();

        // Overwrite public params dir to simulate CLI setting
        let public_params_dir_cli = tmp_dir.join("public_params_cli");
        let mut overrides = HashMap::new();
        overrides.insert("public_params_dir", public_params_dir_cli.to_string());

        let config = Settings::from_config(&config_dir, Some(&overrides)).unwrap();

        assert_eq!(config.public_params_dir, public_params_dir_cli);
        assert_eq!(config.perf, PerfConfig::parallel_steps_only());
    }

    // Tests that duplicate config keys result in an error
    #[test]
    fn test_config_duplicate() {
        let tmp_dir = Builder::new().prefix("tmp").tempdir().unwrap();
        let tmp_dir = Utf8Path::from_path(tmp_dir.path()).unwrap();
        let config_dir = tmp_dir.join("lurk.toml");
        let public_params_dir = tmp_dir.join("public_params").into_string();
        let public_params_dir_dup = tmp_dir.join("public_params_dup").into_string();

        let mut config_file = File::create(config_dir.clone()).unwrap();
        config_file
            .write_all(format!("public_params_dir = \"{public_params_dir}\"\n").as_bytes())
            .unwrap();
        config_file
            .write_all(format!("public_params_dir = \"{public_params_dir_dup}\"\n").as_bytes())
            .unwrap();

        assert!(Settings::from_config(&config_dir, None).is_err())
    }
}
