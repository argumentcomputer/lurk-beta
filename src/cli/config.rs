//! Global config for the CLI
//! Includes settings for cache locations and proof backend
use std::collections::HashMap;

use crate::config::{lurk_config_file, Settings, LURK_CONFIG};
use crate::field::LanguageField;
use camino::Utf8PathBuf;
use config::{Config, ConfigError, Environment, File};
use once_cell::sync::OnceCell;
use serde::Deserialize;

use super::backend::Backend;
use super::paths::{circom_default_dir, commits_default_dir, proofs_default_dir};

/// Global config varable for `CliSettings`
pub(crate) static CLI_CONFIG: OnceCell<CliSettings> = OnceCell::new();

/// Gets the `CLI_CONFIG` settings. If uninitialized, sets the global variable
/// in the following order (greatest to least precedence):
/// - `settings` map if provided, e.g. with key ("proofs", "$HOME/lurk-rs/proofs")
///   This contains any CLI args, set e.g. by `lurk --proofs-dir /path/to/proofs_dir`
/// - Env var per setting, e.g. `LURK_PROOFS_DIR`
/// - Config file, which also has a configurable location (see `lurk_config_file()`),
///   and has the following syntax for e.g. TOML:
///   ```toml
///   proofs_dir = "/path/to/proofs_dir"
///   ```
///   Other file formats are supported by the `config` crate, but only TOML is tested
/// - Default values, e.g. `$HOME/.lurk/proofs`
pub(crate) fn cli_config(
    config_file: Option<&Utf8PathBuf>,
    settings: Option<&HashMap<&str, String>>,
) -> &'static CliSettings {
    LURK_CONFIG
        .set(Settings::from_config(lurk_config_file(config_file), settings).unwrap_or_default())
        .unwrap_or(());
    CLI_CONFIG.get_or_init(|| {
        CliSettings::from_config(lurk_config_file(config_file), settings).unwrap_or_default()
    })
}

/// Contains the CLI configuration settings
// NOTE: Config settings share the same file for both the Lurk library and the CLI.
// It's good practice to avoid duplication of shared settings like `public_params_dir`
// in downstream configs like these to prevent conflicts.
#[derive(Debug, Deserialize)]
pub(crate) struct CliSettings {
    /// Cache directory for proofs
    pub(crate) proofs_dir: Utf8PathBuf,
    /// Cache directory for commitments
    pub(crate) commits_dir: Utf8PathBuf,
    /// Cache directory for Circom files
    pub(crate) circom_dir: Utf8PathBuf,
    /// Proof generation and verification system
    pub(crate) backend: Backend,
    /// Finite field used for evaluation and proving
    pub(crate) field: LanguageField,
    /// Reduction count, which is the number of circuit reductions per step
    pub(crate) rc: usize,
    /// Iteration limit for the program, which is arbitrary to user preferences
    /// Used mainly as a safety check, similar to default stack size
    pub(crate) limit: usize,
    /// Maximum number of frames held at once, used to avoid memory overflows
    pub(crate) max_chunk_size: usize,
}

impl CliSettings {
    /// Loads config settings from a file or env var, or CLI arg if applicable
    pub(crate) fn from_config(
        config_file: &Utf8PathBuf,
        cli_settings: Option<&HashMap<&str, String>>,
    ) -> Result<Self, ConfigError> {
        let (proofs, commits, circom, backend, field, rc, limit, max_chunk_size) = (
            "proofs_dir",
            "commits_dir",
            "circom_dir",
            "backend",
            "field",
            "rc",
            "limit",
            "max_chunk_size",
        );
        Config::builder()
            .set_default(proofs, proofs_default_dir().to_string())?
            .set_default(commits, commits_default_dir().to_string())?
            .set_default(circom, circom_default_dir().to_string())?
            .set_default(backend, Backend::default().to_string())?
            .set_default(field, LanguageField::default().to_string())?
            .set_default(rc, 10)?
            .set_default(limit, 100_000_000)?
            .add_source(File::with_name(config_file.as_str()).required(false))
            // Then overwrite with any `LURK` environment variables
            .add_source(Environment::with_prefix("LURK"))
            // TODO: Derive config::Source for `cli_settings` and use `add_source` instead
            .set_override_option(proofs, cli_settings.and_then(|s| s.get(proofs).map(|v| v.to_owned())))?
            .set_override_option(commits, cli_settings.and_then(|s| s.get(commits).map(|v| v.to_owned())))?
            .set_override_option(circom, cli_settings.and_then(|s| s.get(circom).map(|v| v.to_owned())))?
            .set_override_option(backend, cli_settings.and_then(|s| s.get(backend).map(|v| v.to_owned())))?
            .set_override_option(field, cli_settings.and_then(|s| s.get(field).map(|v| v.to_owned())))?
            .set_override_option(rc, cli_settings.and_then(|s| s.get(rc).map(|v| v.to_owned())))?
            .set_override_option(limit, cli_settings.and_then(|s| s.get(limit).map(|v| v.to_owned())))?
            .set_override_option(max_chunk_size, cli_settings.and_then(|s| s.get(max_chunk_size).map(|v| v.to_owned())))?
            .build()
            .and_then(|c| c.try_deserialize())
    }
}

impl Default for CliSettings {
    fn default() -> Self {
        Self {
            proofs_dir: proofs_default_dir(),
            commits_dir: commits_default_dir(),
            circom_dir: circom_default_dir(),
            backend: Backend::default(),
            field: LanguageField::default(),
            rc: 10,
            limit: 100_000_000,
            max_chunk_size: 1_000_000,
        }
    }
}

#[cfg(test)]
mod tests {
    use camino::Utf8Path;
    use std::io::prelude::*;
    use tempfile::Builder;

    use crate::cli::backend::Backend;
    use crate::cli::config::CliSettings;
    use crate::config::Settings;
    use crate::field::LanguageField;

    // Tests a generic config file with identical syntax to that used in `CLI_CONFIG`
    #[test]
    fn test_config_cli() {
        let tmp_dir = Builder::new().prefix("tmp").tempdir().unwrap();
        let tmp_dir = Utf8Path::from_path(tmp_dir.path()).unwrap();
        let config_dir = tmp_dir.join("lurk.toml");
        let public_params_dir = tmp_dir.join("public_params").into_string();
        let proofs_dir = tmp_dir.join("proofs").into_string();
        let commits_dir = tmp_dir.join("commits").into_string();
        let circom_dir = tmp_dir.join("circom").into_string();
        let backend = "Nova";
        let field = "Pallas";
        let rc = 100;
        let limit = 100_000;
        let max_chunk_size = 10_000;

        let mut config_file = std::fs::File::create(config_dir.clone()).unwrap();
        config_file
            .write_all(format!("public_params_dir = \"{public_params_dir}\"\n").as_bytes())
            .unwrap();
        config_file
            .write_all(format!("proofs_dir = \"{proofs_dir}\"\n").as_bytes())
            .unwrap();
        config_file
            .write_all(format!("commits_dir = \"{commits_dir}\"\n").as_bytes())
            .unwrap();
        config_file
            .write_all(format!("circom_dir = \"{circom_dir}\"\n").as_bytes())
            .unwrap();
        config_file
            .write_all(format!("backend = \"{backend}\"\n").as_bytes())
            .unwrap();
        config_file
            .write_all(format!("field = \"{field}\"\n").as_bytes())
            .unwrap();
        config_file
            .write_all(format!("rc = {rc}\n").as_bytes())
            .unwrap();
        config_file
            .write_all(format!("limit = {limit}\n").as_bytes())
            .unwrap();
        config_file
            .write_all(format!("max_chunk_size = {max_chunk_size}\n").as_bytes())
            .unwrap();

        let cli_config = CliSettings::from_config(&config_dir, None).unwrap();
        let lurk_config = Settings::from_config(&config_dir, None).unwrap();
        assert_eq!(lurk_config.public_params_dir, public_params_dir);
        assert_eq!(cli_config.proofs_dir, proofs_dir);
        assert_eq!(cli_config.commits_dir, commits_dir);
        assert_eq!(cli_config.circom_dir, circom_dir);
        assert_eq!(cli_config.backend, Backend::Nova);
        assert_eq!(cli_config.field, LanguageField::Pallas);
        assert_eq!(cli_config.rc, rc);
        assert_eq!(cli_config.limit, limit);
        assert_eq!(cli_config.max_chunk_size, max_chunk_size);
    }
}
