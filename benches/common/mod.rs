pub(crate) mod fib;

use camino::Utf8PathBuf;
use lurk::cli::paths::lurk_default_dir;
use lurk::config::lurk_config;
use once_cell::sync::Lazy;

/// Edit this path to use a config file specific to benchmarking
/// E.g. `Utf8PathBuf::from("/home/<user>/lurk-rs/lurk-bench.toml");`
pub(crate) static BENCH_CONFIG_PATH: Lazy<Utf8PathBuf> =
    Lazy::new(|| lurk_default_dir().join("lurk.toml"));

/// Sets the config settings with the given file
pub(crate) fn set_bench_config() {
    lurk_config(Some(&BENCH_CONFIG_PATH), None);
}
