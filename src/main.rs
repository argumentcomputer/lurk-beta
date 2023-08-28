use anyhow::Result;
use tracing_subscriber::{fmt, prelude::*, EnvFilter, Registry};
use tracing_texray::TeXRayLayer;

fn main() -> Result<()> {
    // this handle should be held until the end of the program,
    // do not replace by let _ = ...
    let _metrics_handle = lurk_metrics::MetricsSink::init();

    let subscriber = Registry::default()
        .with(fmt::layer().pretty())
        .with(EnvFilter::from_default_env())
        .with(TeXRayLayer::new()); // note: we don't `tracing_texray::examine` anything
    tracing::subscriber::set_global_default(subscriber).unwrap();

    println!(
        "commit: {} {}",
        env!("VERGEN_GIT_COMMIT_DATE"),
        env!("VERGEN_GIT_SHA")
    );
    // note: we don't `tracing_texray::examine` here, so no spans are printed
    lurk::cli::parse_and_run()
}
