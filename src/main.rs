use anyhow::Result;

fn main() -> Result<()> {
    // this handle should be held until the end of the program,
    // do not replace by let _ = ...
    let _metrics_handle = lurk_metrics::MetricsSink::init();
    pretty_env_logger::init();
    lurk::cli::parse_and_run()
}