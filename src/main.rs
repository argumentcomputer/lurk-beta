mod cli;

use anyhow::Result;

use cli::run_cli;

fn main() -> Result<()> {
    pretty_env_logger::init();
    run_cli()
}
