mod cli;

use anyhow::Result;

fn main() -> Result<()> {
    pretty_env_logger::init();
    cli::parse_and_run()
}
