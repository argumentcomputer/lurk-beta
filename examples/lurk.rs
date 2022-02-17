use anyhow::Result;
use flexi_logger::Logger;
use lurk::repl::repl;

fn main() -> Result<()> {
    Logger::try_with_str("info")?.start()?;

    // If an argument is passed, treat is as a Lurk file to run.
    let mut args = std::env::args();
    let lurk_file = if args.len() > 1 {
        Some(args.nth(1).expect("Lurk file missing"))
    } else {
        None
    };

    repl(lurk_file.as_ref().map(|x| &**x))
}
