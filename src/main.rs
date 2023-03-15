use anyhow::Result;
use lurk::field::LanguageField;
use lurk::proof::nova;
use lurk::repl::{repl, ReplState};

use clap::{Arg, ArgAction, Command};

fn main() -> Result<()> {
    pretty_env_logger::init();

    let matches = Command::new("Lurk REPL")
        .arg(
            Arg::new("lurk_file")
                .help("Lurk file to run")
                .action(ArgAction::Set)
                .value_name("LURKFILE")
                .index(1)
                .help("Specifies the path of a lurk file to run"),
        )
        .arg(
            Arg::new("lightstore")
                .long("lightstore")
                .value_parser(clap::builder::NonEmptyStringValueParser::new())
                .action(ArgAction::Set)
                .value_name("LIGHTSTORE")
                .help("Specifies the lightstore file path"),
        )
        .get_matches();

    let lurk_file = matches.get_one::<String>("lurk_file");
    let lightstore_file = matches.get_one::<String>("lightstore");

    let default_field = LanguageField::Pallas;
    let field = if let Ok(lurk_field) = std::env::var("LURK_FIELD") {
        match lurk_field.as_str() {
            "BLS12-381" => LanguageField::BLS12_381,
            "PALLAS" => LanguageField::Pallas,
            "VESTA" => LanguageField::Vesta,
            _ => default_field,
        }
    } else {
        default_field
    };

    match field {
        LanguageField::BLS12_381 => {
            repl::<_, blstrs::Scalar, ReplState<blstrs::Scalar>>(lurk_file, lightstore_file)
        }
        LanguageField::Pallas => {
            repl::<_, nova::S1, ReplState<nova::S1>>(lurk_file, lightstore_file)
        }
        LanguageField::Vesta => {
            repl::<_, nova::S2, ReplState<nova::S2>>(lurk_file, lightstore_file)
        }
    }
}
