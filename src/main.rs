use anyhow::Result;
use lurk::field::LanguageField;
use lurk::proof::nova;
use lurk::repl::{repl_cli, ReplState};

fn main() -> Result<()> {
    pretty_env_logger::init();

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
        LanguageField::BLS12_381 => repl_cli::<blstrs::Scalar, ReplState<blstrs::Scalar>>(),
        LanguageField::Pallas => repl_cli::<nova::S1, ReplState<nova::S1>>(),
        LanguageField::Vesta => repl_cli::<nova::S2, ReplState<nova::S2>>(),
    }
}
