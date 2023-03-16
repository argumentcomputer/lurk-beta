use anyhow::Result;

use clutch::ClutchState;

use lurk::field::LanguageField;
use lurk::proof::nova;
use lurk::repl::repl_cli;

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
        LanguageField::Pallas => repl_cli::<nova::S1, ClutchState<nova::S1>>(),
        _ => panic!("unsupported field"),
    }
}
