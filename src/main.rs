use anyhow::Result;
use once_cell::sync::OnceCell;

use lurk::eval::lang::Lang;
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
        LanguageField::BLS12_381 => {
            repl_cli::<blstrs::Scalar, ReplState<blstrs::Scalar>>(Lang::<blstrs::Scalar>::new())
        }
        LanguageField::Pallas => repl_cli::<nova::S1, ReplState<nova::S1>>(Lang::<nova::S1>::new()),
        LanguageField::Vesta => repl_cli::<nova::S2, ReplState<nova::S2>>(Lang::<nova::S2>::new()),
    }
}
