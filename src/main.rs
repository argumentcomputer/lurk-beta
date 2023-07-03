use anyhow::Result;

use lurk::eval::lang::{Coproc, Lang};
use lurk::field::LanguageField;
use lurk::repl::{repl_cli, ReplState};
use pasta_curves::{pallas, vesta};

fn main() -> Result<()> {
    pretty_env_logger::init();

    println!(
        "commit: {} {}",
        env!("VERGEN_GIT_COMMIT_DATE"),
        env!("VERGEN_GIT_SHA")
    );

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
        LanguageField::BLS12_381 => repl_cli::<
            blstrs::Scalar,
            ReplState<blstrs::Scalar, Coproc<blstrs::Scalar>>,
            Coproc<blstrs::Scalar>,
        >(Lang::<blstrs::Scalar, Coproc<blstrs::Scalar>>::new()),
        LanguageField::Pallas => repl_cli::<
            pallas::Scalar,
            ReplState<pallas::Scalar, Coproc<pallas::Scalar>>,
            Coproc<pallas::Scalar>,
        >(Lang::<pallas::Scalar, Coproc<pallas::Scalar>>::new()),
        LanguageField::Vesta => repl_cli::<
            vesta::Scalar,
            ReplState<vesta::Scalar, Coproc<vesta::Scalar>>,
            Coproc<vesta::Scalar>,
        >(Lang::<vesta::Scalar, Coproc<vesta::Scalar>>::new()),
    }
}
