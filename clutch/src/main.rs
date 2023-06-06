use anyhow::Result;

use clutch::ClutchState;

use lurk::eval::lang::{Coproc, Lang};
use lurk::field::LanguageField;
use lurk::repl::repl_cli;
use pasta_curves::pallas;

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
        LanguageField::Pallas => repl_cli::<
            pallas::Scalar,
            ClutchState<pallas::Scalar, Coproc<pallas::Scalar>>,
            Coproc<pallas::Scalar>,
        >(Lang::<pallas::Scalar, Coproc<pallas::Scalar>>::new()),
        // TODO: Support all LanguageFields.
        // LanguageField::BLS12_381 => repl_cli::<
        //     blstrs::Scalar,
        //     ClutchState<blstrs::Scalar, Coproc<blstrs::Scalar>>,
        //     Coproc<blstrs::Scalar>,
        // >(Lang::<blstrs::Scalar, Coproc<blstrs::Scalar>>::new()),
        // LanguageField::Vesta => repl_cli::<
        //     vesta::Scalar,
        //     ClutchState<vesta::Scalar, Coproc<vesta::Scalar>>,
        //     Coproc<vesta::Scalar>,
        // >(Lang::<vesta::Scalar, Coproc<vesta::Scalar>>::new()),
        _ => panic!("unsupported field"),
    }
}
