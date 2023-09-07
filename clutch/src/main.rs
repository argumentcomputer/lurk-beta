use anyhow::Result;

use clutch::ClutchState;

use lurk::eval::lang::{Coproc, Lang};
use lurk::field::LanguageField;
use lurk::repl::repl_cli;
use pasta_curves::pallas;
use tracing_subscriber::{fmt, prelude::*, EnvFilter, Registry};

fn main() -> Result<()> {
    let subscriber = Registry::default()
        // TODO: correctly filter log level with `clap_verbosity_flag`
        .with(fmt::layer().pretty())
        .with(EnvFilter::from_default_env());
    tracing::subscriber::set_global_default(subscriber).unwrap();

    let default_field = LanguageField::Pallas;
    let field = match std::env::var("LURK_FIELD").as_deref() {
        Ok("BLS12-381") => LanguageField::BLS12_381,
        Ok("PALLAS") => LanguageField::Pallas,
        Ok("VESTA") => LanguageField::Vesta,
        _ => default_field,
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
