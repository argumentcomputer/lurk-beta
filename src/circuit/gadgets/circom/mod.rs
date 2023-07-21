
use std::path::PathBuf;

use anyhow::Result;
use nova_scotia::r1cs::CircomConfig;

use crate::field::LurkField;

/// TODO: fix this duplication with the one in `cli::paths`
fn circom_gadgets() -> PathBuf {
    home::home_dir().expect("no home directory").join(".lurk/circom-gadgets")
}

/// Creates a CircomConfig by loading in the data in `.lurk/circom-gadgets/<name>/*`
/// TODO: better error handling when name doesn't exist
pub fn create_circom_config<F: LurkField>(name: &str) -> Result<CircomConfig<F>> {
    let circom_folder = circom_gadgets().join(name);
    let r1cs = circom_folder.join(format!("{}.r1cs", name));
    let wasm = circom_folder.join(name).with_extension("wasm");

    let cfg = CircomConfig::<F>::new(wasm, r1cs)?;

    Ok(cfg)
}

// pub trait CircomGadget<F: PrimeField> {
//     type Input;
//     type Output;

//     fn name() -> String;

//     fn into_circom_input(input: Self::Input) -> Vec<(String, Vec<F>)>;

//     fn into_lurk_output(output: Self::Output) -> AllocatedPtr<F>;
// }

