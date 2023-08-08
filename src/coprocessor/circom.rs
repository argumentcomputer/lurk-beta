//! # Usage of circom coprocessors.
//!
//! See `examples/circom.rs` for a quick example of how to declare a circom coprocessor.

#[cfg(not(target_arch = "wasm32"))]
pub mod non_wasm {
    use core::fmt::Debug;
    use std::{fs::read_dir, path::PathBuf};

    use ansi_term::Colour::Red;
    use anyhow::{bail, Result};
    use bellperson::{ConstraintSystem, SynthesisError};
    use circom_scotia::r1cs::CircomConfig;

    use crate::{
        circuit::gadgets::{
            circom::CircomGadget,
            data::GlobalAllocations,
            pointer::{AllocatedContPtr, AllocatedPtr},
        },
        coprocessor::{CoCircuit, Coprocessor},
        field::LurkField,
        ptr::Ptr,
        store::Store,
    };

    /// TODO: fix this duplication with the one in `cli::paths`
    fn circom_dir() -> PathBuf {
        home::home_dir()
            .expect("no home directory")
            .join(".lurk/circom")
    }

    /// To setup a new circom gadget `<NAME>`, place your circom files in a designated folder and
    /// create a file called `<NAME>.circom`. `<CIRCOM_FOLDER>/<NAME>.circom` is the input file
    /// for the `circom` binary; in this file you must declare your circom main component.
    fn print_error(name: &str, available: Vec<String>) -> Result<()> {
        let available = available.join("\n    ");
        bail!(
            "
{}: no circom gadget named `{name}`.
Available circom gadgets:

    {available}

If you want to setup a new circom gadget `{name}`, place your circom files in a designated folder and
create a file called `{name}.circom`. The circom binary expects `{}_FOLDER>/{name}.circom` 
as the input file; in this file you must declare your circom main component.

Then run `lurk coprocessor --name {name} <{}_FOLDER>` to instansiate a new gadget `{name}`.",
            Red.bold().paint("error"),
            name.to_ascii_uppercase(),
            name.to_ascii_uppercase(),
        );
    }

    fn validate_gadget<F: LurkField, C: CircomGadget<F>>(gadget: &C) -> Result<()> {
        if !circom_dir().exists() {
            std::fs::create_dir_all(circom_dir())?;
            return print_error(gadget.name(), vec![]);
        }

        let name = gadget.name();
        let circom_folder = circom_dir().join(name);

        if circom_folder.exists() {
            return Ok(());
        };

        let mut subdirs = Vec::new();

        for entry in read_dir(circom_dir())? {
            let entry = entry?;
            let path = entry.path();

            if path.is_dir() {
                if let Some(dir_name) = path.file_name() {
                    if let Some(dir_name) = dir_name.to_str() {
                        subdirs.push(dir_name.to_string());
                    }
                }
            }
        }

        if subdirs.contains(&gadget.name().into()) {
            return Ok(());
        }

        print_error(gadget.name(), subdirs)
    }

    #[derive(Debug)]
    pub struct CircomCoprocessor<F: LurkField, C: CircomGadget<F>> {
        gadget: C,
        config: CircomConfig<F>,
    }

    impl<F: LurkField, C: CircomGadget<F>> Clone for CircomCoprocessor<F, C> {
        fn clone(&self) -> Self {
            CircomCoprocessor::new(self.gadget.clone())
        }
    }

    impl<F: LurkField, C: CircomGadget<F>> CoCircuit<F> for CircomCoprocessor<F, C> {
        /// TODO: Generalize
        fn arity(&self) -> usize {
            0
        }

        fn synthesize<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            g: &GlobalAllocations<F>,
            _store: &Store<F>,
            input_exprs: &[AllocatedPtr<F>],
            input_env: &AllocatedPtr<F>,
            input_cont: &AllocatedContPtr<F>,
        ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError>
        {
            let input = self.gadget.clone().into_circom_input(input_exprs);
            let witness = circom_scotia::calculate_witness(&self.config, input, true).expect("msg");
            let output = circom_scotia::synthesize(cs, self.config.r1cs.clone(), Some(witness))?;

            let res = AllocatedPtr::from_parts(g.num_tag.clone(), output);

            Ok((res, input_env.clone(), input_cont.clone()))
        }
    }

    impl<F: LurkField, C: CircomGadget<F> + Debug> Coprocessor<F> for CircomCoprocessor<F, C> {
        /// TODO: Generalize
        fn eval_arity(&self) -> usize {
            0
        }

        fn simple_evaluate(&self, s: &mut Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
            self.gadget.simple_evaluate(s, args)
        }

        fn has_circuit(&self) -> bool {
            true
        }
    }

    impl<F: LurkField, C: CircomGadget<F>> CircomCoprocessor<F, C> {
        /// Creates a CircomConfig by loading in the data in `.lurk/circom-gadgets/<name>/*`
        pub fn create(gadget: C) -> Result<Self> {
            validate_gadget(&gadget)?;

            let name = gadget.name();
            let circom_folder = circom_dir().join(name);

            let r1cs = circom_folder.join(format!("{}.r1cs", name));
            let wasm = circom_folder.join(name).with_extension("wasm");

            let config = CircomConfig::<F>::new(wasm, r1cs)?;
            let coprocessor = Self { config, gadget };

            Ok(coprocessor)
        }

        pub fn new(gadget: C) -> Self {
            CircomCoprocessor::create(gadget).unwrap()
        }

        pub fn name(&self) -> &str {
            self.gadget.name()
        }
    }
}
