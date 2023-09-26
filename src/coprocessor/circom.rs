// # Usage of circom coprocessors.
//
// See `examples/circom.rs` for a quick example of how to declare a circom coprocessor.

/// Some circom features require non WASM platform features, so we seal the API here.
#[cfg(not(target_arch = "wasm32"))]
pub mod non_wasm {
    use core::fmt::Debug;
    use std::fs::read_dir;

    use ansi_term::Colour::Red;
    use anyhow::{bail, Result};
    use bellpepper::gadgets::boolean::Boolean;
    use bellpepper_core::{ConstraintSystem, SynthesisError};
    use circom_scotia::r1cs::CircomConfig;

    use crate::{
        circuit::gadgets::{
            circom::CircomGadget,
            data::GlobalAllocations,
            pointer::{AllocatedContPtr, AllocatedPtr},
        },
        cli::paths::circom_dir,
        coprocessor::{CoCircuit, Coprocessor},
        field::LurkField,
        lem::{pointers::Ptr as LEMPtr, store::Store as LEMStore, Tag},
        ptr::Ptr,
        store::Store,
    };

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

Then run `lurk coprocessor --name {name} <{}_FOLDER>` to instantiate a new gadget `{name}`.",
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

    /// A concrete instantiation of a [CircomGadget] with a corresponding [CircomConfig] as a coprocessor.
    ///
    /// To create a concrete Coproc from this, simply declare something like this:
    /// ```ignore
    /// #[derive(Clone, Debug, Coproc)]
    /// enum ConcreteCoproc<F: LurkField> {
    ///     SC(CircomCoprocessor<F, ConcreteGadget<F>>),
    /// }
    /// ```
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
            _not_dummy: &Boolean,
        ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError>
        {
            let input = self.gadget.clone().into_circom_input(input_exprs);
            let witness =
                circom_scotia::calculate_witness(&self.config, input, true).map_err(|e| {
                    eprintln!("{:?}", e);
                    SynthesisError::Unsatisfiable
                })?;
            let output = circom_scotia::synthesize(cs, self.config.r1cs.clone(), Some(witness))?;

            let res = AllocatedPtr::from_parts(g.num_tag.clone(), output);

            Ok((res, input_env.clone(), input_cont.clone()))
        }

        fn synthesize_lem_simple<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            g: &crate::lem::circuit::GlobalAllocator<F>,
            _s: &LEMStore<F>,
            _not_dummy: &bellpepper_core::boolean::Boolean,
            args: &[AllocatedPtr<F>],
        ) -> std::result::Result<AllocatedPtr<F>, SynthesisError> {
            let input = self.gadget.clone().into_circom_input(args);
            let witness =
                circom_scotia::calculate_witness(&self.config, input, true).map_err(|e| {
                    eprintln!("{:?}", e);
                    SynthesisError::Unsatisfiable
                })?;
            let output = circom_scotia::synthesize(cs, self.config.r1cs.clone(), Some(witness))?;
            let num_tag = g
                .get_allocated_const(Tag::Expr(crate::tag::ExprTag::Num).to_field())
                .expect("Num tag should have been allocated");
            let res = AllocatedPtr::from_parts(num_tag.clone(), output);

            Ok(res)
        }
    }

    impl<F: LurkField, C: CircomGadget<F> + Debug> Coprocessor<F> for CircomCoprocessor<F, C> {
        /// TODO: Generalize
        fn eval_arity(&self) -> usize {
            0
        }

        fn simple_evaluate(&self, s: &Store<F>, args: &[Ptr<F>]) -> Ptr<F> {
            self.gadget.simple_evaluate(s, args)
        }

        fn evaluate_lem_simple(&self, s: &LEMStore<F>, args: &[LEMPtr<F>]) -> LEMPtr<F> {
            self.gadget.simple_evaluate_lem(s, args)
        }

        fn has_circuit(&self) -> bool {
            true
        }
    }

    impl<F: LurkField, C: CircomGadget<F>> CircomCoprocessor<F, C> {
        /// Creates a [CircomConfig] by loading in the data in `<CIRCOM_DIR>/<gadget.name>/*`
        pub fn create(gadget: C) -> Result<Self> {
            validate_gadget(&gadget)?;

            let name = gadget.name();
            let circom_folder = circom_dir().join(name);

            let r1cs = circom_folder.join(format!("{name}.r1cs"));
            let wasm = circom_folder.join(name).with_extension("wasm");

            let config = CircomConfig::<F>::new(wasm, r1cs)?;
            let coprocessor = Self { config, gadget };

            Ok(coprocessor)
        }

        /// Creates a [CircomCoprocessor] and panics if it fails
        pub fn new(gadget: C) -> Self {
            CircomCoprocessor::create(gadget).unwrap()
        }

        /// The defined name of this coprocessor, which is just the inner gadget's name
        pub fn name(&self) -> &str {
            self.gadget.name()
        }
    }
}
