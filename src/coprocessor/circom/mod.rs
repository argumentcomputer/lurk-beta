// # Usage of circom coprocessors.
//
// See `examples/circom.rs` for a quick example of how to declare a circom coprocessor.

pub mod error;

/// Some circom features require non WASM platform features, so we seal the API here.
#[cfg(not(target_arch = "wasm32"))]
pub mod non_wasm {
    use core::fmt::Debug;
    use std::fs;
    use std::io::Write;

    use ansi_term::Colour::Red;
    use anyhow::Result;
    use bellpepper_core::{ConstraintSystem, SynthesisError};
    use camino::Utf8PathBuf;
    use circom_scotia::r1cs::CircomConfig;

    use crate::circuit::gadgets::circom::CircomGadgetReference;
    use crate::coprocessor::circom::error::CircomCoprocessorError;
    use crate::{
        circuit::gadgets::{circom::CircomGadget, pointer::AllocatedPtr},
        cli::paths::circom_dir,
        coprocessor::{CoCircuit, Coprocessor},
        field::LurkField,
        lem::{pointers::Ptr, store::Store},
    };

    /// Returns a pretty error prelude for error messages.
    pub(crate) fn error_prelude() -> String {
        format!("{}", Red.bold().paint("error"))
    }

    /// Tries to retrieve a gadget from our local collection. If a corresponding one is found, returns
    /// its static files path in `Some(<r1cs_path>, <wasm_path>)`. Otherwise, returns `None`.
    fn get_local_gadget<F: LurkField, C: CircomGadget<F>>(
        gadget: &C,
    ) -> Result<Option<(Utf8PathBuf, Utf8PathBuf)>, CircomCoprocessorError> {
        return match gadget.reference().confirm_or_create_local(true)? {
            Some(_) => {
                let r1cs = circom_dir()
                    .join(gadget.reference().identifier())
                    .join(gadget.reference().name())
                    .with_extension("r1cs");
                let wasm = circom_dir()
                    .join(gadget.reference().identifier())
                    .join(gadget.reference().name())
                    .with_extension("wasm");

                if r1cs.exists() && wasm.exists() {
                    return Ok(Some((r1cs, wasm)));
                }

                Ok(None)
            }
            None => Ok(None),
        };
    }

    /// Tries to fetch a gadget from a remote Git repository. The repository has to follow our standard
    /// layout to properly work out.
    fn get_remote_gadget<F: LurkField, C: CircomGadget<F>>(
        gadget: &C,
    ) -> Result<Option<(Utf8PathBuf, Utf8PathBuf)>, CircomCoprocessorError> {
        let identifier_as_string = String::from(gadget.reference().identifier());

        // Check that we have a proper version for a remote release. If not, look if gadget repo exist
        // and return error accordingly.
        if gadget.version().is_none() {
            let prelude = error_prelude();

            let response =
                reqwest::blocking::get(format!("https://github.com/{identifier_as_string}"))
                    .map_err(|err| CircomCoprocessorError::RemoteCallFailure {
                        prelude: prelude.clone(),
                        reference: gadget.reference().clone(),
                        source: err.into(),
                    })?;

            if !response.status().is_success() {
                return Err(CircomCoprocessorError::GadgetNotFound {
                    reference: gadget.reference().clone(),
                    name: String::from(gadget.reference().name()),
                    prelude,
                });
            }

            return Err(CircomCoprocessorError::MissingGadgetVersion {
                prelude,
                reference: identifier_as_string.clone(),
            });
        }
        // Check if the targeted directory on file system exists.
        gadget.reference().confirm_or_create_local(true)?;

        let r1cs = circom_dir()
            .join(gadget.reference().identifier())
            .join(gadget.reference().name())
            .with_extension("r1cs");
        let wasm = circom_dir()
            .join(gadget.reference().identifier())
            .join(gadget.reference().name())
            .with_extension("wasm");

        get_from_github(gadget.reference(), gadget.version().unwrap(), "r1cs")?;
        get_from_github(gadget.reference(), gadget.version().unwrap(), "wasm")?;

        Ok(Some((r1cs, wasm)))
    }

    /// Download a named resource from a given release for a given repository on Github.
    fn get_from_github(
        reference: &CircomGadgetReference,
        release: &str,
        extension: &str,
    ) -> Result<(), CircomCoprocessorError> {
        let name = reference.name();
        let identifier = reference.identifier();

        let asset_url = format!(
            "https://github.com/{identifier}/releases/download/{release}/{name}.{extension}"
        );

        let path = circom_dir()
            .join(reference.identifier())
            .join(name)
            .with_extension(extension);

        let response = reqwest::blocking::get(format!(
            "https://github.com/{identifier}/releases/download/{release}/{name}.{extension}"
        ))
        .map_err(|err| CircomCoprocessorError::RemoteCallFailure {
            prelude: error_prelude(),
            reference: reference.clone(),
            source: err.into(),
        })?;

        let mut out =
            fs::File::create(path).map_err(|err| CircomCoprocessorError::AssetCreationFailure {
                prelude: error_prelude(),
                reference: reference.clone(),
                source: err.into(),
            })?;

        let response_byte =
            &response
                .bytes()
                .map_err(|err| CircomCoprocessorError::PayloadProcessingError {
                    prelude: error_prelude(),
                    reference: reference.clone(),
                    source: err.into(),
                    asset_url,
                })?;

        out.write_all(response_byte).map_err(|err| {
            CircomCoprocessorError::AssetCreationFailure {
                prelude: error_prelude(),
                reference: reference.clone(),
                source: err.into(),
            }
        })?;

        Ok(())
    }

    /// Tries to first get gadget static files from a local file system, and on failure tries to fetch
    /// it from a remote Github repository.
    fn get_gadget<F: LurkField, C: CircomGadget<F>>(
        gadget: &C,
    ) -> Result<(Utf8PathBuf, Utf8PathBuf), CircomCoprocessorError> {
        match get_local_gadget(gadget)? {
            Some(paths) => Ok(paths),
            None => match get_remote_gadget(gadget)? {
                Some(paths) => Ok(paths),
                None => Err(CircomCoprocessorError::GadgetNotFound {
                    reference: gadget.reference().clone(),
                    name: String::from(gadget.reference().name()),
                    prelude: error_prelude(),
                }),
            },
        }
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

        fn synthesize_simple<CS: ConstraintSystem<F>>(
            &self,
            cs: &mut CS,
            g: &crate::lem::circuit::GlobalAllocator<F>,
            _s: &Store<F>,
            _not_dummy: &bellpepper_core::boolean::Boolean,
            args: &[AllocatedPtr<F>],
        ) -> std::result::Result<AllocatedPtr<F>, SynthesisError> {
            let input = self.gadget.clone().into_circom_input(args);
            let witness =
                circom_scotia::calculate_witness(&self.config, input, true).map_err(|e| {
                    eprintln!("{:?}", e);
                    SynthesisError::Unsatisfiable
                })?;

            let outputs = circom_scotia::synthesize(cs, self.config.r1cs.clone(), Some(witness))?;

            let mut vec_ptr = Vec::with_capacity(outputs.len());

            for output in outputs {
                let num_tag = g.alloc_tag(cs, &crate::tag::ExprTag::Num);

                vec_ptr.push(AllocatedPtr::from_parts(num_tag.clone(), output));
            }

            //let tag = g.alloc_tag(cs, &crate::tag::ExprTag::)
            //let res = AllocatedPtr::from_parts()

            Ok(vec_ptr[0].clone())
        }
    }

    impl<F: LurkField, C: CircomGadget<F> + Debug> Coprocessor<F> for CircomCoprocessor<F, C> {
        /// TODO: Generalize
        fn eval_arity(&self) -> usize {
            0
        }

        fn evaluate_simple(&self, s: &Store<F>, args: &[Ptr]) -> Ptr {
            self.gadget.evaluate_simple(s, args)
        }

        fn has_circuit(&self) -> bool {
            true
        }
    }

    impl<F: LurkField, C: CircomGadget<F>> CircomCoprocessor<F, C> {
        /// Creates a [CircomConfig] by loading in the r1cs and wasm data. It will first look locally,
        /// then extend the search to a Github repository release if it has not been found.
        pub fn create(gadget: C) -> Result<Self> {
            // First try to get from the file system.
            let (r1cs, wasm) = get_gadget(&gadget)?;

            let config = CircomConfig::<F>::new(wasm, r1cs)?;
            let coprocessor = Self { config, gadget };

            Ok(coprocessor)
        }

        /// Creates a [CircomCoprocessor] and panics if it fails.
        pub fn new(gadget: C) -> Self {
            CircomCoprocessor::create(gadget).unwrap()
        }

        /// The defined reference of this coprocessor, which is just the inner gadget's identifier.
        pub fn name(&self) -> String {
            self.gadget.reference().identifier()
        }
    }
}
