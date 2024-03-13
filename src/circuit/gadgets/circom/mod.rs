//! # Usage of circom coprocessors.
//!
//! See `examples/keccak.rs` for a quick example of how to declare a circom coprocessor.

use crate::cli::paths::circom_dir;
use crate::coprocessor::circom::error::CircomCoprocessorError;
use crate::{
    field::LurkField,
    lem::{pointers::Ptr, store::Store},
};
use anyhow::{bail, Result};
use bellpepper_core::{ConstraintSystem, SynthesisError};
use camino::Utf8PathBuf;
use circom_scotia::r1cs::CircomInput;
use std::fmt::{Debug, Display, Formatter};

use super::pointer::AllocatedPtr;

/// An interface to declare a new type of Circom gadget.
/// It requires 3 things:
///  1. The user defined [`CircomGadgetReference`] of the gadget. This _must_ have a format of <AUTHOR>/<NAME>.
///     The reference _must_ either exist into the  file system (loaded via the CLI with
///     `lurk coprocessor --name <NAME> <CIRCOM_FOLDER>`) or be a valid gadget repository following
///     our standard layout.
///  2. The desired release of the gadget to use. This is only relevant when dealing with remote gadget,
///     not for gadget only existing on the file system.
///  3. A defined way to take a list of Lurk input pointers and turn them into a Circom input. We do not enforce the shapes
///     of either the Lurk end or the Circom end, so users should take care to define what shape they expect.
///  4. A defined way *Lurk* should evaluate what this gadget does. This is then the implementation used in the
///     `Coprocessor` trait.
pub trait CircomGadget<F: LurkField>: Send + Sync + Clone {
    fn reference(&self) -> &CircomGadgetReference;

    fn version(&self) -> Option<&str> {
        None
    }

    fn into_circom_input<CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
        g: &crate::lem::circuit::GlobalAllocator<F>,
        s: &Store<F>,
        not_dummy: &bellpepper_core::boolean::Boolean,
        input: &[AllocatedPtr<F>],
    ) -> Result<Vec<CircomInput<F>>, SynthesisError>;

    fn evaluate_simple(&self, s: &Store<F>, args: &[Ptr]) -> Ptr;

    fn arity(&self) -> usize;
}

#[derive(Clone, Default)]
pub struct CircomGadgetReference {
    author: String,
    name: String,
}

impl CircomGadgetReference {
    pub fn new(reference: &str) -> Result<Self> {
        let reference_split: Vec<&str> = reference.split('/').collect();
        if reference_split.len() != 2
            || reference_split[0].is_empty()
            || reference_split[1].is_empty()
        {
            bail!("Expected a reference of format \"<AUTHOR>/<NAME>\", got \"{reference}\"");
        }

        Ok(Self {
            author: reference_split[0].parse()?,
            name: reference_split[1].parse()?,
        })
    }

    pub fn identifier(&self) -> String {
        format!("{}/{}", self.author, self.name)
    }

    pub fn author(&self) -> &str {
        &self.author
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn confirm_or_create_local(
        &self,
        create_if_missing: bool,
    ) -> Result<Option<Utf8PathBuf>, CircomCoprocessorError> {
        let gadget_dir = circom_dir().join(self.identifier());

        if !gadget_dir.exists() && !create_if_missing {
            return Ok(None);
        } else if !gadget_dir.exists() && create_if_missing {
            std::fs::create_dir_all(&gadget_dir).map_err(|err| {
                CircomCoprocessorError::AssetCreationFailure {
                    prelude: String::from("error"),
                    reference: self.clone(),
                    source: err.into(),
                }
            })?;

            return Ok(None);
        }

        Ok(Some(gadget_dir))
    }
}

impl Display for CircomGadgetReference {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.author, &self.name)
    }
}

impl Debug for CircomGadgetReference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CircomGadgetReference")
            .field("author", &self.author)
            .field("name", &self.name)
            .finish()
    }
}
