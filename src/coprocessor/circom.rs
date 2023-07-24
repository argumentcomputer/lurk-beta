//! # Usage of circom coprocessors.
//! 
//! See `examples/circom.rs` for a quick example of how to declare a circom coprocessor.

use core::fmt::Debug;
use std::path::PathBuf;

use anyhow::Result;
use bellperson::{ConstraintSystem, SynthesisError};
use nova_scotia::r1cs::CircomConfig;

use crate::{
    coprocessor::{CoCircuit, Coprocessor},
    field::LurkField,
    ptr::Ptr,
    store::Store, circuit::gadgets::{circom::CircomGadget, data::GlobalAllocations, pointer::{AllocatedPtr, AllocatedContPtr}},
};

/// TODO: fix this duplication with the one in `cli::paths`
fn circom_gadgets() -> PathBuf {
    home::home_dir()
        .expect("no home directory")
        .join(".lurk/circom-gadgets")
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
    ) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedContPtr<F>), SynthesisError> {
        let input = self.gadget.into_circom_input(input_exprs);
        let witness = nova_scotia::calculate_witness(&self.config, input, true).expect("msg");
        let output = nova_scotia::synthesize(cs, self.config.r1cs.clone(), Some(witness))?;

        let res = AllocatedPtr::from_parts(g.num_tag.clone(), output);

        Ok((res, input_env.clone(), input_cont.clone()))
    }
}

impl<F: LurkField, C: CircomGadget<F> + Debug> Coprocessor<F>
    for CircomCoprocessor<F, C>
{
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
    /// TODO: better error handling when name doesn't exist
    /// Should look something like:
    /// ```dead
    /// error: no circom gadget named `foo`.
    /// Available circom gadgets:
    ///     bar
    ///     baz
    /// 
    /// If you want to setup a new circom gadget `foo`, run
    ///     `lurk coprocessor --name foo <FOO_CIRCOM_FOLDER>`
    /// ```
    pub fn create(gadget: C) -> Result<Self> {
        let name = gadget.name();
        let circom_folder = circom_gadgets().join(name);
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