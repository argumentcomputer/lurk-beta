use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use lurk::{
    cli::{field_data::HasFieldModulus, zstore::ZDag},
    field::LurkField,
    lem::{
        pointers::{Ptr, ZPtr},
        store::Store,
    },
};

#[derive(Serialize, Deserialize)]
pub struct ChainData<F: LurkField> {
    current_callable: ZPtr<F>,
    result: ZPtr<F>,
    next_callable: ZPtr<F>,
    z_dag: ZDag<F>,
}

impl<F: LurkField> ChainData<F> {
    pub fn new(
        current_callable: &Ptr,
        result: &Ptr,
        next_callable: &Ptr,
        store: &Store<F>,
    ) -> Self {
        let cache = &mut HashMap::default();
        let mut z_dag = ZDag::default();
        let current_callable = z_dag.populate_with(current_callable, store, cache);
        let result = z_dag.populate_with(result, store, cache);
        let next_callable = z_dag.populate_with(next_callable, store, cache);
        ChainData {
            current_callable,
            result,
            next_callable,
            z_dag,
        }
    }

    pub fn extract(&self, store: &Store<F>) -> Result<(Ptr, Ptr, Ptr)> {
        let cache = &mut HashMap::default();
        let current_callable = self
            .z_dag
            .populate_store(&self.current_callable, store, cache)?;
        let result = self.z_dag.populate_store(&self.result, store, cache)?;
        let next_callable = self
            .z_dag
            .populate_store(&self.next_callable, store, cache)?;
        Ok((current_callable, result, next_callable))
    }
}

impl<F: LurkField> HasFieldModulus for ChainData<F> {
    fn field_modulus() -> String {
        F::MODULUS.to_string()
    }
}
