use anyhow::Result;
use nova::supernova::snark::CompressedSNARK;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use lurk::{
    cli::{field_data::HasFieldModulus, zstore::ZDag},
    field::LurkField,
    lem::{
        pointers::{Ptr, ZPtr},
        store::Store,
    },
    proof::{
        nova::{CurveCycleEquipped, E1},
        supernova::{SS1, SS2},
    },
};

#[derive(Serialize, Deserialize)]
pub struct ConfigResponseData<F: LurkField> {
    rc: usize,
    callable: ZPtr<F>,
    stream_init_callable: Option<ZPtr<F>>,
    z_dag: ZDag<F>,
}

impl<F: LurkField> ConfigResponseData<F> {
    pub fn new(
        rc: usize,
        callable: &Ptr,
        stream_init_callable: Option<&Ptr>,
        store: &Store<F>,
    ) -> Self {
        let mut z_dag = ZDag::default();
        let cache = &mut HashMap::default();
        let callable = z_dag.populate_with(callable, store, cache);
        let stream_init_callable =
            stream_init_callable.map(|x| z_dag.populate_with(x, store, cache));
        Self {
            rc,
            callable,
            stream_init_callable,
            z_dag,
        }
    }

    pub fn interned(&self, store: &Store<F>) -> Result<(Ptr, Option<Ptr>)> {
        let cache = &mut HashMap::default();
        let callable = self.z_dag.populate_store(&self.callable, store, cache)?;
        let stream_init_callable = if let Some(z_ptr) = &self.stream_init_callable {
            Some(self.z_dag.populate_store(z_ptr, store, cache)?)
        } else {
            None
        };
        Ok((callable, stream_init_callable))
    }

    #[inline]
    pub fn get_rc(&self) -> usize {
        self.rc
    }
}

impl<F: LurkField> HasFieldModulus for ConfigResponseData<F> {
    fn field_modulus() -> String {
        F::MODULUS.to_string()
    }
}

#[derive(Serialize, Deserialize)]
pub struct ChainRequestData<F: LurkField> {
    callable: ZPtr<F>,
    argument: ZPtr<F>,
    z_dag: ZDag<F>,
}

impl<F: LurkField> ChainRequestData<F> {
    pub fn new(callable: &Ptr, argument: &Ptr, store: &Store<F>) -> Self {
        let cache = &mut HashMap::default();
        let mut z_dag = ZDag::default();
        let callable = z_dag.populate_with(callable, store, cache);
        let argument = z_dag.populate_with(argument, store, cache);
        Self {
            callable,
            argument,
            z_dag,
        }
    }

    pub fn interned(&self, store: &Store<F>) -> Result<(Ptr, Ptr)> {
        let cache = &mut HashMap::default();
        let callable = self.z_dag.populate_store(&self.callable, store, cache)?;
        let argument = self.z_dag.populate_store(&self.argument, store, cache)?;
        Ok((callable, argument))
    }
}

impl<F: CurveCycleEquipped> HasFieldModulus for ChainRequestData<F> {
    fn field_modulus() -> String {
        F::MODULUS.to_string()
    }
}

#[derive(Serialize, Deserialize)]
pub struct ChainResponseData<F: CurveCycleEquipped> {
    result: ZPtr<F>,
    next_callable: ZPtr<F>,
    z_dag: ZDag<F>,
    proof: CompressedSNARK<E1<F>, SS1<F>, SS2<F>>,
}

impl<F: CurveCycleEquipped> ChainResponseData<F> {
    pub fn new(
        result: &Ptr,
        next_callable: &Ptr,
        store: &Store<F>,
        proof: CompressedSNARK<E1<F>, SS1<F>, SS2<F>>,
    ) -> Self {
        let cache = &mut HashMap::default();
        let mut z_dag = ZDag::default();
        let result = z_dag.populate_with(result, store, cache);
        let next_callable = z_dag.populate_with(next_callable, store, cache);
        Self {
            result,
            next_callable,
            z_dag,
            proof,
        }
    }

    pub fn interned(&self, store: &Store<F>) -> Result<(Ptr, Ptr)> {
        let cache = &mut HashMap::default();
        let result = self.z_dag.populate_store(&self.result, store, cache)?;
        let next_callable = self
            .z_dag
            .populate_store(&self.next_callable, store, cache)?;
        Ok((result, next_callable))
    }

    #[inline]
    pub fn get_proof(&self) -> &CompressedSNARK<E1<F>, SS1<F>, SS2<F>> {
        &self.proof
    }
}

impl<F: CurveCycleEquipped> HasFieldModulus for ChainResponseData<F> {
    fn field_modulus() -> String {
        F::MODULUS.to_string()
    }
}
