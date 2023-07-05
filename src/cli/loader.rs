use std::path::PathBuf;
use std::sync::Arc;

use anyhow::{bail, Result};

use lurk::coprocessor::Coprocessor;
use lurk::eval::lang::Lang;
use lurk::field::LurkField;
use lurk::ptr::Ptr;
use lurk::public_parameters::Claim;
use lurk::store::Store;

use super::prove_and_verify::prove_claim;

pub struct Loader<F: LurkField, C: Coprocessor<F>> {
    pub store: Store<F>,
    pub env: Ptr<F>,
    pub limit: usize,
    pub lang: Arc<Lang<F, C>>,
    pub last_claim: Option<Claim<F>>,
}

impl<F: LurkField, C: Coprocessor<F>> Loader<F, C> {
    pub fn new(store: Store<F>, env: Ptr<F>, limit: usize) -> Loader<F, C> {
        Loader {
            store,
            env,
            limit,
            lang: Arc::new(Lang::<F, C>::new()),
            last_claim: None,
        }
    }

    pub fn load_file(&mut self, path: &PathBuf) -> Result<()> {
        Ok(())
    }

    pub fn repl(&mut self) -> Result<()> {
        Ok(())
    }

    pub fn prove_last_claim(&mut self) -> Result<()> {
        match &self.last_claim {
            Some(claim) => {
                let _ = prove_claim(&claim);
                Ok(())
            }
            None => {
                bail!("No claim to prove");
            }
        }
    }
}
