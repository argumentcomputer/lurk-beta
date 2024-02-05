use ::nova::{supernova::FlatAuxParams, FlatPublicParams};
use abomonation::{decode, Abomonation};
use once_cell::sync::OnceCell;
use tap::TapFallible;
use tracing::{info, warn};

use crate::coprocessor::Coprocessor;
use crate::proof::nova::{self, NovaCircuitShape, NovaPublicParams, PublicParams};
use crate::proof::nova::{CurveCycleEquipped, Dual, E1};

pub mod disk_cache;
mod error;
pub mod instance;

use crate::proof::supernova::{self, SuperNovaAuxParams, SuperNovaPublicParams};
use crate::public_parameters::disk_cache::{public_params_dir, DiskCache};
use crate::public_parameters::error::Error;
use crate::public_parameters::instance::Instance;

pub fn public_params<F: CurveCycleEquipped, C: Coprocessor<F>>(
    instance: &Instance<F, C>,
) -> Result<PublicParams<F>, Error>
where
    <F as ff::PrimeField>::Repr: Abomonation,
    <Dual<F> as ff::PrimeField>::Repr: Abomonation,
{
    let default = |instance: &Instance<F, C>| nova::public_params(instance.rc, instance.lang());

    // subdirectory search
    let disk_cache = DiskCache::new(public_params_dir()).unwrap();

    // read the file if it exists, otherwise initialize
    if instance.abomonated {
        let mut bytes = vec![];
        match disk_cache.read_bytes(instance, &mut bytes) {
            Ok(()) => {
                info!("loading abomonated {}", instance.key());
                let (pp, rest) = unsafe { decode::<FlatPublicParams<E1<F>>>(&mut bytes).unwrap() };
                assert!(rest.is_empty());
                let pp = PublicParams::from(NovaPublicParams::<F>::from(pp.clone())); // this clone is VERY expensive
                Ok(pp)
            }
            Err(Error::IO(e)) => {
                warn!("{e}");
                info!("Generating fresh public parameters");
                let pp = default(instance);
                let fp = FlatPublicParams::try_from(pp.pp).unwrap();
                // maybe just directly write
                disk_cache
                    .write_abomonated(instance, &fp)
                    .tap_ok(|_| info!("writing public params to disk-cache: {}", instance.key()))
                    .map_err(|e| Error::Cache(format!("Disk write error: {e}")))?;
                Ok(PublicParams::from(NovaPublicParams::<F>::from(fp)))
            }
            _ => unreachable!(),
        }
    } else {
        // read the file if it exists, otherwise initialize
        if let Ok(pp) = disk_cache.read(instance) {
            info!("loading abomonated {}", instance.key());
            Ok(pp)
        } else {
            let pp = default(instance);
            disk_cache
                .write(instance, &pp)
                .tap_ok(|_| info!("writing public params to disk-cache: {}", instance.key()))
                .map_err(|e| Error::Cache(format!("Disk write error: {e}")))?;
            Ok(pp)
        }
    }
}

pub fn supernova_circuit_params<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>(
    instance: &Instance<F, C>,
) -> Result<NovaCircuitShape<F>, Error>
where
    <F as ff::PrimeField>::Repr: Abomonation,
    <Dual<F> as ff::PrimeField>::Repr: Abomonation,
{
    let disk_cache = DiskCache::<F, C>::new(public_params_dir()).unwrap();

    let mut bytes = vec![];
    disk_cache.read_bytes(instance, &mut bytes).and_then(|()| {
        if let Some((pp, remaining)) = unsafe { decode::<NovaCircuitShape<F>>(&mut bytes) } {
            assert!(remaining.is_empty());
            eprintln!("Using disk-cached public params for {}", instance.key());
            Ok(pp.clone())
        } else {
            Err(Error::Cache("failed to decode bytes".into()))
        }
    })
}

pub fn supernova_aux_params<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>(
    instance: &Instance<F, C>,
) -> Result<SuperNovaAuxParams<F>, Error>
where
    <F as ff::PrimeField>::Repr: Abomonation,
    <Dual<F> as ff::PrimeField>::Repr: Abomonation,
{
    let disk_cache = DiskCache::<F, C>::new(public_params_dir()).unwrap();

    let mut bytes = vec![];
    disk_cache.read_bytes(instance, &mut bytes).and_then(|()| {
        if let Some((flat_aux_params, remaining)) =
            unsafe { decode::<FlatAuxParams<E1<F>>>(&mut bytes) }
        {
            assert!(remaining.is_empty());
            Ok(SuperNovaAuxParams::<F>::from(flat_aux_params.clone()))
        } else {
            Err(Error::Cache("failed to decode bytes".into()))
        }
    })
}

/// Attempts to extract abomonated public parameters.
pub fn supernova_public_params<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>(
    instance_primary: &Instance<F, C>,
) -> Result<supernova::PublicParams<F>, Error>
where
    <F as ff::PrimeField>::Repr: Abomonation,
    <Dual<F> as ff::PrimeField>::Repr: Abomonation,
{
    let default =
        |instance: &Instance<F, C>| supernova::public_params::<F, C>(instance.rc, instance.lang());
    let disk_cache = DiskCache::<F, C>::new(public_params_dir()).unwrap();

    let maybe_circuit_params_vec = instance_primary
        .circuit_param_instances()
        .iter()
        .map(|instance| supernova_circuit_params::<F, C>(instance))
        .collect::<Result<Vec<NovaCircuitShape<F>>, _>>();

    let maybe_aux_params = supernova_aux_params::<F, C>(instance_primary);

    let pp = if let (Ok(circuit_params_vec), Ok(aux_params)) =
        (maybe_circuit_params_vec, maybe_aux_params)
    {
        println!("generating public params");

        let pp = SuperNovaPublicParams::<F>::from_parts_unchecked(circuit_params_vec, aux_params);

        supernova::PublicParams {
            pp,
            pk_and_vk: OnceCell::new(),
        }
    } else {
        println!("generating running claim params");
        let pp = default(instance_primary);

        let (circuit_params_vec, aux_params) = pp.pp.into_parts();

        let flat_aux_params = FlatAuxParams::<E1<F>>::try_from(aux_params).unwrap();
        disk_cache.write_abomonated(instance_primary, &flat_aux_params)?;
        let aux_params = SuperNovaAuxParams::<F>::from(flat_aux_params);

        for (circuit_index, circuit_params) in circuit_params_vec.iter().enumerate() {
            let instance = instance_primary.reindex(circuit_index);
            disk_cache.write_abomonated(&instance, circuit_params)?;
        }

        let pp = SuperNovaPublicParams::<F>::from_parts_unchecked(circuit_params_vec, aux_params);

        supernova::PublicParams {
            pp,
            pk_and_vk: OnceCell::new(),
        }
    };

    Ok(pp)
}

#[cfg(test)]
mod tests {
    use super::{instance::Kind, *};
    use crate::eval::lang::{Coproc, Lang};
    use halo2curves::bn256::Fr as S1;
    use std::sync::Arc;
    use tempfile::Builder;

    #[test]
    // Note: No Eq instance for PublicParams currently, just testing disk read/write
    fn serde_public_params_roundtrip() {
        let tmp_dir = Builder::new().prefix("tmp").tempdir().unwrap();
        std::env::set_var("LURK_PUBLIC_PARAMS", tmp_dir.path());

        let lang: Arc<Lang<S1>> = Arc::new(Lang::new());
        let instance = Instance::new(10, lang, true, Kind::NovaPublicParams);
        // Without disk cache, writes to tmpfile
        let _public_params = public_params::<S1, Coproc<S1>>(&instance).unwrap();
        // With disk cache, reads from tmpfile
        let _public_params = public_params::<S1, Coproc<S1>>(&instance).unwrap();
    }
}
