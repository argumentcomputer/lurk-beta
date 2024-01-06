use ::nova::{supernova::snark::CompressedSNARK, traits::Engine};
use abomonation::{decode, Abomonation};
use std::sync::Arc;

use crate::coprocessor::Coprocessor;
use crate::proof::nova::{self, NovaCircuitShape, PublicParams, C1LEM};
use crate::proof::nova::{CurveCycleEquipped, E1, E2};

pub mod disk_cache;
mod error;
pub mod instance;
mod mem_cache;

use crate::proof::supernova::{self, SuperNovaAuxParams, SuperNovaPublicParams};
use crate::public_parameters::disk_cache::public_params_dir;
use crate::public_parameters::error::Error;

use self::disk_cache::DiskCache;
use self::instance::Instance;

pub fn public_params<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'static>(
    instance: &Instance<'static, F, C>,
) -> Result<Arc<PublicParams<F, C1LEM<'a, F, C>>>, Error>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    let f = |instance: &Instance<'static, F, C>| {
        Arc::new(nova::public_params(instance.rc, instance.lang()))
    };
    mem_cache::PUBLIC_PARAM_MEM_CACHE.get_from_mem_cache_or_update_with(instance, f)
}

/// Attempts to extract abomonated public parameters.
/// To avoid all copying overhead, we zerocopy all of the data within the file;
/// this leads to extremely high performance, but restricts the lifetime of the data
/// to the lifetime of the file. Thus, we cannot pass a reference out and must
/// rely on a closure to capture the data and continue the computation in `bind`.
pub fn with_public_params<'a, F, C, M, Fn, T>(
    instance: &Instance<'a, F, C>,
    bind: Fn,
) -> Result<T, Error>
where
    F: CurveCycleEquipped,
    C: Coprocessor<F> + 'a,
    Fn: FnOnce(&PublicParams<F, C1LEM<'a, F, C>>) -> T,
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    let default = |instance: &Instance<'a, F, C>| nova::public_params(instance.rc, instance.lang());
    let disk_cache = DiskCache::<F, C>::new(public_params_dir()).unwrap();

    let mut bytes = vec![];
    let pp = disk_cache.read_bytes(instance, &mut bytes).and_then(|()| {
        if let Some((pp, remaining)) = unsafe { decode(&mut bytes) } {
            assert!(remaining.is_empty());
            eprintln!("Using disk-cached public params for {}", instance.key());
            Ok(pp)
        } else {
            Err(Error::Cache("failed to decode bytes".into()))
        }
    });

    match pp {
        Ok(pp) => Ok(bind(pp)),
        Err(e) => {
            eprintln!("{e}");
            let pp = default(instance);
            disk_cache.write_abomonated(instance, &pp)?;
            Ok(bind(&pp))
        }
    }
}

pub fn supernova_circuit_params<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>(
    instance: &Instance<'a, F, C>,
) -> Result<NovaCircuitShape<F>, Error>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
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
    instance: &Instance<'a, F, C>,
) -> Result<SuperNovaAuxParams<F>, Error>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    let disk_cache = DiskCache::<F, C>::new(public_params_dir()).unwrap();

    let mut bytes = vec![];
    disk_cache.read_bytes(instance, &mut bytes).and_then(|()| {
        if let Some((aux_params, remaining)) =
            unsafe { decode::<SuperNovaAuxParams<F>>(&mut bytes) }
        {
            assert!(remaining.is_empty());
            Ok(aux_params.clone())
        } else {
            Err(Error::Cache("failed to decode bytes".into()))
        }
    })
}

/// Attempts to extract abomonated public parameters.
pub fn supernova_public_params<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>(
    instance_primary: &Instance<'a, F, C>,
) -> Result<supernova::PublicParams<F, C1LEM<'a, F, C>>, Error>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    let default = |instance: &Instance<'a, F, C>| {
        supernova::public_params::<'a, F, C, C1LEM<'a, F, C>>(instance.rc, instance.lang())
    };
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

        let pp = SuperNovaPublicParams::<F, C1LEM<'a, F, C>>::from_parts_unchecked(
            circuit_params_vec,
            aux_params,
        );
        let (pk, vk) = CompressedSNARK::setup(&pp).unwrap();

        supernova::PublicParams { pp, pk, vk }
    } else {
        println!("generating running claim params");
        let pp = default(instance_primary);

        let (circuit_params_vec, aux_params) = pp.pp.into_parts();

        disk_cache.write_abomonated(instance_primary, &aux_params)?;

        for (circuit_index, circuit_params) in circuit_params_vec.iter().enumerate() {
            let instance = instance_primary.reindex(circuit_index);
            disk_cache.write_abomonated(&instance, circuit_params)?;
        }

        let pp = SuperNovaPublicParams::<F, C1LEM<'a, F, C>>::from_parts_unchecked(
            circuit_params_vec,
            aux_params,
        );
        let (pk, vk) = CompressedSNARK::setup(&pp).unwrap();

        supernova::PublicParams { pp, pk, vk }
    };

    Ok(pp)
}

#[cfg(test)]
mod tests {
    use super::{instance::Kind, *};
    use crate::eval::lang::{Coproc, Lang};
    use pasta_curves::pallas::Scalar as S1;
    use tempfile::Builder;

    #[test]
    // Note: No Eq instance for PublicParams currently, just testing disk read/write
    fn serde_public_params_roundtrip() {
        let tmp_dir = Builder::new().prefix("tmp").tempdir().unwrap();
        std::env::set_var("LURK_PUBLIC_PARAMS", tmp_dir.path());

        let lang: Arc<Lang<S1, Coproc<S1>>> = Arc::new(Lang::new());
        let instance = Instance::new(10, lang, true, Kind::NovaPublicParams);
        // Without disk cache, writes to tmpfile
        let _public_params = public_params::<S1, Coproc<S1>>(&instance).unwrap();
        // With disk cache, reads from tmpfile
        let _public_params = public_params::<S1, Coproc<S1>>(&instance).unwrap();
    }
}
