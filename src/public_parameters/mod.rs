use ::nova::traits::Engine;
use ::nova::{CommitmentKey, CommitmentKeyParams};
use abomonation::{decode, Abomonation};
use once_cell::sync::OnceCell;

use crate::coprocessor::Coprocessor;
use crate::proof::nova::{self, NovaCircuitShape, NovaAuxParams, NovaPublicParams, C1LEM};
use crate::proof::nova::{CurveCycleEquipped, E1, E2};

pub mod disk_cache;
mod error;
pub mod instance;

use crate::proof::supernova::{self, SuperNovaAuxParams, SuperNovaPublicParams};
use crate::public_parameters::disk_cache::{public_params_dir, DiskCache};
use crate::public_parameters::error::Error;
use crate::public_parameters::instance::Instance;

pub fn nova_aux_params<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>(
    instance: &Instance<F, C>,
) -> Result<NovaAuxParams<F>, Error>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    let disk_cache = DiskCache::<F, C>::new(public_params_dir()).unwrap();

    let mut bytes = vec![];
    disk_cache.read_bytes(instance, &mut bytes).and_then(|()| {
        if let Some((aux_params, remaining)) =
            unsafe { decode::<NovaAuxParams<F>>(&mut bytes) }
        {
            assert!(remaining.is_empty());
            Ok(aux_params.clone())
        } else {
            Err(Error::Cache("failed to decode bytes".into()))
        }
    })
}

/// Attempts to extract abomonated public parameters.
pub fn public_params<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>(
    instance_primary: &Instance<F, C>,
) -> Result<nova::PublicParams<F, C1LEM<'a, F, C>>, Error>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    let default = |instance: &Instance<F, C>| {
        nova::public_params::<'a, F, C>(instance.rc, instance.lang())
    };
    let disk_cache = DiskCache::<F, C>::new(public_params_dir()).unwrap();

    let maybe_circuit_params_vec = instance_primary
        .circuit_param_instances()
        .iter()
        .map(|instance| circuit_params::<F, C>(instance))
        .collect::<Result<Vec<NovaCircuitShape<F>>, _>>();

    let maybe_aux_params = nova_aux_params::<F, C>(instance_primary);

    let pp = if let (Ok(mut circuit_params_vec), Ok(aux_params)) =
        (maybe_circuit_params_vec, maybe_aux_params)
    {
        let (primary, secondary) = Instance::<F, C>::new_cks(
            aux_params.ck_primary_len,
            aux_params.ck_secondary_len,
            instance_primary.abomonated,
        );
        let ck_params = commitment_key_params(&primary, &secondary)?;
        let pp = NovaPublicParams::<F, C1LEM<'a, F, C>>::from_parts(
            circuit_params_vec.remove(0), // there should only be one element
            ck_params,
            aux_params,
        );

        nova::PublicParams::from(pp)
    } else {
        let pp = default(instance_primary);

        let (circuit_shape, ck_params, aux_params) = pp.pp.into_parts();

        disk_cache.write_abomonated(instance_primary, &aux_params)?;

        let (primary, secondary) = Instance::new_cks(
            aux_params.ck_primary_len,
            aux_params.ck_secondary_len,
            instance_primary.abomonated,
        );
        disk_cache.write_abomonated(&primary, &ck_params.primary)?;
        disk_cache.write_abomonated(&secondary, &ck_params.secondary)?;

        let instance = instance_primary.reindex(0);
        disk_cache.write_abomonated(&instance, &circuit_shape)?;

        let pp = NovaPublicParams::<F, C1LEM<'a, F, C>>::from_parts(
            circuit_shape,
            ck_params,
            aux_params,
        );

        nova::PublicParams::from(pp)
    };

    Ok(pp)
}

pub fn commitment_key_params<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>(
    primary: &Instance<F, C>,
    secondary: &Instance<F, C>,
) -> Result<CommitmentKeyParams<E1<F>, E2<F>>, Error>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    let disk_cache = DiskCache::<F, C>::new(public_params_dir()).unwrap();

    let mut bytes = vec![];
    let ck_primary = disk_cache.read_bytes(primary, &mut bytes).and_then(|()| {
        if let Some((pp, remaining)) = unsafe { decode::<CommitmentKey<E1<F>>>(&mut bytes) } {
            assert!(remaining.is_empty());
            eprintln!("Using disk-cached commitment key for {}", primary.key());
            Ok(pp.clone())
        } else {
            Err(Error::Cache("failed to decode bytes".into()))
        }
    })?;
    let ck_secondary = disk_cache
        .read_bytes(secondary, &mut bytes)
        .and_then(|()| {
            if let Some((pp, remaining)) = unsafe { decode::<CommitmentKey<E2<F>>>(&mut bytes) } {
                assert!(remaining.is_empty());
                eprintln!("Using disk-cached commitment key for {}", secondary.key());
                Ok(pp.clone())
            } else {
                Err(Error::Cache("failed to decode bytes".into()))
            }
        })?;
    Ok(CommitmentKeyParams {
        primary: ck_primary,
        secondary: ck_secondary,
    })
}

pub fn circuit_params<'a, F: CurveCycleEquipped, C: Coprocessor<F> + 'a>(
    instance: &Instance<F, C>,
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
            eprintln!("Using disk-cached circuit params for {}", instance.key());
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
    instance_primary: &Instance<F, C>,
) -> Result<supernova::PublicParams<F, C1LEM<'a, F, C>>, Error>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    let default = |instance: &Instance<F, C>| {
        supernova::public_params::<'a, F, C>(instance.rc, instance.lang())
    };
    let disk_cache = DiskCache::<F, C>::new(public_params_dir()).unwrap();

    let maybe_circuit_params_vec = instance_primary
        .circuit_param_instances()
        .iter()
        .map(|instance| circuit_params::<F, C>(instance))
        .collect::<Result<Vec<NovaCircuitShape<F>>, _>>();

    let maybe_aux_params = supernova_aux_params::<F, C>(instance_primary);

    let pp = if let (Ok(circuit_params_vec), Ok(aux_params)) =
        (maybe_circuit_params_vec, maybe_aux_params)
    {
        let (primary, secondary) = Instance::<F, C>::new_cks(
            aux_params.ck_primary_len,
            aux_params.ck_secondary_len,
            instance_primary.abomonated,
        );
        let ck_params = commitment_key_params(&primary, &secondary)?;
        let pp = SuperNovaPublicParams::<F, C1LEM<'a, F, C>>::from_parts_unchecked(
            circuit_params_vec,
            ck_params,
            aux_params,
        );

        supernova::PublicParams {
            pp,
            pk_and_vk: OnceCell::new(),
        }
    } else {
        let pp = default(instance_primary);

        let (circuit_params_vec, ck_params, aux_params) = pp.pp.into_parts();

        disk_cache.write_abomonated(instance_primary, &aux_params)?;

        let (primary, secondary) = Instance::<F, C>::new_cks(
            aux_params.ck_primary_len,
            aux_params.ck_secondary_len,
            instance_primary.abomonated,
        );
        disk_cache.write_abomonated(&primary, &ck_params.primary)?;
        disk_cache.write_abomonated(&secondary, &ck_params.secondary)?;

        for (circuit_index, circuit_params) in circuit_params_vec.iter().enumerate() {
            let instance = instance_primary.reindex(circuit_index);
            disk_cache.write_abomonated(&instance, circuit_params)?;
        }

        let pp = SuperNovaPublicParams::<F, C1LEM<'a, F, C>>::from_parts_unchecked(
            circuit_params_vec,
            ck_params,
            aux_params,
        );

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

        let lang: Arc<Lang<S1, Coproc<S1>>> = Arc::new(Lang::new());
        let instance = Instance::new(10, lang, true, Kind::NovaPublicParams);
        // Without disk cache, writes to tmpfile
        let _public_params = public_params::<S1, Coproc<S1>>(&instance).unwrap();
        // With disk cache, reads from tmpfile
        let _public_params = public_params::<S1, Coproc<S1>>(&instance).unwrap();
    }
}
