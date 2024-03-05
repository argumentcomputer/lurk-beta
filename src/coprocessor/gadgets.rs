//! Helper gadgets for synthesis

use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};
use neptune::circuit2::poseidon_hash_allocated as poseidon_hash;
use std::borrow::Borrow;

use crate::{
    circuit::gadgets::{
        constraints::{boolean_to_num, implies_equal},
        pointer::AllocatedPtr,
    },
    field::LurkField,
    lem::{
        circuit::GlobalAllocator,
        pointers::{Ptr, ZPtr},
        store::{expect_ptrs, Store},
        tag,
    },
    tag::{ExprTag, Tag},
};

/// Constructs an `AllocatedPtr` compound by two others
#[allow(dead_code)]
pub(crate) fn construct_tuple2<F: LurkField, CS: ConstraintSystem<F>, T: Tag>(
    cs: &mut CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    tag: &T,
    a: &AllocatedPtr<F>,
    b: &AllocatedPtr<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let tag = g.alloc_tag_cloned(cs, tag);

    let hash = poseidon_hash(
        cs,
        vec![
            a.tag().clone(),
            a.hash().clone(),
            b.tag().clone(),
            b.hash().clone(),
        ],
        store.poseidon_cache.constants.c4(),
    )?;

    Ok(AllocatedPtr::from_parts(tag, hash))
}

/// Constructs an `AllocatedPtr` compound by three others
#[allow(dead_code)]
pub(crate) fn construct_tuple3<F: LurkField, CS: ConstraintSystem<F>, T: Tag>(
    cs: &mut CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    tag: &T,
    a: &AllocatedPtr<F>,
    b: &AllocatedPtr<F>,
    c: &AllocatedPtr<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let tag = g.alloc_tag_cloned(cs, tag);

    let hash = poseidon_hash(
        cs,
        vec![
            a.tag().clone(),
            a.hash().clone(),
            b.tag().clone(),
            b.hash().clone(),
            c.tag().clone(),
            c.hash().clone(),
        ],
        store.poseidon_cache.constants.c6(),
    )?;

    Ok(AllocatedPtr::from_parts(tag, hash))
}

/// Constructs an `AllocatedPtr` compound by four others
#[allow(dead_code)]
pub(crate) fn construct_tuple4<F: LurkField, CS: ConstraintSystem<F>, T: Tag>(
    cs: &mut CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    tag: &T,
    a: &AllocatedPtr<F>,
    b: &AllocatedPtr<F>,
    c: &AllocatedPtr<F>,
    d: &AllocatedPtr<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let tag = g.alloc_tag_cloned(cs, tag);

    let hash = poseidon_hash(
        cs,
        vec![
            a.tag().clone(),
            a.hash().clone(),
            b.tag().clone(),
            b.hash().clone(),
            c.tag().clone(),
            c.hash().clone(),
            d.tag().clone(),
            d.hash().clone(),
        ],
        store.poseidon_cache.constants.c8(),
    )?;

    Ok(AllocatedPtr::from_parts(tag, hash))
}

/// Constructs a `Cons` pointer
#[allow(dead_code)]
#[inline]
pub(crate) fn construct_cons<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    car: &AllocatedPtr<F>,
    cdr: &AllocatedPtr<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    construct_tuple2(cs, g, store, &ExprTag::Cons, car, cdr)
}

/// Constructs a cons-list with the provided `elts`. The terminating value defaults
/// to `nil` when `last` is `None`
#[allow(dead_code)]
pub(crate) fn construct_list<
    F: LurkField,
    CS: ConstraintSystem<F>,
    B: Borrow<AllocatedPtr<F>>,
    I: IntoIterator<Item = B>,
>(
    cs: &mut CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    elts: I,
    last: Option<AllocatedPtr<F>>,
) -> Result<AllocatedPtr<F>, SynthesisError>
where
    <I as IntoIterator>::IntoIter: DoubleEndedIterator,
{
    let init = match last {
        Some(last) => last,
        None => g.alloc_ptr(cs, &store.intern_nil(), store),
    };
    elts.into_iter()
        .rev()
        .enumerate()
        .try_fold(init, |acc, (i, ptr)| {
            construct_cons(ns!(cs, format!("cons {i}")), g, store, ptr.borrow(), &acc)
        })
}

/// Constructs an `Env` pointer
#[allow(dead_code)]
#[inline]
pub(crate) fn construct_env<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    var_hash: &AllocatedNum<F>,
    val: &AllocatedPtr<F>,
    next_env: &AllocatedNum<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let tag = g.alloc_tag_cloned(cs, &ExprTag::Env);

    let hash = poseidon_hash(
        cs,
        vec![
            var_hash.clone(),
            val.tag().clone(),
            val.hash().clone(),
            next_env.clone(),
        ],
        store.poseidon_cache.constants.c4(),
    )?;

    Ok(AllocatedPtr::from_parts(tag, hash))
}

#[inline]
pub(crate) fn construct_provenance<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    query_hash: &AllocatedNum<F>,
    result: &AllocatedPtr<F>,
    deps: &AllocatedNum<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let tag = g.alloc_tag_cloned(cs, &ExprTag::Prov);

    let hash = poseidon_hash(
        cs,
        vec![
            query_hash.clone(),
            result.tag().clone(),
            result.hash().clone(),
            deps.clone(),
        ],
        store.poseidon_cache.constants.c4(),
    )?;

    Ok(AllocatedPtr::from_parts(tag, hash))
}

/// Deconstructs `env`, assumed to be a composition of a symbol hash, a value `Ptr`, and a next `Env` hash.
///
/// # Panics
/// Panics if the store can't deconstruct the env hash.
pub(crate) fn deconstruct_env<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    s: &Store<F>,
    not_dummy: &Boolean,
    env: &AllocatedNum<F>,
) -> Result<(AllocatedNum<F>, AllocatedPtr<F>, AllocatedNum<F>), SynthesisError> {
    let env_zptr = ZPtr::from_parts(tag::Tag::Expr(ExprTag::Env), env.get_value().unwrap());
    let env_ptr = s.to_ptr(&env_zptr);

    let (a, b, c, d) = {
        if let Some([v, val, new_env]) = s.pop_binding(env_ptr) {
            let v_zptr = s.hash_ptr(&v);
            let val_zptr = s.hash_ptr(&val);
            let new_env_zptr = s.hash_ptr(&new_env);
            (
                *v_zptr.value(),
                val_zptr.tag().to_field::<F>(),
                *val_zptr.value(),
                *new_env_zptr.value(),
            )
        } else {
            (F::ZERO, F::ZERO, F::ZERO, F::ZERO)
        }
    };

    let key_sym_hash = AllocatedNum::alloc_infallible(ns!(cs, "key_sym_hash"), || a);
    let val_tag = AllocatedNum::alloc_infallible(ns!(cs, "val_tag"), || b);
    let val_hash = AllocatedNum::alloc_infallible(ns!(cs, "val_hash"), || c);
    let new_env_hash = AllocatedNum::alloc_infallible(ns!(cs, "new_env_hash"), || d);

    let hash = poseidon_hash(
        ns!(cs, "hash"),
        vec![
            key_sym_hash.clone(),
            val_tag.clone(),
            val_hash.clone(),
            new_env_hash.clone(),
        ],
        s.poseidon_cache.constants.c4(),
    )?;

    let val = AllocatedPtr::from_parts(val_tag, val_hash);

    implies_equal(ns!(cs, "hash equality"), not_dummy, env, &hash);

    Ok((key_sym_hash, val, new_env_hash))
}

#[allow(dead_code)]
pub(crate) fn deconstruct_provenance<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    s: &Store<F>,
    not_dummy: &Boolean,
    provenance: &AllocatedNum<F>,
) -> Result<(AllocatedNum<F>, AllocatedPtr<F>, AllocatedNum<F>), SynthesisError> {
    let prov_zptr = ZPtr::from_parts(
        tag::Tag::Expr(ExprTag::Prov),
        provenance.get_value().unwrap_or(F::ZERO),
    );
    let prov_ptr = s.to_ptr(&prov_zptr);

    let (a, b, c, d) = {
        if let Some([q, res, deps]) = s.deconstruct_provenance(prov_ptr) {
            let q_zptr = s.hash_ptr(&q);
            let res_zptr = s.hash_ptr(&res);
            let deps_zptr = s.hash_ptr(&deps);
            (
                *q_zptr.value(),
                res_zptr.tag().to_field::<F>(),
                *res_zptr.value(),
                *deps_zptr.value(),
            )
        } else {
            (F::ZERO, F::ZERO, F::ZERO, F::ZERO)
        }
    };

    let query_cons_hash = AllocatedNum::alloc_infallible(ns!(cs, "query_cons_hash"), || a);
    let res_tag = AllocatedNum::alloc_infallible(ns!(cs, "res_tag"), || b);
    let res_hash = AllocatedNum::alloc_infallible(ns!(cs, "res_hash"), || c);
    let deps_tuple_hash = AllocatedNum::alloc_infallible(ns!(cs, "deps_tuple_hash"), || d);

    let hash = poseidon_hash(
        ns!(cs, "hash"),
        vec![
            query_cons_hash.clone(),
            res_tag.clone(),
            res_hash.clone(),
            deps_tuple_hash.clone(),
        ],
        s.poseidon_cache.constants.c4(),
    )?;

    let res = AllocatedPtr::from_parts(res_tag, res_hash);

    implies_equal(ns!(cs, "hash equality"), not_dummy, provenance, &hash);

    Ok((query_cons_hash, res, deps_tuple_hash))
}

/// Retrieves the `Ptr` that corresponds to `a_ptr` by using the `Store` as the
/// hint provider
#[allow(dead_code)]
fn get_ptr<F: LurkField>(a_ptr: &AllocatedPtr<F>, store: &Store<F>) -> Result<Ptr, SynthesisError> {
    let z_ptr = ZPtr::from_parts(
        Tag::from_field(
            &a_ptr
                .tag()
                .get_value()
                .ok_or_else(|| SynthesisError::AssignmentMissing)?,
        )
        .ok_or_else(|| SynthesisError::Unsatisfiable)?,
        a_ptr
            .hash()
            .get_value()
            .ok_or_else(|| SynthesisError::AssignmentMissing)?,
    );
    Ok(store.to_ptr(&z_ptr))
}

/// Deconstructs `tuple`, assumed to be a composition of two others.
///
/// # Panics
/// Panics if the store can't deconstruct the tuple pointer
#[allow(dead_code)]
pub(crate) fn deconstruct_tuple2<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    store: &Store<F>,
    not_dummy: &Boolean,
    tuple: &AllocatedPtr<F>,
) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>), SynthesisError> {
    let (a, b) = if not_dummy.get_value() == Some(true) {
        let idx = get_ptr(tuple, store)?.get_index2().expect("invalid Ptr");
        let [a, b] = &expect_ptrs!(store, 2, idx);
        (store.hash_ptr(a), store.hash_ptr(b))
    } else {
        (ZPtr::dummy(), ZPtr::dummy())
    };

    let a = AllocatedPtr::alloc_infallible(ns!(cs, "a"), || a);
    let b = AllocatedPtr::alloc_infallible(ns!(cs, "b"), || b);

    let hash = poseidon_hash(
        ns!(cs, "hash"),
        vec![
            a.tag().clone(),
            a.hash().clone(),
            b.tag().clone(),
            b.hash().clone(),
        ],
        store.poseidon_cache.constants.c4(),
    )?;

    implies_equal(ns!(cs, "hash equality"), not_dummy, tuple.hash(), &hash);

    Ok((a, b))
}

/// Deconstructs `tuple`, assumed to be a composition of three others.
///
/// # Panics
/// Panics if the store can't deconstruct the tuple pointer
#[allow(dead_code)]
pub(crate) fn deconstruct_tuple3<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    store: &Store<F>,
    not_dummy: &Boolean,
    tuple: &AllocatedPtr<F>,
) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, AllocatedPtr<F>), SynthesisError> {
    let (a, b, c) = if not_dummy.get_value() == Some(true) {
        let idx = get_ptr(tuple, store)?.get_index3().expect("invalid Ptr");
        let [a, b, c] = &expect_ptrs!(store, 3, idx);
        (store.hash_ptr(a), store.hash_ptr(b), store.hash_ptr(c))
    } else {
        (ZPtr::dummy(), ZPtr::dummy(), ZPtr::dummy())
    };

    let a = AllocatedPtr::alloc_infallible(ns!(cs, "a"), || a);
    let b = AllocatedPtr::alloc_infallible(ns!(cs, "b"), || b);
    let c = AllocatedPtr::alloc_infallible(ns!(cs, "c"), || c);

    let hash = poseidon_hash(
        ns!(cs, "hash"),
        vec![
            a.tag().clone(),
            a.hash().clone(),
            b.tag().clone(),
            b.hash().clone(),
            c.tag().clone(),
            c.hash().clone(),
        ],
        store.poseidon_cache.constants.c6(),
    )?;

    implies_equal(ns!(cs, "hash equality"), not_dummy, tuple.hash(), &hash);

    Ok((a, b, c))
}

/// Deconstructs `tuple`, assumed to be a composition of four others.
///
/// # Panics
/// Panics if the store can't deconstruct the tuple pointer
#[allow(dead_code)]
pub(crate) fn deconstruct_tuple4<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    store: &Store<F>,
    not_dummy: &Boolean,
    tuple: &AllocatedPtr<F>,
) -> Result<
    (
        AllocatedPtr<F>,
        AllocatedPtr<F>,
        AllocatedPtr<F>,
        AllocatedPtr<F>,
    ),
    SynthesisError,
> {
    let (a, b, c, d) = if not_dummy.get_value() == Some(true) {
        let idx = get_ptr(tuple, store)?.get_index4().expect("invalid Ptr");
        let [a, b, c, d] = &expect_ptrs!(store, 4, idx);
        (
            store.hash_ptr(a),
            store.hash_ptr(b),
            store.hash_ptr(c),
            store.hash_ptr(d),
        )
    } else {
        (ZPtr::dummy(), ZPtr::dummy(), ZPtr::dummy(), ZPtr::dummy())
    };

    let a = AllocatedPtr::alloc_infallible(ns!(cs, "a"), || a);
    let b = AllocatedPtr::alloc_infallible(ns!(cs, "b"), || b);
    let c = AllocatedPtr::alloc_infallible(ns!(cs, "c"), || c);
    let d = AllocatedPtr::alloc_infallible(ns!(cs, "d"), || d);

    let hash = poseidon_hash(
        ns!(cs, "hash"),
        vec![
            a.tag().clone(),
            a.hash().clone(),
            b.tag().clone(),
            b.hash().clone(),
            c.tag().clone(),
            c.hash().clone(),
            d.tag().clone(),
            d.hash().clone(),
        ],
        store.poseidon_cache.constants.c8(),
    )?;

    implies_equal(ns!(cs, "hash equality"), not_dummy, tuple.hash(), &hash);

    Ok((a, b, c, d))
}

/// Deconstructs `data` with `car_cdr` semantics.
///
/// # Panics
/// Panics if the store can't deconstruct `data` with `car_cdr`
#[allow(dead_code)]
pub(crate) fn car_cdr<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    not_dummy: &Boolean,
    data: &AllocatedPtr<F>,
) -> Result<(AllocatedPtr<F>, AllocatedPtr<F>, Boolean), SynthesisError> {
    let (car, cdr) = if not_dummy.get_value() == Some(true) {
        let (car, cdr) = store.car_cdr(&get_ptr(data, store)?).expect("invalid Ptr");
        (store.hash_ptr(&car), store.hash_ptr(&cdr))
    } else {
        (ZPtr::dummy(), ZPtr::dummy())
    };

    let nil = g.alloc_ptr(cs, &store.intern_nil(), store);
    let empty_str = g.alloc_ptr(cs, &store.intern_string(""), store);

    let car = AllocatedPtr::alloc_infallible(ns!(cs, "car"), || car);
    let cdr = AllocatedPtr::alloc_infallible(ns!(cs, "cdr"), || cdr);

    let data_is_nil = data.alloc_equal(ns!(cs, "data is nil"), &nil)?;

    let data_is_empty_str = data.alloc_equal(ns!(cs, "data is empty str"), &empty_str)?;

    {
        // when data is nil, we enforce that car and cdr are both nil
        let not_dummy_and_data_is_nil = Boolean::and(
            ns!(cs, "not dummy and data is nil"),
            not_dummy,
            &data_is_nil,
        )?;

        car.implies_ptr_equal(
            ns!(cs, "data is nil implies car is nil"),
            &not_dummy_and_data_is_nil,
            &nil,
        );
        cdr.implies_ptr_equal(
            ns!(cs, "data is nil implies cdr is nil"),
            &not_dummy_and_data_is_nil,
            &nil,
        );
    }

    {
        // when data is the empty string, we enforce that car is nil and cdr is
        // the empty string
        let not_dummy_and_data_is_empty_str = Boolean::and(
            ns!(cs, "not dummy and data is empty str"),
            not_dummy,
            &data_is_empty_str,
        )?;

        car.implies_ptr_equal(
            ns!(cs, "data is empty str implies car is nil"),
            &not_dummy_and_data_is_empty_str,
            &nil,
        );
        cdr.implies_ptr_equal(
            ns!(cs, "data is empty str implies cdr is empty str"),
            &not_dummy_and_data_is_empty_str,
            &empty_str,
        );
    }

    // data is not empty: it's not nil and it's not the empty string
    let data_is_not_empty = Boolean::and(
        ns!(cs, "data is not empty"),
        &data_is_nil.not(),
        &data_is_empty_str.not(),
    )?;

    {
        // when data is not empty, we enforce hash equality
        let not_dumy_and_data_is_not_empty = Boolean::and(
            ns!(cs, "not dummy and data is not empty"),
            not_dummy,
            &data_is_not_empty,
        )?;

        let hash = poseidon_hash(
            ns!(cs, "hash"),
            vec![
                car.tag().clone(),
                car.hash().clone(),
                cdr.tag().clone(),
                cdr.hash().clone(),
            ],
            store.poseidon_cache.constants.c4(),
        )?;

        implies_equal(
            ns!(cs, "data is not empty implies hash equality"),
            &not_dumy_and_data_is_not_empty,
            data.hash(),
            &hash,
        );
    }

    Ok((car, cdr, data_is_not_empty))
}

/// Chains `car_cdr` calls `n` times, returning the accumulated `car`s, the final
/// `cdr` and the (explored) actual length (`<= n`) of the cons-like `data`. For
/// example, calling `chain_car_cdr` on "ab" with `n = 4` should return the full
/// actual length `2` of such string. But if `n` is set to `1`, it will return
/// `1` as the (explored) length.
///
/// It can be used to deconstruct cons-lists into their elements or strings into
/// their characters.
///
/// # Panics
/// Panics if any of the reached elements can't be deconstructed with `car_cdr`
///
/// ```
/// # use bellpepper_core::{boolean::Boolean, test_cs::TestConstraintSystem, ConstraintSystem};
/// # use pasta_curves::Fq;
///
/// use lurk::{
/// #    circuit::gadgets::pointer::AllocatedPtr,
/// #    field::LurkField,
/// #    lem::{circuit::GlobalAllocator, pointers::Ptr, store::Store},
///     coprocessor::gadgets::{a_ptr_as_z_ptr, chain_car_cdr},
/// };
///
/// # let mut cs = TestConstraintSystem::new();
/// # let g = GlobalAllocator::default();
/// let store = Store::<Fq>::default();
/// let nil = store.intern_nil();
/// let z_nil = store.hash_ptr(&nil);
/// let empty_str = store.intern_string("");
/// let z_empty_str = store.hash_ptr(&empty_str);
/// let not_dummy = Boolean::Constant(true);
///
/// let ab = store.intern_string("ab");
/// let z_ab = store.hash_ptr(&ab);
/// let a = store.char('a');
/// let b = store.char('b');
/// let z_a = store.hash_ptr(&a);
/// let z_b = store.hash_ptr(&b);
/// let a_ab = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "ab"), || z_ab);
/// let (cars, cdr, length) = chain_car_cdr(
///     &mut cs.namespace(|| "chain_car_cdr on ab"),
///     &g,
///     &store,
///     &not_dummy,
///     &a_ab,
///     4,
/// )
/// .unwrap();
/// assert_eq!(cars.len(), 4);
/// assert_eq!(a_ptr_as_z_ptr(&cars[0]), Some(z_a));
/// assert_eq!(a_ptr_as_z_ptr(&cars[1]), Some(z_b));
/// assert_eq!(a_ptr_as_z_ptr(&cars[2]), Some(z_nil));
/// assert_eq!(a_ptr_as_z_ptr(&cars[3]), Some(z_nil));
/// assert_eq!(a_ptr_as_z_ptr(&cdr), Some(z_empty_str));
/// assert_eq!(length.get_value(), Some(Fq::from_u64(2)));
/// ```
#[allow(dead_code)]
pub fn chain_car_cdr<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    not_dummy: &Boolean,
    data: &AllocatedPtr<F>,
    n: usize,
) -> Result<(Vec<AllocatedPtr<F>>, AllocatedPtr<F>, AllocatedNum<F>), SynthesisError> {
    let mut cars = Vec::with_capacity(n);
    let mut cdr = data.clone();
    let mut length = g.alloc_const_cloned(cs, F::ZERO);
    for i in 0..n {
        let (car, new_cdr, not_empty) =
            car_cdr(ns!(cs, format!("car_cdr {i}")), g, store, not_dummy, &cdr)?;
        cars.push(car);
        cdr = new_cdr;
        let not_empty_num = boolean_to_num(ns!(cs, format!("not_empty_num {i}")), &not_empty)?;
        length = length.add(ns!(cs, format!("length {i}")), &not_empty_num)?;
    }
    Ok((cars, cdr, length))
}

#[inline]
pub fn a_ptr_as_z_ptr<T: Tag, F: LurkField>(
    a: &AllocatedPtr<F>,
) -> Option<crate::z_ptr::ZPtr<T, F>> {
    a.tag()
        .get_value()
        .and_then(|t| Tag::from_field(&t))
        .and_then(|tag| {
            a.hash()
                .get_value()
                .map(|hash| crate::z_ptr::ZPtr::from_parts(tag, hash))
        })
}

#[cfg(test)]
mod test {
    use bellpepper::util_cs::witness_cs::WitnessCS;
    use bellpepper_core::{boolean::Boolean, test_cs::TestConstraintSystem, ConstraintSystem};
    use halo2curves::bn256::Fr as Fq;

    use crate::{
        circuit::gadgets::pointer::AllocatedPtr,
        coprocessor::gadgets::{
            car_cdr, construct_tuple2, construct_tuple3, construct_tuple4, deconstruct_tuple3,
            deconstruct_tuple4,
        },
        field::LurkField,
        lem::{
            circuit::GlobalAllocator,
            store::{intern_ptrs, Store},
        },
    };

    use super::{a_ptr_as_z_ptr, chain_car_cdr, construct_list, deconstruct_tuple2};

    #[test]
    fn test_construct_tuples() {
        let mut cs = WitnessCS::new();
        let g = GlobalAllocator::default();
        let store = Store::<Fq>::default();
        let nil = store.intern_nil();
        let nil_tag = nil.tag();
        let a_nil = g.alloc_ptr(&mut cs, &nil, &store);

        let nil2 = construct_tuple2(ns!(cs, "nil2"), &g, &store, nil_tag, &a_nil, &a_nil).unwrap();
        let nil2_ptr = intern_ptrs!(store, *nil_tag, nil, nil);
        let z_nil2_ptr = store.hash_ptr(&nil2_ptr);
        assert_eq!(a_ptr_as_z_ptr(&nil2), Some(z_nil2_ptr));

        let nil3 =
            construct_tuple3(ns!(cs, "nil3"), &g, &store, nil_tag, &a_nil, &a_nil, &a_nil).unwrap();
        let nil3_ptr = intern_ptrs!(store, *nil_tag, nil, nil, nil);
        let z_nil3_ptr = store.hash_ptr(&nil3_ptr);
        assert_eq!(a_ptr_as_z_ptr(&nil3), Some(z_nil3_ptr));

        let nil4 = construct_tuple4(
            ns!(cs, "nil4"),
            &g,
            &store,
            nil_tag,
            &a_nil,
            &a_nil,
            &a_nil,
            &a_nil,
        )
        .unwrap();
        let nil4_ptr = intern_ptrs!(store, *nil_tag, nil, nil, nil, nil);
        let z_nil4_ptr = store.hash_ptr(&nil4_ptr);
        assert_eq!(a_ptr_as_z_ptr(&nil4), Some(z_nil4_ptr));
    }

    #[test]
    fn test_construct_list() {
        let mut cs = WitnessCS::new();
        let g = GlobalAllocator::default();
        let store = Store::<Fq>::default();
        let one = store.num_u64(1);
        let a_one = g.alloc_ptr(&mut cs, &one, &store);

        // proper list
        let a_list = construct_list(&mut cs, &g, &store, [&a_one, &a_one], None).unwrap();
        let z_list = store.hash_ptr(&store.list(vec![one, one]));
        assert_eq!(a_ptr_as_z_ptr(&a_list), Some(z_list));

        // improper list
        let a_list =
            construct_list(&mut cs, &g, &store, [&a_one, &a_one], Some(a_one.clone())).unwrap();
        let z_list = store.hash_ptr(&store.improper_list(vec![one, one], one));
        assert_eq!(a_ptr_as_z_ptr(&a_list), Some(z_list));
    }

    #[test]
    fn deconstruct_tuples() {
        let mut cs = TestConstraintSystem::new();
        let store = Store::<Fq>::default();
        let nil = store.intern_nil();
        let z_nil = store.hash_ptr(&nil);
        let nil_tag = *nil.tag();
        let not_dummy = Boolean::Constant(true);

        let tuple2 = intern_ptrs!(store, nil_tag, nil, nil);
        let z_tuple2 = store.hash_ptr(&tuple2);
        let a_tuple2 = AllocatedPtr::alloc_infallible(ns!(cs, "tuple2"), || z_tuple2);
        let (a, b) =
            deconstruct_tuple2(ns!(cs, "deconstruct tuple2"), &store, &not_dummy, &a_tuple2)
                .unwrap();
        assert_eq!(a_ptr_as_z_ptr(&a), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&b), Some(z_nil));

        let tuple3 = intern_ptrs!(store, nil_tag, nil, nil, nil);
        let z_tuple3 = store.hash_ptr(&tuple3);
        let a_tuple3 = AllocatedPtr::alloc_infallible(ns!(cs, "tuple3"), || z_tuple3);
        let (a, b, c) =
            deconstruct_tuple3(ns!(cs, "deconstruct tuple3"), &store, &not_dummy, &a_tuple3)
                .unwrap();
        assert_eq!(a_ptr_as_z_ptr(&a), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&b), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&c), Some(z_nil));

        let tuple4 = intern_ptrs!(store, nil_tag, nil, nil, nil, nil);
        let z_tuple4 = store.hash_ptr(&tuple4);
        let a_tuple4 = AllocatedPtr::alloc_infallible(ns!(cs, "tuple4"), || z_tuple4);
        let (a, b, c, d) =
            deconstruct_tuple4(ns!(cs, "deconstruct tuple4"), &store, &not_dummy, &a_tuple4)
                .unwrap();
        assert_eq!(a_ptr_as_z_ptr(&a), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&b), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&c), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&d), Some(z_nil));

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_car_cdr() {
        let mut cs = TestConstraintSystem::new();
        let g = GlobalAllocator::default();
        let store = Store::<Fq>::default();
        let nil = store.intern_nil();
        let z_nil = store.hash_ptr(&nil);
        let empty_str = store.intern_string("");
        let z_empty_str = store.hash_ptr(&empty_str);
        let not_dummy = Boolean::Constant(true);

        // nil
        let a_nil = AllocatedPtr::alloc_infallible(ns!(cs, "nil"), || z_nil);
        let (car, cdr, not_empty) =
            car_cdr(ns!(cs, "car_cdr of nil"), &g, &store, &not_dummy, &a_nil).unwrap();
        assert_eq!(a_ptr_as_z_ptr(&car), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&cdr), Some(z_nil));
        assert_eq!(not_empty.get_value(), Some(false));

        // cons
        let one = store.num_u64(1);
        let z_one = store.hash_ptr(&one);
        let cons = store.cons(one, one);
        let z_cons = store.hash_ptr(&cons);
        let a_cons = AllocatedPtr::alloc_infallible(ns!(cs, "cons"), || z_cons);
        let (car, cdr, not_empty) =
            car_cdr(ns!(cs, "car_cdr of cons"), &g, &store, &not_dummy, &a_cons).unwrap();
        assert_eq!(a_ptr_as_z_ptr(&car), Some(z_one));
        assert_eq!(a_ptr_as_z_ptr(&cdr), Some(z_one));
        assert_eq!(not_empty.get_value(), Some(true));

        // empty string
        let a_empty_str = AllocatedPtr::alloc_infallible(ns!(cs, "empty str"), || z_empty_str);
        let (car, cdr, not_empty) = car_cdr(
            ns!(cs, "car_cdr of empty str"),
            &g,
            &store,
            &not_dummy,
            &a_empty_str,
        )
        .unwrap();
        assert_eq!(a_ptr_as_z_ptr(&car), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&cdr), Some(z_empty_str));
        assert_eq!(not_empty.get_value(), Some(false));

        // non-empty string
        let abc = store.intern_string("abc");
        let bc = store.intern_string("bc");
        let a = store.char('a');
        let z_abc = store.hash_ptr(&abc);
        let z_bc = store.hash_ptr(&bc);
        let z_a = store.hash_ptr(&a);
        let a_abc = AllocatedPtr::alloc_infallible(ns!(cs, "abc"), || z_abc);
        let (car, cdr, not_empty) =
            car_cdr(ns!(cs, "car_cdr of abc"), &g, &store, &not_dummy, &a_abc).unwrap();
        assert_eq!(a_ptr_as_z_ptr(&car), Some(z_a));
        assert_eq!(a_ptr_as_z_ptr(&cdr), Some(z_bc));
        assert_eq!(not_empty.get_value(), Some(true));

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_chain_car_cdr() {
        let mut cs = TestConstraintSystem::new();
        let g = GlobalAllocator::default();
        let store = Store::<Fq>::default();
        let nil = store.intern_nil();
        let z_nil = store.hash_ptr(&nil);
        let empty_str = store.intern_string("");
        let z_empty_str = store.hash_ptr(&empty_str);
        let not_dummy = Boolean::Constant(true);

        // string
        let ab = store.intern_string("ab");
        let z_ab = store.hash_ptr(&ab);
        let a = store.char('a');
        let b = store.char('b');
        let z_a = store.hash_ptr(&a);
        let z_b = store.hash_ptr(&b);
        let a_ab = AllocatedPtr::alloc_infallible(ns!(cs, "ab"), || z_ab);
        let (cars, cdr, length) = chain_car_cdr(
            ns!(cs, "chain_car_cdr on ab"),
            &g,
            &store,
            &not_dummy,
            &a_ab,
            4,
        )
        .unwrap();
        assert_eq!(cars.len(), 4);
        assert_eq!(a_ptr_as_z_ptr(&cars[0]), Some(z_a));
        assert_eq!(a_ptr_as_z_ptr(&cars[1]), Some(z_b));
        assert_eq!(a_ptr_as_z_ptr(&cars[2]), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&cars[3]), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&cdr), Some(z_empty_str));
        assert_eq!(length.get_value(), Some(Fq::from_u64(2)));

        // list
        let list = store.list(vec![ab, ab]);
        let z_list = store.hash_ptr(&list);
        let a_list = AllocatedPtr::alloc_infallible(ns!(cs, "list"), || z_list);
        let (cars, cdr, length) = chain_car_cdr(
            ns!(cs, "chain_car_cdr on list"),
            &g,
            &store,
            &not_dummy,
            &a_list,
            4,
        )
        .unwrap();
        assert_eq!(cars.len(), 4);
        assert_eq!(a_ptr_as_z_ptr(&cars[0]), Some(z_ab));
        assert_eq!(a_ptr_as_z_ptr(&cars[1]), Some(z_ab));
        assert_eq!(a_ptr_as_z_ptr(&cars[2]), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&cars[3]), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&cdr), Some(z_nil));
        assert_eq!(length.get_value(), Some(Fq::from_u64(2)));
    }
}
