//! Helper gadgets for synthesis

use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};

use crate::{
    circuit::gadgets::{
        constraints::{boolean_to_num, implies_equal},
        data::hash_poseidon,
        pointer::AllocatedPtr,
    },
    field::LurkField,
    lem::{
        circuit::GlobalAllocator,
        pointers::{Ptr, ZPtr},
        store::Store,
    },
    tag::{ExprTag, Tag},
};

/// Constructs an `AllocatedPtr` compound by two others
#[allow(dead_code)]
pub(crate) fn construct_tuple2<F: LurkField, CS: ConstraintSystem<F>, T: Tag>(
    cs: CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    tag: &T,
    a: &AllocatedPtr<F>,
    b: &AllocatedPtr<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let tag = g.get_tag_cloned(tag)?;

    let hash = hash_poseidon(
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
    cs: CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    tag: &T,
    a: &AllocatedPtr<F>,
    b: &AllocatedPtr<F>,
    c: &AllocatedPtr<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let tag = g.get_tag_cloned(tag)?;

    let hash = hash_poseidon(
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
    cs: CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    tag: &T,
    a: &AllocatedPtr<F>,
    b: &AllocatedPtr<F>,
    c: &AllocatedPtr<F>,
    d: &AllocatedPtr<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let tag = g.get_tag_cloned(tag)?;

    let hash = hash_poseidon(
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
    cs: CS,
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
pub(crate) fn construct_list<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    elts: &[&AllocatedPtr<F>],
    last: Option<AllocatedPtr<F>>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let init = match last {
        Some(last) => last,
        None => g.get_allocated_ptr_from_ptr(&store.intern_nil(), store)?,
    };
    elts.iter()
        .rev()
        .enumerate()
        .try_fold(init, |acc, (i, ptr)| {
            construct_cons(cs.namespace(|| format!("cons {i}")), g, store, ptr, &acc)
        })
}

/// Retrieves the `Ptr` that corresponds to `a_ptr` by using the `Store` as the
/// hint provider
#[allow(dead_code)]
fn get_ptr<F: LurkField>(
    a_ptr: &AllocatedPtr<F>,
    store: &Store<F>,
) -> Result<Ptr<F>, SynthesisError> {
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
        let (a, b) = store.expect_2_ptrs(idx);
        (store.hash_ptr(a), store.hash_ptr(b))
    } else {
        (ZPtr::dummy(), ZPtr::dummy())
    };

    let a = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "a"), || a);
    let b = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "b"), || b);

    let hash = hash_poseidon(
        &mut cs.namespace(|| "hash"),
        vec![
            a.tag().clone(),
            a.hash().clone(),
            b.tag().clone(),
            b.hash().clone(),
        ],
        store.poseidon_cache.constants.c4(),
    )?;

    implies_equal(
        &mut cs.namespace(|| "hash equality"),
        not_dummy,
        tuple.hash(),
        &hash,
    );

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
        let (a, b, c) = store.expect_3_ptrs(idx);
        (store.hash_ptr(a), store.hash_ptr(b), store.hash_ptr(c))
    } else {
        (ZPtr::dummy(), ZPtr::dummy(), ZPtr::dummy())
    };

    let a = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "a"), || a);
    let b = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "b"), || b);
    let c = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "c"), || c);

    let hash = hash_poseidon(
        &mut cs.namespace(|| "hash"),
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

    implies_equal(
        &mut cs.namespace(|| "hash equality"),
        not_dummy,
        tuple.hash(),
        &hash,
    );

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
        let (a, b, c, d) = store.expect_4_ptrs(idx);
        (
            store.hash_ptr(a),
            store.hash_ptr(b),
            store.hash_ptr(c),
            store.hash_ptr(d),
        )
    } else {
        (ZPtr::dummy(), ZPtr::dummy(), ZPtr::dummy(), ZPtr::dummy())
    };

    let a = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "a"), || a);
    let b = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "b"), || b);
    let c = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "c"), || c);
    let d = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "d"), || d);

    let hash = hash_poseidon(
        &mut cs.namespace(|| "hash"),
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

    implies_equal(
        &mut cs.namespace(|| "hash equality"),
        not_dummy,
        tuple.hash(),
        &hash,
    );

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

    let nil = g.get_allocated_ptr_from_ptr(&store.intern_nil(), store)?;
    let empty_str = g.get_allocated_ptr_from_ptr(&store.intern_string(""), store)?;

    let car = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "car"), || car);
    let cdr = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "cdr"), || cdr);

    let data_is_nil = data.alloc_equal(&mut cs.namespace(|| "data is nil"), &nil)?;

    let data_is_empty_str =
        data.alloc_equal(&mut cs.namespace(|| "data is empty str"), &empty_str)?;

    {
        // when data is nil, we enforce that car and cdr are both nil
        let not_dummy_and_data_is_nil = Boolean::and(
            &mut cs.namespace(|| "not dummy and data is nil"),
            not_dummy,
            &data_is_nil,
        )?;

        car.implies_ptr_equal(
            &mut cs.namespace(|| "data is nil implies car is nil"),
            &not_dummy_and_data_is_nil,
            &nil,
        );
        cdr.implies_ptr_equal(
            &mut cs.namespace(|| "data is nil implies cdr is nil"),
            &not_dummy_and_data_is_nil,
            &nil,
        );
    }

    {
        // when data is the empty string, we enforce that car is nil and cdr is
        // the empty string
        let not_dummy_and_data_is_empty_str = Boolean::and(
            &mut cs.namespace(|| "not dummy and data is empty str"),
            not_dummy,
            &data_is_empty_str,
        )?;

        car.implies_ptr_equal(
            &mut cs.namespace(|| "data is empty str implies car is nil"),
            &not_dummy_and_data_is_empty_str,
            &nil,
        );
        cdr.implies_ptr_equal(
            &mut cs.namespace(|| "data is empty str implies cdr is empty str"),
            &not_dummy_and_data_is_empty_str,
            &empty_str,
        );
    }

    // data is not empty: it's not nil and it's not the empty string
    let data_is_not_empty = Boolean::and(
        &mut cs.namespace(|| "data is not empty"),
        &data_is_nil.not(),
        &data_is_empty_str.not(),
    )?;

    {
        // when data is not empty, we enforce hash equality
        let not_dumy_and_data_is_not_empty = Boolean::and(
            &mut cs.namespace(|| "not dummy and data is not empty"),
            not_dummy,
            &data_is_not_empty,
        )?;

        let hash = hash_poseidon(
            &mut cs.namespace(|| "hash"),
            vec![
                car.tag().clone(),
                car.hash().clone(),
                cdr.tag().clone(),
                cdr.hash().clone(),
            ],
            store.poseidon_cache.constants.c4(),
        )?;

        implies_equal(
            &mut cs.namespace(|| "data is not empty implies hash equality"),
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
/// # let mut g = GlobalAllocator::default();
/// let store = Store::<Fq>::default();
/// let nil = store.intern_nil();
/// let z_nil = store.hash_ptr(&nil);
/// let empty_str = store.intern_string("");
/// let z_empty_str = store.hash_ptr(&empty_str);
/// # g.new_consts_from_z_ptr(&mut cs, &z_nil);
/// # g.new_consts_from_z_ptr(&mut cs, &z_empty_str);
/// let not_dummy = Boolean::Constant(true);
///
/// let ab = store.intern_string("ab");
/// let z_ab = store.hash_ptr(&ab);
/// let a = Ptr::char('a');
/// let b = Ptr::char('b');
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
pub(crate) fn chain_car_cdr<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    not_dummy: &Boolean,
    data: &AllocatedPtr<F>,
    n: usize,
) -> Result<(Vec<AllocatedPtr<F>>, AllocatedPtr<F>, AllocatedNum<F>), SynthesisError> {
    let mut cars = Vec::with_capacity(n);
    let mut cdr = data.clone();
    let mut length = g.get_const_cloned(F::ZERO)?;
    for i in 0..n {
        let (car, new_cdr, not_empty) = car_cdr(
            &mut cs.namespace(|| format!("car_cdr {i}")),
            g,
            store,
            not_dummy,
            &cdr,
        )?;
        cars.push(car);
        cdr = new_cdr;
        let not_empty_num = boolean_to_num(
            &mut cs.namespace(|| format!("not_empty_num {i}")),
            &not_empty,
        )?;
        length = length.add(&mut cs.namespace(|| format!("length {i}")), &not_empty_num)?;
    }
    Ok((cars, cdr, length))
}

#[inline]
#[allow(dead_code)]
pub(crate) fn a_ptr_as_z_ptr<T: Tag, F: LurkField>(
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
    use pasta_curves::Fq;

    use crate::{
        circuit::gadgets::pointer::AllocatedPtr,
        coprocessor::gadgets::{
            car_cdr, construct_tuple2, construct_tuple3, construct_tuple4, deconstruct_tuple3,
            deconstruct_tuple4,
        },
        field::LurkField,
        lem::{circuit::GlobalAllocator, pointers::Ptr, store::Store},
        tag::ExprTag,
    };

    use super::{a_ptr_as_z_ptr, chain_car_cdr, construct_list, deconstruct_tuple2};

    #[test]
    fn test_construct_tuples() {
        let mut cs = WitnessCS::new();
        let mut g = GlobalAllocator::default();
        let store = Store::<Fq>::default();
        let nil = store.intern_nil();
        let z_nil = store.hash_ptr(&nil);
        let nil_tag = z_nil.tag();
        g.new_consts_from_z_ptr(&mut cs, &z_nil);
        let a_nil = g.get_allocated_ptr(nil_tag, *z_nil.value()).unwrap();

        let nil2 = construct_tuple2(
            &mut cs.namespace(|| "nil2"),
            &g,
            &store,
            nil_tag,
            &a_nil,
            &a_nil,
        )
        .unwrap();
        let nil2_ptr = store.intern_2_ptrs(*nil_tag, nil, nil);
        let z_nil2_ptr = store.hash_ptr(&nil2_ptr);
        assert_eq!(a_ptr_as_z_ptr(&nil2), Some(z_nil2_ptr));

        let nil3 = construct_tuple3(
            &mut cs.namespace(|| "nil3"),
            &g,
            &store,
            nil_tag,
            &a_nil,
            &a_nil,
            &a_nil,
        )
        .unwrap();
        let nil3_ptr = store.intern_3_ptrs(*nil_tag, nil, nil, nil);
        let z_nil3_ptr = store.hash_ptr(&nil3_ptr);
        assert_eq!(a_ptr_as_z_ptr(&nil3), Some(z_nil3_ptr));

        let nil4 = construct_tuple4(
            &mut cs.namespace(|| "nil4"),
            &g,
            &store,
            nil_tag,
            &a_nil,
            &a_nil,
            &a_nil,
            &a_nil,
        )
        .unwrap();
        let nil4_ptr = store.intern_4_ptrs(*nil_tag, nil, nil, nil, nil);
        let z_nil4_ptr = store.hash_ptr(&nil4_ptr);
        assert_eq!(a_ptr_as_z_ptr(&nil4), Some(z_nil4_ptr));
    }

    #[test]
    fn test_construct_list() {
        let mut cs = WitnessCS::new();
        let mut g = GlobalAllocator::default();
        let store = Store::<Fq>::default();
        let one = Ptr::num_u64(1);
        let nil = store.intern_nil();
        let z_one = store.hash_ptr(&one);
        let z_nil = store.hash_ptr(&nil);
        g.new_consts_from_z_ptr(&mut cs, &z_nil);
        g.new_consts_from_z_ptr(&mut cs, &z_one);
        g.new_const_from_tag(&mut cs, &ExprTag::Cons);
        let a_one = g.get_allocated_ptr(z_one.tag(), *z_one.value()).unwrap();

        // proper list
        let a_list = construct_list(&mut cs, &g, &store, &[&a_one, &a_one], None).unwrap();
        let z_list = store.hash_ptr(&store.list(vec![one, one]));
        assert_eq!(a_ptr_as_z_ptr(&a_list), Some(z_list));

        // improper list
        let a_list =
            construct_list(&mut cs, &g, &store, &[&a_one, &a_one], Some(a_one.clone())).unwrap();
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

        let tuple2 = store.intern_2_ptrs(nil_tag, nil, nil);
        let z_tuple2 = store.hash_ptr(&tuple2);
        let a_tuple2 = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "tuple2"), || z_tuple2);
        let (a, b) = deconstruct_tuple2(
            &mut cs.namespace(|| "deconstruct tuple2"),
            &store,
            &not_dummy,
            &a_tuple2,
        )
        .unwrap();
        assert_eq!(a_ptr_as_z_ptr(&a), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&b), Some(z_nil));

        let tuple3 = store.intern_3_ptrs(nil_tag, nil, nil, nil);
        let z_tuple3 = store.hash_ptr(&tuple3);
        let a_tuple3 = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "tuple3"), || z_tuple3);
        let (a, b, c) = deconstruct_tuple3(
            &mut cs.namespace(|| "deconstruct tuple3"),
            &store,
            &not_dummy,
            &a_tuple3,
        )
        .unwrap();
        assert_eq!(a_ptr_as_z_ptr(&a), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&b), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&c), Some(z_nil));

        let tuple4 = store.intern_4_ptrs(nil_tag, nil, nil, nil, nil);
        let z_tuple4 = store.hash_ptr(&tuple4);
        let a_tuple4 = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "tuple4"), || z_tuple4);
        let (a, b, c, d) = deconstruct_tuple4(
            &mut cs.namespace(|| "deconstruct tuple4"),
            &store,
            &not_dummy,
            &a_tuple4,
        )
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
        let mut g = GlobalAllocator::default();
        let store = Store::<Fq>::default();
        let nil = store.intern_nil();
        let z_nil = store.hash_ptr(&nil);
        let empty_str = store.intern_string("");
        let z_empty_str = store.hash_ptr(&empty_str);
        let not_dummy = Boolean::Constant(true);
        g.new_consts_from_z_ptr(&mut cs, &z_nil);
        g.new_consts_from_z_ptr(&mut cs, &z_empty_str);

        // nil
        let a_nil = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "nil"), || z_nil);
        let (car, cdr, not_empty) = car_cdr(
            &mut cs.namespace(|| "car_cdr of nil"),
            &g,
            &store,
            &not_dummy,
            &a_nil,
        )
        .unwrap();
        assert_eq!(a_ptr_as_z_ptr(&car), Some(z_nil));
        assert_eq!(a_ptr_as_z_ptr(&cdr), Some(z_nil));
        assert_eq!(not_empty.get_value(), Some(false));

        // cons
        let one = Ptr::num_u64(1);
        let z_one = store.hash_ptr(&one);
        let cons = store.cons(one, one);
        let z_cons = store.hash_ptr(&cons);
        let a_cons = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "cons"), || z_cons);
        let (car, cdr, not_empty) = car_cdr(
            &mut cs.namespace(|| "car_cdr of cons"),
            &g,
            &store,
            &not_dummy,
            &a_cons,
        )
        .unwrap();
        assert_eq!(a_ptr_as_z_ptr(&car), Some(z_one));
        assert_eq!(a_ptr_as_z_ptr(&cdr), Some(z_one));
        assert_eq!(not_empty.get_value(), Some(true));

        // empty string
        let a_empty_str =
            AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "empty str"), || z_empty_str);
        let (car, cdr, not_empty) = car_cdr(
            &mut cs.namespace(|| "car_cdr of empty str"),
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
        let a = Ptr::char('a');
        let z_abc = store.hash_ptr(&abc);
        let z_bc = store.hash_ptr(&bc);
        let z_a = store.hash_ptr(&a);
        let a_abc = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "abc"), || z_abc);
        let (car, cdr, not_empty) = car_cdr(
            &mut cs.namespace(|| "car_cdr of abc"),
            &g,
            &store,
            &not_dummy,
            &a_abc,
        )
        .unwrap();
        assert_eq!(a_ptr_as_z_ptr(&car), Some(z_a));
        assert_eq!(a_ptr_as_z_ptr(&cdr), Some(z_bc));
        assert_eq!(not_empty.get_value(), Some(true));

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_chain_car_cdr() {
        let mut cs = TestConstraintSystem::new();
        let mut g = GlobalAllocator::default();
        let store = Store::<Fq>::default();
        let nil = store.intern_nil();
        let z_nil = store.hash_ptr(&nil);
        let empty_str = store.intern_string("");
        let z_empty_str = store.hash_ptr(&empty_str);
        g.new_consts_from_z_ptr(&mut cs, &z_nil);
        g.new_consts_from_z_ptr(&mut cs, &z_empty_str);
        let not_dummy = Boolean::Constant(true);

        // string
        let ab = store.intern_string("ab");
        let z_ab = store.hash_ptr(&ab);
        let a = Ptr::char('a');
        let b = Ptr::char('b');
        let z_a = store.hash_ptr(&a);
        let z_b = store.hash_ptr(&b);
        let a_ab = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "ab"), || z_ab);
        let (cars, cdr, length) = chain_car_cdr(
            &mut cs.namespace(|| "chain_car_cdr on ab"),
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
        let a_list = AllocatedPtr::alloc_infallible(&mut cs.namespace(|| "list"), || z_list);
        let (cars, cdr, length) = chain_car_cdr(
            &mut cs.namespace(|| "chain_car_cdr on list"),
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
