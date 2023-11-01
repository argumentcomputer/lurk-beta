//! Helper gadgets for synthesis
//!
//! TODO: deconstructing gadgets from `circuit_frame.rs`

use bellpepper_core::{ConstraintSystem, SynthesisError};

use crate::{
    circuit::gadgets::{data::hash_poseidon, pointer::AllocatedPtr},
    field::LurkField,
    lem::{circuit::GlobalAllocator, store::Store},
    tag::{ExprTag, Tag},
};

pub fn construct_tuple2<F: LurkField, CS: ConstraintSystem<F>, T: Tag>(
    cs: CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    tag: &T,
    a: &AllocatedPtr<F>,
    b: &AllocatedPtr<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let tag = g.get_tag_cloned(tag).expect("Tag not allocated");

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

pub fn construct_tuple3<F: LurkField, CS: ConstraintSystem<F>, T: Tag>(
    cs: CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    tag: &T,
    a: &AllocatedPtr<F>,
    b: &AllocatedPtr<F>,
    c: &AllocatedPtr<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let tag = g.get_tag_cloned(tag).expect("Tag not allocated");

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

pub fn construct_tuple4<F: LurkField, CS: ConstraintSystem<F>, T: Tag>(
    cs: CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    tag: &T,
    a: &AllocatedPtr<F>,
    b: &AllocatedPtr<F>,
    c: &AllocatedPtr<F>,
    d: &AllocatedPtr<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let tag = g.get_tag_cloned(tag).expect("Tag not allocated");

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

#[inline]
pub fn construct_cons<F: LurkField, CS: ConstraintSystem<F>>(
    cs: CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    car: &AllocatedPtr<F>,
    cdr: &AllocatedPtr<F>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    construct_tuple2(cs, g, store, &ExprTag::Cons, car, cdr)
}

/// Constructs a cons-list with the provided `elts`. The terminating value defaults
/// to the `nil` allocated pointer when `last` is `None`
pub fn construct_list<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    g: &GlobalAllocator<F>,
    store: &Store<F>,
    elts: &[&AllocatedPtr<F>],
    last: Option<AllocatedPtr<F>>,
) -> Result<AllocatedPtr<F>, SynthesisError> {
    let init = last.unwrap_or_else(|| {
        g.get_allocated_ptr_from_ptr(&store.intern_nil(), store)
            .expect("nil pointer not allocated")
    });
    elts.iter()
        .rev()
        .enumerate()
        .try_fold(init, |acc, (i, ptr)| {
            construct_cons(cs.namespace(|| format!("Cons {i}")), g, store, ptr, &acc)
        })
}

#[cfg(test)]
mod test {
    use bellpepper::util_cs::witness_cs::WitnessCS;
    use bellpepper_core::ConstraintSystem;
    use pasta_curves::Fq;

    use crate::{
        coprocessor::gadgets::{construct_tuple2, construct_tuple3, construct_tuple4},
        lem::{circuit::GlobalAllocator, pointers::Ptr, store::Store},
        tag::{ExprTag, Tag},
    };

    use super::construct_list;

    #[test]
    fn test_tuples() {
        let mut cs = WitnessCS::new();
        let mut g = GlobalAllocator::default();
        let store = Store::<Fq>::default();
        let nil = store.intern_nil();
        let z_nil = store.hash_ptr(&nil);
        let nil_tag = z_nil.tag();
        g.new_const(&mut cs, nil_tag.to_field());
        g.new_const(&mut cs, *z_nil.value());
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
        assert_eq!(nil2.tag().get_value(), Some(z_nil2_ptr.tag_field()));
        assert_eq!(nil2.hash().get_value(), Some(*z_nil2_ptr.value()));

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
        assert_eq!(nil3.tag().get_value(), Some(z_nil3_ptr.tag_field()));
        assert_eq!(nil3.hash().get_value(), Some(*z_nil3_ptr.value()));

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
        assert_eq!(nil4.tag().get_value(), Some(z_nil4_ptr.tag_field()));
        assert_eq!(nil4.hash().get_value(), Some(*z_nil4_ptr.value()));
    }

    #[test]
    fn test_list() {
        let mut cs = WitnessCS::new();
        let mut g = GlobalAllocator::default();
        let store = Store::<Fq>::default();
        let one = Ptr::num_u64(1);
        let nil = store.intern_nil();
        let z_one = store.hash_ptr(&one);
        let z_nil = store.hash_ptr(&nil);
        g.new_const(&mut cs, z_nil.tag_field());
        g.new_const(&mut cs, *z_nil.value());
        g.new_const(&mut cs, z_one.tag_field());
        g.new_const(&mut cs, *z_one.value());
        g.new_const(&mut cs, ExprTag::Cons.to_field());
        let a_one = g.get_allocated_ptr(z_one.tag(), *z_one.value()).unwrap();

        // proper list
        let a_list = construct_list(
            &mut cs.namespace(|| "proper list"),
            &g,
            &store,
            &[&a_one, &a_one],
            None,
        )
        .unwrap();
        let z_list = store.hash_ptr(&store.list(vec![one, one]));
        assert_eq!(a_list.tag().get_value(), Some(z_list.tag_field()));
        assert_eq!(a_list.hash().get_value(), Some(*z_list.value()));

        // improper list
        let a_list = construct_list(
            &mut cs.namespace(|| "improper list"),
            &g,
            &store,
            &[&a_one, &a_one],
            Some(a_one.clone()),
        )
        .unwrap();
        let z_list = store.hash_ptr(&store.improper_list(vec![one, one], one));
        assert_eq!(a_list.tag().get_value(), Some(z_list.tag_field()));
        assert_eq!(a_list.hash().get_value(), Some(*z_list.value()));
    }
}
