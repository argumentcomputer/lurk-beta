// Initially taken from: rust-fil-proofs/storage-proofs-core/src/gadgets/
use crate::{circuit::gadgets::constraints::*, field::LurkField};
use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    ConstraintSystem, SynthesisError,
};
use ff::PrimeField;

/// If premise is true, enforce `a` fits into 64 bits. It shows a non-deterministic
/// partial bit decomposition in order to constraint correct behavior.
pub(crate) fn implies_u64<F: LurkField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    premise: &Boolean,
    a: &AllocatedNum<F>,
) -> Result<(), SynthesisError> {
    let mut a_u64 = a.get_value().and_then(|a| a.to_u64()).unwrap_or(0);

    let mut bits: Vec<Boolean> = Vec::with_capacity(64);
    for i in 0..64 {
        let b = a_u64 & 1;
        let b_bool = Boolean::Is(AllocatedBit::alloc(
            &mut cs.namespace(|| format!("b.{i}")),
            Some(b == 1),
        )?);
        bits.push(b_bool);

        a_u64 /= 2;
    }

    // premise -> a = sum(bits)
    implies_pack(
        &mut cs.namespace(|| "u64 bit decomposition check"),
        premise,
        &bits,
        a,
    )?;

    Ok(())
}

/// Adds a constraint to CS, enforcing that the number of true bits in `Boolean` vector `v`
/// is equal to one, if the premise is true.
///
/// summation(v) = one (if premise)
pub(crate) fn enforce_selector_with_premise<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    premise: &Boolean,
    v: &[Boolean],
) -> Result<(), SynthesisError> {
    let popcount = popcount_lc::<F, CS>(v)?;

    enforce_implication_lc(cs, premise, |_| popcount)
}

/// Enforce equality of an allocated number and a constant given an implication premise
pub(crate) fn implies_equal_const<CS: ConstraintSystem<F>, F: PrimeField>(
    cs: &mut CS,
    premise: &Boolean,
    a: &AllocatedNum<F>,
    b: F,
) -> Result<(), SynthesisError> {
    enforce_implication_lc_zero(cs, premise, |lc| lc + a.get_variable() - (b, CS::one()))
}

/// Enforce inequality of two allocated numbers given an implication premise
pub(crate) fn implies_unequal<CS: ConstraintSystem<F>, F: PrimeField>(
    cs: &mut CS,
    premise: &Boolean,
    a: &AllocatedNum<F>,
    b: &AllocatedNum<F>,
) -> Result<(), SynthesisError> {
    // We know that `a != b` iff `a-b` has an inverse, i.e. that there exists
    // `q` such that `q * (a-b) = 1`. Thus, we can add the constraint that there
    // must exist `q` such that `q * (a-b) = premise`, enforcing the difference
    // only when `premise = 1`; otherwise the constraint is trivially satisfied
    // for `q = 0`
    let q = cs.alloc(
        || "q",
        || {
            let premise = premise
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            if premise {
                let a = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let b = b.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let inv = (a - b).invert();
                if inv.is_some().into() {
                    Ok(inv.unwrap())
                } else {
                    Ok(F::ZERO)
                }
            } else {
                Ok(F::ZERO)
            }
        },
    )?;
    let maybe_inverse = |lc| lc + q;
    let implication_lc = |lc| lc + a.get_variable() - b.get_variable();
    let premise = |_| premise.lc(CS::one(), F::ONE);

    cs.enforce(|| "implication", maybe_inverse, implication_lc, premise);
    Ok(())
}

/// Enforce inequality of two allocated numbers given an implication premise
pub(crate) fn implies_unequal_const<CS: ConstraintSystem<F>, F: PrimeField>(
    cs: &mut CS,
    premise: &Boolean,
    a: &AllocatedNum<F>,
    b: F,
) -> Result<(), SynthesisError> {
    // We know that `a != b` iff `a-b` has an inverse, i.e. that there exists
    // `q` such that `q * (a-b) = 1`. Thus, we can add the constraint that there
    // must exist `q` such that `q * (a-b) = premise`, enforcing the difference
    // only when `premise = 1`; otherwise the constraint is trivially satisfied
    // for `q = 0`
    let q = cs.alloc(
        || "q",
        || {
            let premise = premise
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            if premise {
                let a = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let inv = (a - b).invert();
                if inv.is_some().into() {
                    Ok(inv.unwrap())
                } else {
                    Ok(F::ZERO)
                }
            } else {
                Ok(F::ZERO)
            }
        },
    )?;
    let maybe_inverse = |lc| lc + q;
    let implication_lc = |lc| lc + a.get_variable() - (b, CS::one());
    let premise = |_| premise.lc(CS::one(), F::ONE);

    cs.enforce(|| "implication", maybe_inverse, implication_lc, premise);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use bellpepper_core::test_cs::TestConstraintSystem;
    use blstrs::Scalar as Fr;
    use proptest::prelude::*;

    use crate::field::FWrap;

    proptest! {
        #[test]
        fn test_implies_unequal(p in any::<bool>(), (a, b) in prop_oneof![
            any::<(FWrap<Fr>, FWrap<Fr>)>(),
            any::<FWrap<Fr>>().prop_map(|a| (a, a)),
        ]) {
            let test_a_b = |premise: bool, a, b| -> bool{
                let mut cs = TestConstraintSystem::<Fr>::new();
                let a_num = AllocatedNum::alloc(cs.namespace(|| "a_num"), || Ok(a)).unwrap();
                let b_num = AllocatedNum::alloc(cs.namespace(|| "b_num"), || Ok(b)).unwrap();
                let pb = Boolean::constant(premise);
                let _ = implies_unequal(&mut cs.namespace(|| "implies equal"), &pb, &a_num, &b_num);
                cs.is_satisfied()
            };

            prop_assert_eq!(test_a_b(p, a.0, b.0), !p || (a.0 != b.0));
        }

        #[test]
        fn test_implies_unequal_const(
            p in any::<bool>(),
            candidate in any::<FWrap<Fr>>(),
            target in any::<FWrap<Fr>>()
        ) {

            let test_premise_unequal = |premise: bool, n, t| -> bool  {
                let mut cs = TestConstraintSystem::<Fr>::new();
                let num = AllocatedNum::alloc(cs.namespace(|| "num"), || Ok(n)).unwrap();
                let pb = Boolean::constant(premise);
                let _ = implies_unequal_const(&mut cs.namespace(|| "implies equal zero"), &pb, &num, t);
                cs.is_satisfied()
            };

            prop_assert_eq!(test_premise_unequal(p, candidate.0, target.0), !p || (candidate != target));
            prop_assert_eq!(test_premise_unequal(p, target.0, target.0), !p);
        }

        #[test]
        fn test_implies_equal_const(
            p in any::<bool>(),
            candidate in any::<FWrap<Fr>>(),
            target in any::<FWrap<Fr>>()
        ) {

            let test_premise_equal = |premise: bool, n, t| -> bool  {
                let mut cs = TestConstraintSystem::<Fr>::new();
                let num = AllocatedNum::alloc(cs.namespace(|| "num"), || Ok(n)).unwrap();
                let pb = Boolean::constant(premise);
                let _ = implies_equal_const(&mut cs.namespace(|| "implies equal zero"), &pb, &num, t);
                cs.is_satisfied()
            };

            prop_assert_eq!(test_premise_equal(p, candidate.0, target.0), !p || (candidate == target));
            prop_assert!(test_premise_equal(p, target.0, target.0));
        }

        #[test]
        fn test_enforce_selector(
            p in any::<bool>(),
            (v1, v2, v3) in any::<(bool, bool, bool)>(),
            (i, j, k) in ((0usize..7), (0usize..7), (0usize..7)),
        ) {
            // get distinct indices
            prop_assume!(i != j);
            prop_assume!(j != k);
            prop_assume!(i != k);
            // initialize with false
            let mut v = vec![Boolean::constant(false); 7];
            let mut test_premise = |
                    premise: bool,
                    randomize: bool,
                    select_random: bool,
                    select_many: bool,
                    result: bool
                | {
                    if randomize {
                        v[i] = Boolean::constant(v1);
                        v[j] = Boolean::constant(v2);
                        v[k] = Boolean::constant(v3);
                    }
                    if select_random {
                        v[i] = Boolean::constant(true);
                    }
                    if select_many {
                        v[i] = Boolean::constant(true);
                        v[j] = Boolean::constant(true);
                        v[k] = Boolean::constant(true);
                    }
                    let mut cs = TestConstraintSystem::<Fr>::new();
                    let p = Boolean::Constant(premise);
                    let _ = enforce_selector_with_premise(&mut cs.namespace(|| "enforce selector with premise"), &p, &v);
                    assert_eq!(cs.is_satisfied(), result);
                };

            // select a random position
            // for any premise, test good selections
            test_premise(p, false, true, false, true);

            // if p is false, any v works
            test_premise(false, true, false, false, true);

            // select many, then must fail
            test_premise(true, false, false, true, false);

        }
    }

    #[test]
    fn test_implies_u64_negative_edge_case() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let alloc_num = AllocatedNum::alloc(&mut cs.namespace(|| "num"), || {
            // Edge case: 2ˆ64 = 18446744073709551616
            Ok(Fr::from_str_vartime("18446744073709551616").unwrap())
        })
        .unwrap();

        let t = Boolean::Constant(true);
        implies_u64(&mut cs.namespace(|| "enforce u64"), &t, &alloc_num).unwrap();
        assert!(!cs.is_satisfied());
    }

    proptest! {
        #[test]
        fn test_implies_u64(f in any::<FWrap<Fr>>()) {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let num = AllocatedNum::alloc(cs.namespace(|| "num"), || Ok(f.0)).unwrap();

            let t = Boolean::Constant(true);
            implies_u64(&mut cs.namespace(|| "enforce u64"), &t, &num).unwrap();

            let f_u64_roundtrip: Fr = f.0.to_u64_unchecked().into();
            let was_u64 = f_u64_roundtrip == f.0;
            prop_assert_eq!(was_u64, cs.is_satisfied());
        }
    }
}
