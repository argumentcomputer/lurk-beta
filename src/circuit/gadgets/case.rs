use super::constraints::{alloc_is_zero, pick};
use super::data::GlobalAllocations;

use crate::field::LurkField;

use bellperson::{
    gadgets::boolean::{AllocatedBit, Boolean},
    gadgets::num::AllocatedNum,
    ConstraintSystem, SynthesisError,
};
use itertools::Itertools;

use std::collections::HashSet;
use std::fmt::Debug;

/*
Initialized map entry for a fixed `key` with
an allocated `value` computed at runtime.
*/
pub struct CaseClause<'a, F: LurkField> {
    pub key: F,
    pub value: &'a AllocatedNum<F>,
}

impl<F: LurkField + Debug> Debug for CaseClause<'_, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CaseClause")
            .field("key", &self.key)
            .field(
                "value",
                &format!(
                    "AllocatedNum {{ value: {:?}, variable: {:?} }}",
                    self.value.get_value(),
                    self.value.get_variable()
                ),
            )
            .finish()
    }
}

/*
An allocated `selected_key` supposedly equal to one of the fixed keys
in the list of allocated map entries defined in `clauses`.
*/
pub struct CaseConstraint<'a, F: LurkField> {
    selected_key: AllocatedNum<F>,
    clauses: &'a [CaseClause<'a, F>],
}

impl<F: LurkField> CaseConstraint<'_, F> {
    /*
    This function returns not only the result of selection, but also the
    selector, a vector of selection bits, where exactly one bit is 1, and
    others are 0, such that it can be reused later.
    */
    fn enforce_selection<CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
        zero: &AllocatedNum<F>,
    ) -> Result<(AllocatedNum<F>, Vec<AllocatedBit>), SynthesisError> {
        // Allocate one bit per clause, called selection bit. This creates
        // constraints enforcing that each bit is 0 or 1. In fact, the
        // 'selected' clause will have selection bit = 1 while the others
        // are 0. This will be confirmed/enforced by later constraints.
        let mut selector = Vec::with_capacity(self.clauses.len());
        // check each key is only included once
        debug_assert!({
            let mut uniq = HashSet::new();
            self.clauses
                .iter()
                .all(|clause| uniq.insert(clause.key.to_bytes()))
        });

        for (i, clause) in self.clauses.iter().enumerate() {
            let is_selected = if let Some(value) = self.selected_key.get_value() {
                clause.key == value
            } else {
                false
            };
            selector.push(AllocatedBit::alloc(
                cs.namespace(|| format!("selection bit {i}")),
                Some(is_selected),
            )?);
        }

        // We add up all bits. If the result is 1, then it means
        // there is exactly one bit equal 1, while others are 0.
        // This guarantees we don't have repeated selected keys.
        // ( ∑ᵢ 1 ⋅ selectorᵢ ) * ( 1 ) = ( 1 )
        cs.enforce(
            || "exactly one selector is 1",
            |lc| {
                selector
                    .iter()
                    .fold(lc, |lc, selector| lc + selector.get_variable())
            },
            |lc| lc + CS::one(),
            |lc| lc + CS::one(),
        );

        // Apply selection.
        // ( ∑ᵢ keyᵢ ⋅ selectorᵢ ) * (1) = selected_key
        cs.enforce(
            || "selection vector dot keys = selected",
            |lc| {
                selector
                    .iter()
                    .zip(self.clauses)
                    .fold(lc, |lc, (selector, clause)| {
                        lc + (clause.key, selector.get_variable())
                    })
            },
            |lc| lc + CS::one(),
            |lc| lc + self.selected_key.get_variable(),
        );

        let values = self
            .clauses
            .iter()
            .map(|c| c.value.clone())
            .collect::<Vec<_>>();

        // result ← ∑ᵢ  selectorᵢ ⋅ valueᵢ
        let result = selector_dot_product(
            &mut cs.namespace(|| "extract result"),
            &selector,
            values.as_slice(),
            zero,
        )?;

        Ok((result, selector))
    }
}

/*
Returns ∑ᵢ  selector[i] ⋅ value_vector[i].
*/
fn selector_dot_product<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    selector: &[AllocatedBit],
    value_vector: &[AllocatedNum<F>],
    zero: &AllocatedNum<F>, // Must be a constant-allocated zero.
) -> Result<AllocatedNum<F>, SynthesisError> {
    let mut computed_result = F::zero();

    let mut all_products = Vec::new();

    for (i, (bit, value)) in selector.iter().zip(value_vector).enumerate() {
        let allocated_prod = pick(
            &mut cs.namespace(|| format!("allocated_prod {i}")),
            &Boolean::Is(bit.clone()),
            value,
            zero,
        )?;

        all_products.push(allocated_prod.clone());

        if let Some(prod) = allocated_prod.get_value() {
            computed_result += prod;
        };
    }
    let result = AllocatedNum::<F>::alloc(&mut cs.namespace(|| "result"), || Ok(computed_result))?;

    cs.enforce(
        || "sum of products",
        |lc| {
            all_products
                .iter()
                .fold(lc, |acc, prod| acc + prod.get_variable())
        },
        |lc| lc + CS::one(),
        |lc| lc + result.get_variable(),
    );

    Ok(result)
}

/*
Selects the clause whose key is equal to selected and returns its value,
or if no key is selected, returns the default.
*/
pub fn case<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    selected: &AllocatedNum<F>,
    clauses: &[CaseClause<F>],
    default: &AllocatedNum<F>,
    g: &GlobalAllocations<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    multi_case(cs, selected, &[clauses], &[default], g).map(|r| r[0].to_owned())
}

/*
Selects the clauses whose key is equal to selected and returns
a vector containing the corresponding values, or if no key is selected,
returns the default.
*/
pub fn multi_case<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    selected: &AllocatedNum<F>,
    cases: &[&[CaseClause<F>]],
    defaults: &[&AllocatedNum<F>],
    g: &GlobalAllocations<F>,
) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
    let result = multi_case_aux(cs, selected, cases, defaults, g)?;
    let selected = result.0;
    Ok(selected)
}

/*
 * Returns not only the selected clause, but also a Boolean that can
 * be used to determine if the default clause was returned.
 */
pub fn multi_case_aux<F: LurkField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    selected: &AllocatedNum<F>,
    cases: &[&[CaseClause<F>]],
    defaults: &[&AllocatedNum<F>],
    g: &GlobalAllocations<F>,
) -> Result<(Vec<AllocatedNum<F>>, Boolean), SynthesisError> {
    debug_assert!(!cases.is_empty());
    debug_assert_eq!(cases.len(), defaults.len());
    debug_assert!(!cases[0].is_empty());
    // All sets of clauses must specify the same keys in the same order.
    debug_assert!(cases
        .iter()
        .map(|x| x.iter().map(|clause| clause.key).collect::<Vec<_>>())
        .all_equal());

    let mut result = Vec::new();

    // First clause in the list allows to constrain the selected key,
    // which must be the same (including ordering) in other clauses.
    let (selector, is_default) = {
        let i = 0;
        let c = cases[0];
        let default = defaults[0];

        let mut any_selected = false;

        // acc ← 1
        let mut acc = g.true_num.clone();

        for (i, clause) in c.iter().enumerate() {
            if Some(clause.key) == selected.get_value() {
                any_selected = true;
            }
            let mut x = clause.key;
            let mut selected_present = false;

            if let Some(s) = selected.get_value() {
                selected_present = true;
                x.sub_assign(&s);
            };

            if let Some(a) = acc.get_value() {
                x.mul_assign(&a)
            };

            // new_acc ← x = acc * (clause.key[i] - selected)
            let new_acc = AllocatedNum::alloc(
                &mut cs.namespace(|| format!("acc {}, case {i}", i + 1)),
                || {
                    if selected_present {
                        Ok(x)
                    } else {
                        Err(SynthesisError::AssignmentMissing)
                    }
                },
            )?;

            // acc * ( clause.key - selected ) = new_acc
            cs.enforce(
                || format!("acc * (clause-{i}.key - selected) = new_acc, case {i}"),
                |lc| lc + acc.get_variable(),
                |_| Boolean::Constant(true).lc(CS::one(), clause.key) - selected.get_variable(),
                |lc| lc + new_acc.get_variable(),
            );

            acc = new_acc;
        }

        // acc = ∏ᵢ (clause[i].key - selected)
        // Therefore acc is zero if and only if some key was selected.
        let is_selected = alloc_is_zero(cs.namespace(|| format!("is_selected, case {i}")), &acc)?;

        // If no selection matched, use a dummy key so constraints are met.
        // We will actually return the default value, though.
        let dummy_key = c[0].key;
        let selected_key = AllocatedNum::alloc(cs.namespace(|| "default key"), || {
            if any_selected {
                selected
                    .get_value()
                    .ok_or(SynthesisError::AssignmentMissing)
            } else {
                Ok(dummy_key)
            }
        })?;

        // enforce_selection() guarantees no repeated selected keys exist
        // and returns a tuple containing the result and the selector
        let cc = CaseConstraint {
            selected_key,
            clauses: c,
        };
        let zero = &g.false_num;
        let (enforced_result, selector) =
            cc.enforce_selection(&mut cs.namespace(|| format!("case {i}")), zero)?;

        // If no selection matched, choose the default value
        let is_default = is_selected.not();

        result.push(pick(
            &mut cs.namespace(|| format!("maybe default, case {i}")),
            &is_default,
            default,
            &enforced_result,
        )?);

        (selector, is_default)
    };

    // Now that we constrained the selector, we can constrain the selection
    // of the corresponding values in next clauses
    // 1..n
    for (i, (c, default)) in cases.iter().zip(defaults).enumerate().skip(1) {
        // Ensure key ordering actually matches
        for (j, case) in c.iter().enumerate() {
            debug_assert_eq!(case.key, cases[0][j].key, "Key ordering mismatch {i}:{j}");
        }

        let values = c
            .iter()
            .map(|clause| clause.value.clone())
            .collect::<Vec<_>>();

        let zero = &g.false_num;
        let next_enforced_value = selector_dot_product(
            &mut cs.namespace(|| format!("extract result, case {i}")),
            &selector,
            &values,
            zero,
        )?;
        result.push(pick(
            &mut cs.namespace(|| format!("maybe default, case {i}")),
            &is_default,
            default,
            &next_enforced_value,
        )?);
    }

    Ok((result, is_default))
}

#[allow(unused_imports)]
mod tests {
    use blstrs::Scalar as Fr;

    use super::*;
    use crate::store::Store;

    use bellperson::util_cs::{
        metric_cs::MetricCS, test_cs::TestConstraintSystem, Comparable, Delta,
    };

    #[test]
    fn simple_case() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        let g = GlobalAllocations::new(&mut cs, s).unwrap();

        let x = Fr::from(123);
        let y = Fr::from(124);
        let selected = AllocatedNum::alloc(cs.namespace(|| "selected"), || Ok(x)).unwrap();
        let val0 = AllocatedNum::alloc(cs.namespace(|| "val0"), || Ok(Fr::from(666))).unwrap();
        let val1 = AllocatedNum::alloc(cs.namespace(|| "val1"), || Ok(Fr::from(777))).unwrap();
        let default =
            AllocatedNum::alloc(cs.namespace(|| "default_v"), || Ok(Fr::from(999))).unwrap();

        {
            let clauses = [
                CaseClause {
                    key: x,
                    value: &val0,
                },
                CaseClause {
                    key: y,
                    value: &val1,
                },
            ];

            let result = case(
                &mut cs.namespace(|| "selected case"),
                &selected,
                &clauses,
                &default,
                &g,
            )
            .unwrap();

            assert_eq!(val0.get_value(), result.get_value());
            assert!(cs.is_satisfied());
        }

        {
            let clauses = [CaseClause {
                key: y,
                value: &val0,
            }];

            let default_chosen =
                AllocatedNum::alloc(cs.namespace(|| "default chosen"), || Ok(Fr::from(999)))
                    .unwrap();
            let result = case(
                &mut cs.namespace(|| "default case"),
                &selected,
                &clauses,
                &default_chosen,
                &g,
            )
            .unwrap();

            assert_eq!(default.get_value(), result.get_value());
            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn multicase() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        let g = GlobalAllocations::new(&mut cs, s).unwrap();

        let x = Fr::from(123);
        let y = Fr::from(124);
        let z = Fr::from(125);
        let selected0 = AllocatedNum::alloc(cs.namespace(|| "selected0"), || Ok(x)).unwrap();
        let selected1 = AllocatedNum::alloc(cs.namespace(|| "selected1"), || Ok(z)).unwrap();
        let val0 = AllocatedNum::alloc(cs.namespace(|| "val0"), || Ok(Fr::from(666))).unwrap();
        let val1 = AllocatedNum::alloc(cs.namespace(|| "val1"), || Ok(Fr::from(777))).unwrap();
        let val2 = AllocatedNum::alloc(cs.namespace(|| "val2"), || Ok(Fr::from(700))).unwrap();
        let default_vec = [
            &AllocatedNum::alloc(cs.namespace(|| "default0"), || Ok(Fr::from(999))).unwrap(),
            &AllocatedNum::alloc(cs.namespace(|| "default1"), || Ok(Fr::from(998))).unwrap(),
            &AllocatedNum::alloc(cs.namespace(|| "default2"), || Ok(Fr::from(997))).unwrap(),
        ];

        {
            let clauses0: [CaseClause<Fr>; 2] = [
                CaseClause {
                    key: x,
                    value: &val0,
                },
                CaseClause {
                    key: y,
                    value: &val1,
                },
            ];
            let clauses1: [CaseClause<Fr>; 2] = [
                CaseClause {
                    key: x,
                    value: &val1,
                },
                CaseClause {
                    key: y,
                    value: &val0,
                },
            ];
            let clauses2: [CaseClause<Fr>; 2] = [
                CaseClause {
                    key: x,
                    value: &val2,
                },
                CaseClause {
                    key: y,
                    value: &val0,
                },
            ];
            let clauses_vec: [&[CaseClause<Fr>]; 3] = [&clauses0, &clauses1, &clauses2];

            // Test regular multicase, select first clause
            let mut result = multi_case(
                &mut cs.namespace(|| "selected case 0"),
                &selected0,
                &clauses_vec,
                &default_vec,
                &g,
            )
            .unwrap();

            assert_eq!(val0.get_value(), result[0].get_value());
            assert_eq!(val1.get_value(), result[1].get_value());
            assert_eq!(val2.get_value(), result[2].get_value());
            assert!(cs.is_satisfied());

            // Test regular multicase, select default
            result = multi_case(
                &mut cs.namespace(|| "selected case 1"),
                &selected1,
                &clauses_vec,
                &default_vec,
                &g,
            )
            .unwrap();

            assert_eq!(default_vec[0].get_value(), result[0].get_value());
            assert_eq!(default_vec[1].get_value(), result[1].get_value());
            assert_eq!(default_vec[2].get_value(), result[2].get_value());
            assert!(cs.is_satisfied());
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic]
    fn multicase_negative1_panic() {
        multicase_negative1_aux();
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn multicase_negative1_unsatisfied() {
        multicase_negative1_aux();
    }

    #[allow(dead_code)]
    fn multicase_negative1_aux() {
        // Test invalid multicase (repeated keys)
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        let g = GlobalAllocations::new(&mut cs, s).unwrap();

        let x = Fr::from(123);
        let z = Fr::from(125);
        let selected = AllocatedNum::alloc(cs.namespace(|| "selected"), || Ok(z)).unwrap();
        let val0 = AllocatedNum::alloc(cs.namespace(|| "val0"), || Ok(Fr::from(666))).unwrap();
        let val1 = AllocatedNum::alloc(cs.namespace(|| "val1"), || Ok(Fr::from(777))).unwrap();
        let val2 = AllocatedNum::alloc(cs.namespace(|| "val2"), || Ok(Fr::from(700))).unwrap();

        let default_vec = [
            &AllocatedNum::alloc(cs.namespace(|| "default0"), || Ok(Fr::from(999))).unwrap(),
            &AllocatedNum::alloc(cs.namespace(|| "default1"), || Ok(Fr::from(998))).unwrap(),
        ];

        let clauses0: [CaseClause<Fr>; 2] = [
            CaseClause {
                key: x,
                value: &val0,
            },
            CaseClause {
                key: x,
                value: &val1,
            },
        ];
        let clauses1: [CaseClause<Fr>; 2] = [
            CaseClause {
                key: x,
                value: &val2,
            },
            CaseClause {
                key: x,
                value: &val0,
            },
        ];

        // Test repeated keys
        let invalid_clauses_vec: [&[CaseClause<Fr>]; 2] = [&clauses0, &clauses1];

        let _ = multi_case(
            &mut cs.namespace(|| "selected case"),
            &selected,
            &invalid_clauses_vec,
            &default_vec,
            &g,
        );
        assert!(!cs.is_satisfied());
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "assertion failed: `(left == right)")]
    fn multicase_negative2() {
        // Test invalid multicase (keys ording doesn't match)
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        let g = GlobalAllocations::new(&mut cs, s).unwrap();

        let x = Fr::from(123);
        let y = Fr::from(124);
        let z = Fr::from(125);
        let selected = AllocatedNum::alloc(cs.namespace(|| "selected"), || Ok(z)).unwrap();
        let val0 = AllocatedNum::alloc(cs.namespace(|| "val0"), || Ok(Fr::from(666))).unwrap();
        let val1 = AllocatedNum::alloc(cs.namespace(|| "val1"), || Ok(Fr::from(777))).unwrap();
        let val2 = AllocatedNum::alloc(cs.namespace(|| "val2"), || Ok(Fr::from(700))).unwrap();

        let default_vec = [
            &AllocatedNum::alloc(cs.namespace(|| "default0"), || Ok(Fr::from(999))).unwrap(),
            &AllocatedNum::alloc(cs.namespace(|| "default1"), || Ok(Fr::from(998))).unwrap(),
            &AllocatedNum::alloc(cs.namespace(|| "default2"), || Ok(Fr::from(997))).unwrap(),
        ];

        let clauses0: [CaseClause<Fr>; 2] = [
            CaseClause {
                key: x,
                value: &val0,
            },
            CaseClause {
                key: y,
                value: &val1,
            },
        ];
        let clauses1: [CaseClause<Fr>; 2] = [
            CaseClause {
                key: y,
                value: &val2,
            },
            CaseClause {
                key: x,
                value: &val0,
            },
        ];

        let invalid_clauses_vec: [&[CaseClause<Fr>]; 2] = [&clauses0, &clauses1];

        // Test keys ordering
        let _ = multi_case(
            &mut cs.namespace(|| "selected case"),
            &selected,
            &invalid_clauses_vec,
            &default_vec,
            &g,
        );
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic]
    fn multicase_negative3() {
        // Test invalid multicase (clauses sizes doesn't match)
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        let g = GlobalAllocations::new(&mut cs, s).unwrap();

        let x = Fr::from(123);
        let y = Fr::from(124);
        let z = Fr::from(125);
        let selected = AllocatedNum::alloc(cs.namespace(|| "selected"), || Ok(z)).unwrap();
        let val0 = AllocatedNum::alloc(cs.namespace(|| "val0"), || Ok(Fr::from(666))).unwrap();
        let val1 = AllocatedNum::alloc(cs.namespace(|| "val1"), || Ok(Fr::from(777))).unwrap();
        let val2 = AllocatedNum::alloc(cs.namespace(|| "val2"), || Ok(Fr::from(700))).unwrap();

        let default_vec = [
            &AllocatedNum::alloc(cs.namespace(|| "default0"), || Ok(Fr::from(999))).unwrap(),
            &AllocatedNum::alloc(cs.namespace(|| "default1"), || Ok(Fr::from(998))).unwrap(),
        ];

        let clauses0: [CaseClause<Fr>; 2] = [
            CaseClause {
                key: x,
                value: &val0,
            },
            CaseClause {
                key: y,
                value: &val1,
            },
        ];
        let clauses1: [CaseClause<Fr>; 3] = [
            CaseClause {
                key: x,
                value: &val2,
            },
            CaseClause {
                key: y,
                value: &val2,
            },
            CaseClause {
                key: x,
                value: &val0,
            },
        ];

        // Test invalid clauses sizes
        let invalid_clauses_vec: [&[CaseClause<Fr>]; 2] = [&clauses0, &clauses1];

        let _ = multi_case(
            &mut cs.namespace(|| "selected case"),
            &selected,
            &invalid_clauses_vec,
            &default_vec,
            &g,
        );
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "assertion failed: !cases.is_empty()")]
    fn multicase_negative4() {
        // Test invalid multicase (empty clauses)
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        let g = GlobalAllocations::new(&mut cs, s).unwrap();

        let x = Fr::from(123);
        let selected = AllocatedNum::alloc(cs.namespace(|| "selected"), || Ok(x)).unwrap();
        let default_vec = [
            &AllocatedNum::alloc(cs.namespace(|| "default0"), || Ok(Fr::from(999))).unwrap(),
            &AllocatedNum::alloc(cs.namespace(|| "default1"), || Ok(Fr::from(998))).unwrap(),
        ];

        let _ = multi_case(
            &mut cs.namespace(|| "selected case"),
            &selected,
            &[],
            &default_vec,
            &g,
        );
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic]
    fn multicase_negative5() {
        // Test invalid multicase (empty defaults)
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        let g = GlobalAllocations::new(&mut cs, s).unwrap();

        let x = Fr::from(123);
        let y = Fr::from(124);
        let selected = AllocatedNum::alloc(cs.namespace(|| "selected"), || Ok(x)).unwrap();
        let val0 = AllocatedNum::alloc(cs.namespace(|| "val0"), || Ok(Fr::from(666))).unwrap();
        let val1 = AllocatedNum::alloc(cs.namespace(|| "val1"), || Ok(Fr::from(777))).unwrap();
        let val2 = AllocatedNum::alloc(cs.namespace(|| "val2"), || Ok(Fr::from(700))).unwrap();
        let clauses0: [CaseClause<Fr>; 2] = [
            CaseClause {
                key: x,
                value: &val0,
            },
            CaseClause {
                key: y,
                value: &val1,
            },
        ];
        let clauses1: [CaseClause<Fr>; 3] = [
            CaseClause {
                key: x,
                value: &val2,
            },
            CaseClause {
                key: y,
                value: &val2,
            },
            CaseClause {
                key: x,
                value: &val0,
            },
        ];
        let clauses_vec: [&[CaseClause<Fr>]; 2] = [&clauses0, &clauses1];

        // Test invalid, empty defaults
        let _ = multi_case(
            &mut cs.namespace(|| "selected case"),
            &selected,
            &clauses_vec,
            &[],
            &g,
        );
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic]
    fn multicase_negative6() {
        // Test invalid multicase (empty case).
        let mut cs = TestConstraintSystem::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        let g = GlobalAllocations::new(&mut cs, s).unwrap();

        let x = Fr::from(123);
        let y = Fr::from(124);
        let selected = AllocatedNum::alloc(cs.namespace(|| "selected"), || Ok(x)).unwrap();
        let val0 = AllocatedNum::alloc(cs.namespace(|| "val0"), || Ok(Fr::from(666))).unwrap();
        let val1 = AllocatedNum::alloc(cs.namespace(|| "val1"), || Ok(Fr::from(777))).unwrap();
        let default_vec = [
            &AllocatedNum::alloc(cs.namespace(|| "default0"), || Ok(Fr::from(999))).unwrap(),
            &AllocatedNum::alloc(cs.namespace(|| "default1"), || Ok(Fr::from(998))).unwrap(),
        ];
        let clauses0: [CaseClause<Fr>; 2] = [
            CaseClause {
                key: x,
                value: &val0,
            },
            CaseClause {
                key: y,
                value: &val1,
            },
        ];
        let clauses1 = [];
        let clauses_vec: [&[CaseClause<Fr>]; 2] = [&clauses0, &clauses1];

        // Test invalid, empty clauses.
        let _ = multi_case(
            &mut cs.namespace(|| "selected case"),
            &selected,
            &clauses_vec,
            &default_vec,
            &g,
        );
    }

    #[test]
    fn groth_case() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let mut cs_blank = MetricCS::<Fr>::new();
        let s = &mut Store::<Fr>::default();
        let g = GlobalAllocations::new(&mut cs, s).unwrap();
        let g_blank = GlobalAllocations::new(&mut cs_blank, s).unwrap();

        let x = Fr::from(123);
        let y = Fr::from(124);
        let selected = AllocatedNum::alloc(cs.namespace(|| "selected"), || Ok(x)).unwrap();
        let _selected_blank = AllocatedNum::alloc(cs_blank.namespace(|| "selected"), || {
            Err(SynthesisError::AssignmentMissing)
        })
        .unwrap();
        let val0 = AllocatedNum::alloc(cs.namespace(|| "val0"), || Ok(Fr::from(666))).unwrap();
        let val0_blank = AllocatedNum::alloc(cs_blank.namespace(|| "val0"), || {
            Err(SynthesisError::AssignmentMissing)
        })
        .unwrap();
        let val1 = AllocatedNum::alloc(cs.namespace(|| "val1"), || Ok(Fr::from(777))).unwrap();
        let val1_blank = AllocatedNum::alloc(cs_blank.namespace(|| "val1"), || {
            Err(SynthesisError::AssignmentMissing)
        })
        .unwrap();
        let default =
            AllocatedNum::alloc(cs.namespace(|| "default_v"), || Ok(Fr::from(999))).unwrap();
        let default_blank = AllocatedNum::alloc(cs_blank.namespace(|| "default_v"), || {
            Err(SynthesisError::AssignmentMissing)
        })
        .unwrap();

        {
            let clauses = [
                CaseClause {
                    key: x,
                    value: &val0,
                },
                CaseClause {
                    key: y,
                    value: &val1,
                },
            ];

            let result = case(
                &mut cs.namespace(|| "selected case"),
                &selected,
                &clauses,
                &default,
                &g,
            )
            .unwrap();

            assert_eq!(val0.get_value(), result.get_value());
            assert!(cs.is_satisfied());
        }
        {
            let clauses_blank = [
                CaseClause {
                    key: x,
                    value: &val0_blank,
                },
                CaseClause {
                    key: y,
                    value: &val1_blank,
                },
            ];

            let _result = case(
                &mut cs_blank.namespace(|| "selected case"),
                &selected,
                &clauses_blank,
                &default_blank,
                &g_blank,
            )
            .unwrap();

            assert!(cs.is_satisfied());
        }

        let delta = cs.delta(&cs_blank, false);
        assert!(delta == Delta::Equal);
    }
}
