//! This module provides a general mechanism for synthesizing a circuit for a minimized Foil instance.

use std::collections::HashSet;
use std::fmt::Debug;

use bellpepper::gadgets::num::AllocatedNum;
use bellpepper_core::{Circuit, ConstraintSystem, SynthesisError};

use crate::{Id, MappedFoil, MetaData, MetaMapper};
use lurk::field::LurkField;

pub trait Relation<F: LurkField>: Debug {
    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        _cs: &mut CS,
        _allocated_head: AllocatedNum<F>,
        _successors: Vec<AllocatedNum<F>>,
    ) -> Result<(), SynthesisError> {
        unimplemented!()
    }
}

// This is an incomplete schematic sketch of what synthesis should entail. NOTE: the simplicity and uniformity of this
// last-mile conversion to a circuit. Most circuit-specific heavy lifting will be concentrated in the individual
// `Relation` implementations.
impl<T: PartialEq + Clone, F: LurkField, M: MetaData, R: Relation<F>, MR: MetaMapper<M, R>>
    Circuit<F> for MappedFoil<T, M, R, MR>
{
    fn synthesize<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let foil = self.foil;
        assert!(
            foil.is_minimized(),
            "only minimized Foils can be synthesized"
        );

        let partition = foil.graph.partition();
        let _classes = partition.classes().clone();

        let allocated = foil
            .graph
            .vertices()
            .iter()
            .enumerate()
            .map(|(i, vertex)| {
                AllocatedNum::alloc(
                    &mut cs.namespace(|| format!("allocated-{i}-{vertex}")),
                    //|| todo!("get from witness, calculate, or get as constant..."),
                    || Ok(F::ZERO), // Just for initial testing.
                )
            })
            .collect::<Result<Vec<_>, SynthesisError>>()?;

        let mut constrained: HashSet<Id> = Default::default();
        // for constructor in foil.schema.constructors.iter() {
        //     let _projectors = constructor.projectors();
        //     todo!();
        // }

        for (i, (representative_id, _)) in partition.classes.iter().enumerate() {
            let vertex = foil.graph.vertex(*representative_id);
            let allocated_head = allocated[i].clone();

            //if todo!("determine whether this vertex requires allocation") {
            if true {
                // For example, projectors do not require allocation given that they will be constrained by their
                // corresponding constructor. This *could* be handled at the `Relation` level, however, in general this
                // decision may require more global context -- so for now, consider that it should be made in the
                // top-level `synthesize` method.

                // Currently, so-called `Bindings` (equivalences specified through the graph) become trivial after
                // finalization. There is no reason to allocate variables for them or add any related constraints. The
                // right answer is probably that minimization should remove them -- along with any other superfluous
                // nodes of the graph.
                //
                // The point is that some parts of the decision (whether a given vertex needs constraints of its own)
                // should probably be handled upstream. What is important is that we clearly understand the separation
                // of concerns -- so decisions at each stage do not rely on invalid assumptions about the
                // responsibilities of others. Some redundancy may therefore be appropriate.
                //
                // For example, in the case of bindings, all of the following could be implemented:
                //
                // - A full 'minimization' can remove them (with a check to ensure they were indeed enforced -- which
                // means their successors have been made equivalent). This implies that the bindings themselves will not
                // be seen here.

                // - If they do appear here, we can detect that and not allocate or constrain them. However, note that
                // maybe this is the wrong approach -- since it will require increasing knowledge of semantics here. Not
                // special-casing would be simplest. One answer is to ensure that `Func`s can be defined in such a way
                // as to provide hints here. Designation of `Bindings` (in the constructors example) as `equivalences`
                // is effectively such an annotation, but it may be useful to provide a more general (probably
                // trait-based) mechanism.
                //
                // - If we do reach the point of constraining such nodes, their defined `Relation::synthesize` method
                // can be a no-op.

                constrained.insert(*representative_id);

                let allocated_successors = vertex
                    .successors()
                    .borrow()
                    .iter()
                    .map(|successor_id| {
                        constrained.insert(*successor_id);
                        allocated[*successor_id].clone()
                    })
                    .collect::<Vec<_>>();

                let relation = {
                    self.mapper
                        .find(vertex.metadata())
                        .unwrap_or_else(|| panic!("relation missing for {:?}", vertex.metadata()))
                };

                // dbg!(relation);

                relation.synthesize(
                    &mut cs.namespace(|| format!("relation-{}", i)),
                    allocated_head,
                    allocated_successors,
                )?;
            }
        }

        // Every allocation has been constrained.
        assert_eq!(constrained.len(), partition.size());

        Ok(())
    }
}
