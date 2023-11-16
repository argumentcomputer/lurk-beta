use std::collections::HashMap;

use bellpepper_core::{num::AllocatedNum, ConstraintSystem, SynthesisError};

use neptune::circuit2::poseidon_hash_allocated as poseidon_hash;
use neptune::circuit2_witness::poseidon_hash_allocated_witness;

use crate::field::{FWrap, LurkField};
use crate::hash::HashConst;
use crate::hash_witness::{Digest, WitnessBlock};

type HashCircuitWitnessCache<F> = HashMap<Vec<FWrap<F>>, (Vec<F>, F)>;

impl<'a, F: LurkField> HashConst<'a, F> {
    pub(crate) fn hash<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        preimage: Vec<AllocatedNum<F>>,
        hash_circuit_witness_cache: Option<&mut HashCircuitWitnessCache<F>>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        let witness_block = if cs.is_witness_generator() {
            hash_circuit_witness_cache.map(|cache| {
                let key = preimage
                    .iter()
                    .map(|allocated| FWrap(allocated.get_value().unwrap()))
                    .collect::<Vec<_>>();

                let cached = cache.get(&key).unwrap();
                cached
            })
        } else {
            None
        };

        self.hash_with_witness(cs, preimage, witness_block)
    }

    fn hash_with_witness<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        preimage: Vec<AllocatedNum<F>>,
        circuit_witness: Option<&(WitnessBlock<F>, Digest<F>)>,
    ) -> Result<AllocatedNum<F>, SynthesisError> {
        macro_rules! hash {
            ($c:ident) => {
                if cs.is_witness_generator() {
                    if let Some((aux_buf, res)) = circuit_witness {
                        cs.extend_aux(aux_buf);

                        AllocatedNum::alloc(cs, || Ok(*res))
                    } else {
                        // We have no cache, just allocate the witness.
                        poseidon_hash_allocated_witness(cs, &preimage, $c)
                    }
                } else {
                    // CS is not a witness generator, just hash.
                    poseidon_hash(cs, preimage, $c)
                }
            };
        }
        match self {
            HashConst::A3(c) => hash!(c),
            HashConst::A4(c) => hash!(c),
            HashConst::A6(c) => hash!(c),
            HashConst::A8(c) => hash!(c),
        }
    }
}
