use abomonation::Abomonation;
use anyhow::Result;
use bellpepper::util_cs::witness_cs::WitnessCS;
use bellpepper_core::{num::AllocatedNum, Circuit, ConstraintSystem, SynthesisError};
use ff::PrimeField;
use nova::{supernova::NonUniformCircuit, traits::Group};
use std::sync::Arc;

use crate::{
    circuit::gadgets::pointer::AllocatedPtr,
    coprocessor::Coprocessor,
    error::{ProofError, ReductionError},
    eval::{lang::Lang, Meta},
    field::LurkField,
    proof::{
        nova::{CurveCycleEquipped, G1, G2},
        supernova::{FoldingConfig, C2},
        CEKState, EvaluationStore, FrameLike, MultiFrameTrait, Provable,
    },
    state::initial_lurk_state,
    store,
    tag::ContTag,
};

use super::{
    circuit::{BoundAllocations, GlobalAllocator},
    eval::{build_frames, make_cprocs_funcs_from_lang, make_eval_step_from_lang},
    interpreter::Frame,
    pointers::Ptr,
    store::Store,
    Func, Tag,
};

#[derive(Clone, Debug)]
pub struct MultiFrame<'a, F: LurkField, C: Coprocessor<F>> {
    store: Option<&'a Store<F>>,
    /// Cached Lurk step function according to the `folding_config`
    lurk_step: Arc<Func>,
    /// Cached coprocessor functions according to the `folding_config`. Holds
    /// `None` in case of IVC
    cprocs: Option<Arc<[Func]>>,
    input: Option<Vec<Ptr<F>>>,
    output: Option<Vec<Ptr<F>>>,
    frames: Option<Vec<Frame<F>>>,
    cached_witness: Option<WitnessCS<F>>,
    reduction_count: usize,
    folding_config: Arc<FoldingConfig<F, C>>,
    pc: usize,
    next_pc: usize,
}

impl<'a, F: LurkField, C: Coprocessor<F>> MultiFrame<'a, F, C> {
    fn get_func(&self) -> &Func {
        if self.pc == 0 {
            &self.lurk_step
        } else {
            &self.cprocs.as_ref().unwrap()[self.pc - 1]
        }
    }

    #[inline]
    fn get_lang(&self) -> &Lang<F, C> {
        self.folding_config.lang()
    }
}

impl<F: LurkField> CEKState<Ptr<F>, Ptr<F>> for Vec<Ptr<F>> {
    fn expr(&self) -> &Ptr<F> {
        &self[0]
    }
    fn env(&self) -> &Ptr<F> {
        &self[1]
    }
    fn cont(&self) -> &Ptr<F> {
        &self[2]
    }
}

impl<F: LurkField> FrameLike<Ptr<F>, Ptr<F>> for Frame<F> {
    type FrameIO = Vec<Ptr<F>>;
    fn input(&self) -> &Self::FrameIO {
        &self.input
    }
    fn output(&self) -> &Self::FrameIO {
        &self.output
    }
}

impl<F: LurkField> EvaluationStore for Store<F> {
    type Ptr = Ptr<F>;
    type ContPtr = Ptr<F>;
    type Error = anyhow::Error;

    fn read(&self, expr: &str) -> Result<Self::Ptr, Self::Error> {
        self.read_with_default_state(expr)
    }

    fn initial_empty_env(&self) -> Self::Ptr {
        self.intern_nil()
    }

    fn get_cont_terminal(&self) -> Self::ContPtr {
        Ptr::null(Tag::Cont(ContTag::Terminal))
    }

    fn ptr_eq(&self, left: &Self::Ptr, right: &Self::Ptr) -> Result<bool, Self::Error> {
        Ok(self.hash_ptr(left)? == self.hash_ptr(right)?)
    }
}

impl<'a, F: LurkField, C: Coprocessor<F> + 'a> MultiFrameTrait<'a, F, C> for MultiFrame<'a, F, C> {
    type Ptr = Ptr<F>;
    type ContPtr = Ptr<F>;
    type Store = Store<F>;
    type StoreError = store::Error;
    type EvalFrame = Frame<F>;
    type CircuitFrame = Frame<F>;
    type GlobalAllocation = GlobalAllocator<F>;
    type AllocatedIO = Vec<AllocatedPtr<F>>;

    fn emitted(_store: &Store<F>, eval_frame: &Self::EvalFrame) -> Vec<Ptr<F>> {
        eval_frame.emitted.clone()
    }

    fn io_to_scalar_vector(
        store: &Self::Store,
        io: &<Self::EvalFrame as FrameLike<Ptr<F>, Ptr<F>>>::FrameIO,
    ) -> Result<Vec<F>, Self::StoreError> {
        store.to_vector(io).map_err(|e| store::Error(e.to_string()))
    }

    fn compute_witness(&self, s: &Store<F>) -> WitnessCS<F> {
        let mut wcs = WitnessCS::new();

        let z_scalar = s.to_vector(self.input.as_ref().unwrap()).unwrap();

        let mut bogus_cs = WitnessCS::<F>::new();
        let z: Vec<AllocatedNum<F>> = z_scalar
            .iter()
            .map(|x| AllocatedNum::alloc(&mut bogus_cs, || Ok(*x)).unwrap())
            .collect::<Vec<_>>();

        let _ = nova::traits::circuit::StepCircuit::synthesize(self, &mut wcs, z.as_slice());

        wcs
    }

    fn cached_witness(&mut self) -> &mut Option<WitnessCS<F>> {
        &mut self.cached_witness
    }

    fn output(&self) -> &Option<<Self::EvalFrame as FrameLike<Ptr<F>, Ptr<F>>>::FrameIO> {
        &self.output
    }

    fn frames(&self) -> Option<&Vec<Self::CircuitFrame>> {
        self.frames.as_ref()
    }

    fn precedes(&self, maybe_next: &Self) -> bool {
        self.output == maybe_next.input
    }

    fn synthesize_frames<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        store: &Self::Store,
        input: Self::AllocatedIO,
        frames: &[Self::CircuitFrame],
        g: &Self::GlobalAllocation,
    ) -> Result<Self::AllocatedIO, SynthesisError> {
        let (_, output) = frames
            .iter()
            .try_fold((0, input.to_vec()), |(i, input), frame| {
                if !frame.blank {
                    for (alloc_ptr, input) in input.iter().zip(&frame.input) {
                        let input_zptr = store.hash_ptr(input).expect("Hash did not succeed");
                        let (Some(alloc_ptr_tag), Some(alloc_ptr_hash)) = (alloc_ptr.tag().get_value(), alloc_ptr.hash().get_value()) else {
                            return Err(SynthesisError::AssignmentMissing)
                        };
                        assert_eq!(alloc_ptr_tag, input_zptr.tag().to_field());
                        assert_eq!(alloc_ptr_hash, *input_zptr.value());
                    }
                }
                let bound_allocations = &mut BoundAllocations::new();
                let func = self.get_func();
                func.add_input(&input, bound_allocations);
                let output = func
                    .synthesize_frame(
                        &mut cs.namespace(|| format!("frame {i}")),
                        store,
                        frame,
                        g,
                        bound_allocations,
                        self.get_lang(),
                    )
                    .expect("failed to synthesize frame");
                assert_eq!(input.len(), output.len());
                Ok((i + 1, output))
            })?;
        Ok(output)
    }

    fn blank(folding_config: Arc<FoldingConfig<F, C>>, _meta: Meta<F>, pc: usize) -> Self {
        let (lurk_step, cprocs, rc) = match &*folding_config {
            FoldingConfig::IVC(lang, rc) => {
                (Arc::new(make_eval_step_from_lang(lang, true)), None, *rc)
            }
            FoldingConfig::NIVC(lang, rc) => (
                Arc::new(make_eval_step_from_lang(lang, false)),
                Some(make_cprocs_funcs_from_lang(lang)),
                *rc,
            ),
        };
        let reduction_count = if pc == 0 { rc } else { 1 };
        Self {
            store: None,
            lurk_step,
            cprocs,
            input: None,
            output: None,
            frames: None,
            cached_witness: None,
            reduction_count,
            folding_config,
            pc,
            next_pc: 0,
        }
    }

    fn from_frames(
        reduction_count: usize,
        frames: &[Frame<F>],
        store: &'a Self::Store,
        folding_config: Arc<FoldingConfig<F, C>>,
    ) -> Vec<Self> {
        let total_frames = frames.len();
        let n = (total_frames + reduction_count - 1) / reduction_count;
        let mut multi_frames = Vec::with_capacity(n);
        match &*folding_config {
            FoldingConfig::IVC(lang, _) => {
                let lurk_step = Arc::new(make_eval_step_from_lang(lang, true));
                for chunk in frames.chunks(reduction_count) {
                    let output = chunk
                        .last()
                        .expect("chunk must not be empty")
                        .output
                        .to_vec();
                    let inner_frames = if chunk.len() < reduction_count {
                        let mut inner_frames = Vec::with_capacity(reduction_count);
                        inner_frames.extend(chunk.to_vec());
                        let padding_frame = lurk_step
                            .call_simple(&output, store, lang, 0)
                            .expect("reduction step failed");
                        assert_eq!(padding_frame.input, padding_frame.output);
                        inner_frames.resize(reduction_count, padding_frame.clone());
                        inner_frames
                    } else {
                        chunk.to_vec()
                    };

                    let mf = MultiFrame {
                        store: Some(store),
                        lurk_step: lurk_step.clone(),
                        cprocs: None,
                        input: Some(chunk[0].input.to_vec()),
                        output: Some(output),
                        frames: Some(inner_frames),
                        cached_witness: None,
                        reduction_count,
                        folding_config: folding_config.clone(),
                        pc: 0,
                        next_pc: 0,
                    };

                    multi_frames.push(mf);
                }
            }
            FoldingConfig::NIVC(lang, _) => {
                let lurk_step = Arc::new(make_eval_step_from_lang(lang, false));
                let cprocs = make_cprocs_funcs_from_lang(lang);
                let mut chunk_start_idx = 0;
                while chunk_start_idx < frames.len() {
                    let first_frame = &frames[chunk_start_idx];

                    // Variables occurring in both branches
                    let input = first_frame.input.clone();
                    let output: Vec<_>;
                    let frames_to_add: Vec<_>;
                    let mut reduction_count_to_use = reduction_count;
                    let mut pc = 0;
                    let mut next_pc = 0;

                    if first_frame.pc == 0 {
                        let mut inner_frames = Vec::with_capacity(reduction_count);
                        let chunk_start_idx_saved = chunk_start_idx;

                        // fill `inner_frames` with `reduction_count` frames unless
                        // we don't have enough frames or we find some frame whose
                        // `pc` is not `0` on the way
                        for i in 0..reduction_count {
                            let current_frame_idx = chunk_start_idx_saved + i;
                            inner_frames.push(frames[current_frame_idx].clone());
                            chunk_start_idx = current_frame_idx + 1;

                            if let Some(next_frame) = frames.get(chunk_start_idx) {
                                next_pc = next_frame.pc;
                                if next_pc != 0 {
                                    // incompatible `pc` incoming
                                    break;
                                }
                            } else {
                                // not enough frames
                                break;
                            }
                        }

                        output = inner_frames
                            .last()
                            .expect("empty inner_frames")
                            .output
                            .to_vec();

                        if inner_frames.len() < reduction_count {
                            let padding_frame = lurk_step
                                .call_simple(&output, store, lang, 0)
                                .expect("reduction step failed");
                            assert_eq!(padding_frame.input, padding_frame.output);
                            inner_frames.resize(reduction_count, padding_frame);
                        }

                        frames_to_add = inner_frames;
                    } else {
                        chunk_start_idx += 1;
                        output = first_frame.output.clone();
                        frames_to_add = vec![first_frame.clone()];
                        reduction_count_to_use = 1;
                        pc = first_frame.pc;
                    }

                    let mf = MultiFrame {
                        store: Some(store),
                        lurk_step: lurk_step.clone(),
                        cprocs: Some(cprocs.clone()),
                        input: Some(input),
                        output: Some(output),
                        frames: Some(frames_to_add),
                        cached_witness: None,
                        reduction_count: reduction_count_to_use,
                        folding_config: folding_config.clone(),
                        pc,
                        next_pc,
                    };

                    multi_frames.push(mf);
                }
            }
        }

        multi_frames
    }

    /// Make a dummy instance, duplicating `self`'s final `CircuitFrame`.
    fn make_dummy(
        reduction_count: usize,
        circuit_frame: Option<Self::CircuitFrame>,
        store: &'a Self::Store,
        folding_config: Arc<FoldingConfig<F, C>>,
        _meta: Meta<F>,
    ) -> Self {
        let (lurk_step, cprocs) = match &*folding_config {
            FoldingConfig::IVC(lang, _) => (Arc::new(make_eval_step_from_lang(lang, true)), None),
            FoldingConfig::NIVC(lang, _) => (
                Arc::new(make_eval_step_from_lang(lang, false)),
                Some(make_cprocs_funcs_from_lang(lang)),
            ),
        };
        let (frames, input, output) = if let Some(circuit_frame) = circuit_frame {
            (
                Some(vec![circuit_frame.clone(); reduction_count]),
                Some(circuit_frame.input),
                Some(circuit_frame.output),
            )
        } else {
            (None, None, None)
        };
        Self {
            store: Some(store),
            lurk_step,
            cprocs,
            input,
            output,
            frames,
            cached_witness: None,
            reduction_count,
            folding_config,
            pc: 0,
            next_pc: 0,
        }
    }

    fn get_evaluation_frames(
        _padding_predicate: impl Fn(usize) -> bool,
        expr: Self::Ptr,
        env: Self::Ptr,
        store: &Self::Store,
        limit: usize,
        lang: &Lang<F, C>,
    ) -> std::result::Result<Vec<Self::EvalFrame>, ProofError> {
        // TODO: integrate https://github.com/lurk-lab/lurk-rs/commit/963a6361701efcaa78735d8fc9c927f518d8e31c
        let input = vec![expr, env, Ptr::null(Tag::Cont(ContTag::Outermost))];
        let state = initial_lurk_state();
        let log_fmt = |i: usize, inp: &[Ptr<F>], emit: &[Ptr<F>], store: &Store<F>| {
            let mut out = format!(
                "Frame: {i}\n\tExpr: {}\n\tEnv:  {}\n\tCont: {}",
                inp[0].fmt_to_string(store, state),
                inp[1].fmt_to_string(store, state),
                inp[2].fmt_to_string(store, state)
            );
            if let Some(ptr) = emit.first() {
                out.push_str(&format!("\n\tEmtd: {}", ptr.fmt_to_string(store, state)));
            }
            out
        };
        let lurk_step = make_eval_step_from_lang(lang, true);
        match build_frames(&lurk_step, &[], input, store, limit, lang, log_fmt) {
            Ok((frames, ..)) => Ok(frames),
            Err(e) => Err(ProofError::Reduction(ReductionError::Misc(e.to_string()))),
        }
    }

    fn significant_frame_count(frames: &[Self::EvalFrame]) -> usize {
        let stop_cond = |output: &[Ptr<F>]| {
            output[2] == Ptr::null(Tag::Cont(ContTag::Terminal))
                || output[2] == Ptr::null(Tag::Cont(ContTag::Error))
        };
        frames
            .iter()
            .rev()
            .skip_while(|f| f.input == f.output && stop_cond(&f.output))
            .count()
    }
}

impl<'a, F: LurkField, C: Coprocessor<F>> Circuit<F> for MultiFrame<'a, F, C> {
    fn synthesize<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let mut synth =
            |store: &Store<F>, frames: &[Frame<F>], input: &[Ptr<F>], output: &[Ptr<F>]| {
                let mut allocated_input = Vec::with_capacity(input.len());
                for (i, ptr) in input.iter().enumerate() {
                    let z_ptr = store.hash_ptr(ptr).expect("pointer hashing failed");

                    let allocated_tag = AllocatedNum::alloc_infallible(
                        &mut cs.namespace(|| format!("allocated tag for input {i}")),
                        || z_ptr.tag().to_field(),
                    );
                    allocated_tag
                        .inputize(&mut cs.namespace(|| format!("inputized tag for input {i}")))?;

                    let allocated_hash = AllocatedNum::alloc_infallible(
                        &mut cs.namespace(|| format!("allocated hash for input {i}")),
                        || *z_ptr.value(),
                    );
                    allocated_hash
                        .inputize(&mut cs.namespace(|| format!("inputized hash for input {i}")))?;

                    allocated_input.push(AllocatedPtr::from_parts(allocated_tag, allocated_hash));
                }

                let mut allocated_output = Vec::with_capacity(output.len());
                for (i, ptr) in output.iter().enumerate() {
                    let z_ptr = store.hash_ptr(ptr).expect("pointer hashing failed");

                    let allocated_tag = AllocatedNum::alloc_infallible(
                        &mut cs.namespace(|| format!("allocated tag for output {i}")),
                        || z_ptr.tag().to_field(),
                    );
                    allocated_tag
                        .inputize(&mut cs.namespace(|| format!("inputized tag for output {i}")))?;

                    let allocated_hash = AllocatedNum::alloc_infallible(
                        &mut cs.namespace(|| format!("allocated hash for output {i}")),
                        || *z_ptr.value(),
                    );
                    allocated_hash
                        .inputize(&mut cs.namespace(|| format!("inputized hash for output {i}")))?;

                    allocated_output.push(AllocatedPtr::from_parts(allocated_tag, allocated_hash));
                }

                let g = self.lurk_step.alloc_globals(cs, store)?;

                let allocated_output_result =
                    self.synthesize_frames(cs, store, allocated_input, frames, &g)?;

                assert_eq!(allocated_output.len(), allocated_output_result.len());

                for (i, (o_res, o)) in allocated_output_result
                    .iter()
                    .zip(allocated_output)
                    .enumerate()
                {
                    o_res.enforce_equal(
                        &mut cs.namespace(|| format!("outer output {i} is correct")),
                        &o,
                    );
                }

                Ok(())
            };

        match self.store {
            Some(store) => {
                let input = self
                    .input
                    .as_ref()
                    .ok_or_else(|| SynthesisError::AssignmentMissing)?;
                let output = self
                    .output
                    .as_ref()
                    .ok_or_else(|| SynthesisError::AssignmentMissing)?;
                let frames = self.frames.as_ref().unwrap();
                synth(store, frames, input, output)
            }
            None => {
                assert!(self.frames.is_none());
                let dummy_io = [Ptr::dummy(); 3];
                let store = Store::default();
                let blank_frame = Frame::blank(self.get_func(), self.pc);
                let frames = vec![blank_frame; self.reduction_count];
                synth(&store, &frames, &dummy_io, &dummy_io)
            }
        }
    }
}

impl<'a, F: LurkField, C: Coprocessor<F>> Provable<F> for MultiFrame<'a, F, C> {
    fn public_inputs(&self) -> Vec<F> {
        let input = self.input.as_ref().expect("input missing");
        let output = self.output.as_ref().expect("input missing");
        let store = self.store.expect("store missing");
        let mut res = Vec::with_capacity(self.public_input_size());
        for ptr in input {
            let z_ptr = store.hash_ptr(ptr).expect("pointer hashing failed");
            res.push(z_ptr.tag().to_field());
            res.push(*z_ptr.value());
        }
        for ptr in output {
            let z_ptr = store.hash_ptr(ptr).expect("pointer hashing failed");
            res.push(z_ptr.tag().to_field());
            res.push(*z_ptr.value());
        }
        res
    }

    #[inline]
    fn public_input_size(&self) -> usize {
        // tag and hash for input and output (output has the same size as the input)
        4 * self.lurk_step.input_params.len()
    }

    #[inline]
    fn reduction_count(&self) -> usize {
        self.reduction_count
    }
}

impl<'a, F: LurkField, C: Coprocessor<F>> nova::traits::circuit::StepCircuit<F>
    for MultiFrame<'a, F, C>
{
    fn arity(&self) -> usize {
        2 * self.lurk_step.input_params.len()
    }

    fn synthesize<CS>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        assert_eq!(self.arity(), z.len());

        let n_ptrs = self.arity() / 2;
        let mut input = Vec::with_capacity(n_ptrs);
        for i in 0..n_ptrs {
            input.push(AllocatedPtr::from_parts(
                z[2 * i].clone(),
                z[2 * i + 1].clone(),
            ));
        }

        let output_ptrs = match self.frames.as_ref() {
            Some(frames) => {
                if self.pc != 0 {
                    assert_eq!(frames.len(), 1);
                }
                let store = self.store.expect("store missing");
                let g = self.lurk_step.alloc_globals(cs, store)?;
                self.synthesize_frames(cs, store, input, frames, &g)?
            }
            None => {
                assert!(self.store.is_none());
                let store = Store::default();
                let blank_frame = Frame::blank(self.get_func(), self.pc);
                let frames = vec![blank_frame; self.reduction_count];
                let g = self.lurk_step.alloc_globals(cs, &store)?;
                self.synthesize_frames(cs, &store, input, &frames, &g)?
            }
        };

        let mut output = Vec::with_capacity(self.arity());
        for ptr in output_ptrs {
            output.push(ptr.tag().clone());
            output.push(ptr.hash().clone());
        }

        Ok(output)
    }
}

impl<'a, F: LurkField, C: Coprocessor<F>> nova::traits::circuit_supernova::StepCircuit<F>
    for MultiFrame<'a, F, C>
{
    fn arity(&self) -> usize {
        2 * self.lurk_step.input_params.len()
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _pc: Option<&AllocatedNum<F>>,
        z: &[AllocatedNum<F>],
    ) -> Result<(Option<AllocatedNum<F>>, Vec<AllocatedNum<F>>), SynthesisError> {
        let next_pc = AllocatedNum::alloc_infallible(&mut cs.namespace(|| "next_pc"), || {
            F::from_u64(self.next_pc as u64)
        });
        let output = <MultiFrame<'_, F, C> as nova::traits::circuit::StepCircuit<F>>::synthesize(
            self, cs, z,
        )?;
        Ok((Some(next_pc), output))
    }

    fn circuit_index(&self) -> usize {
        self.pc
    }
}

impl<'a, F, C> NonUniformCircuit<G1<F>, G2<F>, MultiFrame<'a, F, C>, C2<F>> for MultiFrame<'a, F, C>
where
    F: CurveCycleEquipped + LurkField,
    C: Coprocessor<F> + 'a,
    <<G1<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
    <<G2<F> as Group>::Scalar as PrimeField>::Repr: Abomonation,
{
    fn num_circuits(&self) -> usize {
        assert_eq!(self.pc, 0);
        self.get_lang().coprocessor_count() + 1
    }

    fn primary_circuit(&self, circuit_index: usize) -> MultiFrame<'a, F, C> {
        if circuit_index == 0 {
            self.clone()
        } else {
            Self::blank(
                self.folding_config.clone(),
                Default::default(),
                circuit_index,
            )
        }
    }

    fn secondary_circuit(&self) -> C2<F> {
        Default::default()
    }
}
