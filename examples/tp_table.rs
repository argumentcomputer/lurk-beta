use anyhow::{anyhow, Result};
use ascii_table::{Align, AsciiTable};
use criterion::black_box;
use lurk::{
    eval::lang::{Coproc, Lang},
    lem::{eval::evaluate, multiframe::MultiFrame, store::Store},
    proof::{
        nova::{public_params, NovaProver, PublicParams},
        Prover,
    },
};
use num_traits::ToPrimitive;
use pasta_curves::pallas::Scalar as Fr;
use statrs::statistics::Statistics;
use std::{cell::OnceCell, sync::Arc, time::Instant};

const PROGRAM: &str = "(letrec ((loop (lambda (k) (begin
  ;; fibonacci from lurk-lib
  (letrec ((next (lambda (a b n target)
               (if (eq n target)
                   a
                   (next b
                         (+ a b)
                         (+ 1 n)
                         target))))
            (fib (next 0 1 0)))
    (fib k))
  ;; to use commitment slots
  (commit k)
  ;; < uses three bit decomp slots
  (< 0 k)
  ;; u64 operator uses one bit decomp slot
  (u64 5)
  ;; product between u64s uses one bit decomp slot
  (* 2u64 3u64)
  ;; char operator uses one bit decomp slot
  (char 97)
  ;; loop infinitely
  (loop (+ k 1))))))
(loop 0))";

#[inline]
fn n_iters(n_folds: usize, rc: usize) -> usize {
    (n_folds + 1) * rc
}

fn filter(elts: &[f64]) -> Vec<f64> {
    let mean = elts.mean();
    let sd = elts.std_dev();
    let lower = &(mean - sd);
    let upper = &(mean + sd);
    let mut out = Vec::with_capacity(elts.len());
    for e in elts.iter() {
        if lower <= e && e <= upper {
            out.push(*e)
        }
    }
    out
}

fn analyze_raw(data: &[Vec<(usize, Vec<f64>)>], rc_vec: &[usize]) -> Vec<Vec<String>> {
    let mut printed = Vec::with_capacity(data.len());
    for (line_data, rc) in data.iter().zip(rc_vec) {
        let mut line = Vec::with_capacity(line_data.len() + 1);
        line.push(rc.to_string());
        for (n_frames, durations) in line_data {
            let tps = durations
                .iter()
                .map(|d| n_frames.to_f64().unwrap() / d)
                .collect::<Vec<_>>();
            line.push(format!("{:.2}±{:.2}", (&tps).mean(), tps.std_dev()));
        }
        printed.push(line);
    }
    printed
}

fn analyze_adj(data: &[Vec<(usize, Vec<f64>)>], rc_vec: &[usize]) -> Vec<Vec<String>> {
    let mut printed = Vec::with_capacity(data.len());
    for (line_data, rc) in data.iter().zip(rc_vec) {
        let mut line = Vec::with_capacity(line_data.len() + 1);
        line.push(rc.to_string());
        let n_frames_duration_0 = OnceCell::new();
        for (n_frames, durations) in &line_data[1..] {
            let (n_frames_0, duration_0) = n_frames_duration_0.get_or_init(|| {
                let (n_frames_0, durations_0) = &line_data[0];
                let duration_0 = durations_0.mean();
                (*n_frames_0, duration_0)
            });
            let tps = durations
                .iter()
                .map(|d| (n_frames - n_frames_0).to_f64().unwrap() / (d - duration_0))
                .collect::<Vec<_>>();
            line.push(format!("{:.2}±{:.2}", (&tps).mean(), tps.std_dev()));
        }
        printed.push(line);
    }
    printed
}

fn rc_env() -> Result<Vec<usize>> {
    std::env::var("LURK_RC")
        .map_err(|e| anyhow!("LURK_RC env var isn't set: {e}"))
        .and_then(|rc| {
            let vec: Result<Vec<usize>> = rc
                .split(',')
                .map(|rc| {
                    rc.parse::<usize>()
                        .map_err(|e| anyhow!("Failed to parse RC: {e}"))
                })
                .collect();
            vec
        })
}

fn n_folds_env() -> Result<usize> {
    std::env::var("LURK_N_FOLDS")
        .map_err(|e| anyhow!("LURK_N_FOLDS env var isn't set: {e}"))
        .and_then(|n_folds| {
            n_folds
                .parse::<usize>()
                .map_err(|e| anyhow!("Failed to parse N_FOLDS: {e}"))
        })
}

/// This example prints adjusted and raw throughput tables whose dimensions are
/// the reduction count (vertical) and the number of folding steps (horizontal).
///
/// Example:
/// ```text
/// $ LURK_RC=8,16 LURK_N_FOLDS=2 cargo run --release --example tp_table
/// ...
/// Raw throughput
/// ┌────────────┬─────────────┬────────────┬────────────┐
/// │ rc\n_folds │ 0           │ 1          │ 2          │
/// ├────────────┼─────────────┼────────────┼────────────┤
/// │          8 │  85.61±3.15 │ 64.45±0.92 │ 56.22±0.68 │
/// │         16 │ 111.48±2.30 │ 77.47±0.70 │ 67.54±0.61 │
/// └────────────┴─────────────┴────────────┴────────────┘
/// Adjusted throughput
/// ┌────────────┬────────────┬────────────┐
/// │ rc\n_folds │ 1          │ 2          │
/// ├────────────┼────────────┼────────────┤
/// │          8 │ 51.72±1.19 │ 48.00±0.75 │
/// │         16 │ 59.38±0.83 │ 56.42±0.63 │
/// └────────────┴────────────┴────────────┘
/// ```
/// The first table
fn main() {
    let rc_vec = rc_env().unwrap_or_else(|_| vec![100]);
    let max_n_folds = n_folds_env().unwrap_or(3);
    let n_samples = 10;

    let max_rc = rc_vec.iter().max().unwrap();

    let limit = n_iters(max_n_folds, *max_rc);

    let store = Store::<Fr>::default();
    let program = store.read_with_default_state(PROGRAM).unwrap();

    let frames = evaluate::<Fr, Coproc<Fr>>(None, program, &store, limit).unwrap();

    let lang = Lang::<Fr, Coproc<Fr>>::new();
    let lang_arc = Arc::new(lang.clone());

    let mut data = Vec::with_capacity(rc_vec.len());

    for rc in rc_vec.clone() {
        let prover: NovaProver<'_, _, _> = NovaProver::new(rc, lang_arc.clone());
        println!("Getting public params for rc={rc}");
        // TODO: use cache once it's fixed
        let pp: PublicParams<_, MultiFrame<'_, _, Coproc<Fr>>> =
            public_params(rc, lang_arc.clone());
        let n_folds_data = (0..=max_n_folds)
            .map(|n_folds| {
                let n_frames = n_iters(n_folds, rc);
                let frames = &frames[..n_frames];
                println!(" Proving for rc={rc} and n_folds={n_folds} ({n_frames} frames)");
                let mut timings = Vec::with_capacity(n_samples);
                for _ in 0..n_samples {
                    let start = Instant::now();
                    let result = prover.prove(&pp, frames, &store);
                    let _ = black_box(result);
                    let end = start.elapsed().as_secs_f64();
                    timings.push(end);
                }
                (n_frames, timings)
            })
            .collect::<Vec<_>>();
        data.push(
            n_folds_data
                .into_iter()
                .map(|(x, y)| (x, filter(&y)))
                .collect(),
        );
    }

    let mut table = AsciiTable::default();
    table
        .column(0)
        .set_header("rc\\n_folds")
        .set_align(Align::Right);
    (0..=max_n_folds).for_each(|i| {
        table
            .column(i + 1)
            .set_header(i.to_string())
            .set_align(Align::Right);
    });

    println!("Raw throughput");
    table.print(analyze_raw(&data, &rc_vec));

    if max_n_folds > 0 {
        let mut table = AsciiTable::default();
        table
            .column(0)
            .set_header("rc\\n_folds")
            .set_align(Align::Right);
        (1..=max_n_folds).for_each(|i| {
            table
                .column(i)
                .set_header(i.to_string())
                .set_align(Align::Right);
        });

        println!("Adjusted throughput");
        table.print(analyze_adj(&data, &rc_vec));
    }
}
