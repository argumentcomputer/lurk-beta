use std::path::Path;
use std::sync::Arc;

use std::{fs::read_to_string, process};

use anyhow::{bail, Context, Result};

use log::info;

use rustyline::{
    error::ReadlineError,
    history::DefaultHistory,
    validate::{MatchingBracketValidator, ValidationContext, ValidationResult, Validator},
    Config, Editor,
};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};

use lurk::{
    eval::{
        lang::{Coproc, Lang},
        Evaluator, Frame, Witness, IO,
    },
    field::{LanguageField, LurkField},
    parser,
    ptr::Ptr,
    store::Store,
    tag::{ContTag, ExprTag},
    writer::Write,
    Num, UInt,
};

#[cfg(not(target_arch = "wasm32"))]
use lurk::{
    proof::{nova::NovaProver, Prover},
    public_parameters::public_params,
    z_store::ZStore,
};

#[cfg(not(target_arch = "wasm32"))]
use super::lurk_proof::{LurkProof, LurkProofMeta};

#[derive(Completer, Helper, Highlighter, Hinter)]
struct InputValidator {
    brackets: MatchingBracketValidator,
}

impl Validator for InputValidator {
    fn validate(&self, ctx: &mut ValidationContext<'_>) -> rustyline::Result<ValidationResult> {
        self.brackets.validate(ctx)
    }
}

pub enum Backend {
    Nova,
    SnarkPackPlus,
}

impl std::fmt::Display for Backend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nova => write!(f, "Nova"),
            Self::SnarkPackPlus => write!(f, "SnarkPack+"),
        }
    }
}

impl Backend {
    pub fn default_field(&self) -> LanguageField {
        match self {
            Self::Nova => LanguageField::Pallas,
            Self::SnarkPackPlus => LanguageField::BLS12_381,
        }
    }

    fn compatible_fields(&self) -> Vec<LanguageField> {
        use LanguageField::*;
        match self {
            Self::Nova => vec![Pallas, Vesta],
            Self::SnarkPackPlus => vec![BLS12_381],
        }
    }

    pub fn validate_field(&self, field: &LanguageField) -> Result<()> {
        let compatible_fields = self.compatible_fields();
        if !compatible_fields.contains(field) {
            bail!(
                "Backend {self} is incompatible with field {field}. Compatible fields are:\n  {}",
                compatible_fields
                    .iter()
                    .map(|f| f.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        Ok(())
    }
}

#[allow(dead_code)]
#[derive(Debug)]
struct Evaluation<F: LurkField> {
    frames: Vec<Frame<IO<F>, Witness<F>, Coproc<F>>>,
    last_frame_idx: usize,
    iterations: usize,
}

#[allow(dead_code)]
pub struct Repl<F: LurkField> {
    store: Store<F>,
    env: Ptr<F>,
    limit: usize,
    lang: Arc<Lang<F, Coproc<F>>>,
    rc: usize,
    backend: Backend,
    evaluation: Option<Evaluation<F>>,
}

pub fn validate_non_zero(name: &str, x: usize) -> Result<()> {
    if x == 0 {
        bail!("`{name}` can't be zero")
    }
    Ok(())
}

/// `pad(a, m)` returns the first multiple of `m` that's equal or greater than `a`
///
/// Panics if `m` is zero
#[inline]
#[allow(dead_code)]
fn pad(a: usize, m: usize) -> usize {
    (a + m - 1) / m * m
}

type F = pasta_curves::pallas::Scalar; // TODO: generalize this

impl Repl<F> {
    pub fn new(store: Store<F>, env: Ptr<F>, limit: usize, rc: usize, backend: Backend) -> Repl<F> {
        info!(
            "Launching REPL with backend {backend} and field {}",
            F::FIELD
        );
        Repl {
            store,
            env,
            limit,
            lang: Arc::new(Lang::new()),
            rc,
            backend,
            evaluation: None,
        }
    }

    #[allow(dead_code)]
    fn proof_claim(
        store: &mut Store<F>,
        exprs: (Ptr<F>, Ptr<F>),
        envs: (Ptr<F>, Ptr<F>),
        conts: ((F, F), (F, F)),
    ) -> Ptr<F> {
        let expr_key = store.key("expr");
        let env_key = store.key("env");
        let cont_key = store.key("cont");
        let expr_out_key = store.key("expr-out");
        let env_out_key = store.key("env-out");
        let cont_out_key = store.key("cont-out");
        let cont_tag = store.num(Num::Scalar(conts.0 .0));
        let cont_val = store.num(Num::Scalar(conts.0 .1));
        let cont = store.cons(cont_tag, cont_val);
        let cont_out_tag = store.num(Num::Scalar(conts.1 .0));
        let cont_out_val = store.num(Num::Scalar(conts.1 .1));
        let cont_out = store.cons(cont_out_tag, cont_out_val);
        store.list(&[
            expr_key,
            exprs.0,
            env_key,
            envs.0,
            cont_key,
            cont,
            expr_out_key,
            exprs.1,
            env_out_key,
            envs.1,
            cont_out_key,
            cont_out,
        ])
    }

    #[cfg(not(target_arch = "wasm32"))]
    pub fn prove_last_frames(&mut self) -> Result<()> {
        use ff::Field;

        use crate::cli::{commitment::Commitment, paths::non_wasm::proof_path};

        match self.evaluation.as_mut() {
            None => bail!("No evaluation to prove"),
            Some(Evaluation {
                frames,
                last_frame_idx,
                iterations,
            }) => match self.backend {
                Backend::Nova => {
                    info!("Hydrating the store");
                    self.store.hydrate_scalar_cache();

                    // saving to avoid clones
                    let input = &frames[0].input;
                    let output = &frames[*last_frame_idx].output;
                    let mut zstore = Some(ZStore::<F>::default());
                    let expr = self.store.get_z_expr(&input.expr, &mut zstore)?.0;
                    let env = self.store.get_z_expr(&input.env, &mut zstore)?.0;
                    let cont = self.store.get_z_cont(&input.cont, &mut zstore)?.0;
                    let expr_out = self.store.get_z_expr(&output.expr, &mut zstore)?.0;
                    let env_out = self.store.get_z_expr(&output.env, &mut zstore)?.0;
                    let cont_out = self.store.get_z_cont(&output.cont, &mut zstore)?.0;

                    let proof_claim = Self::proof_claim(
                        &mut self.store,
                        (input.expr, output.expr),
                        (input.env, output.env),
                        (cont.parts(), cont_out.parts()),
                    );
                    let commitment = Commitment::new(F::ZERO, proof_claim, &mut self.store)?;
                    let proof_id = &commitment.hidden.value().hex_digits();

                    let proof_path = proof_path(proof_id);

                    if proof_path.exists() {
                        info!("Proof already cached");
                        // TODO: make sure that the proof file is not corrupted
                    } else {
                        info!("Proof not cached");
                        // padding the frames, if needed
                        let mut n_frames = frames.len();
                        let n_pad = pad(n_frames, self.rc) - n_frames;
                        if n_pad != 0 {
                            frames.extend(vec![frames[n_frames - 1].clone(); n_pad]);
                            n_frames = frames.len();
                        }

                        info!("Loading public parameters");
                        let pp = public_params(self.rc, self.lang.clone())?;

                        let prover = NovaProver::new(self.rc, (*self.lang).clone());

                        info!("Proving and compressing");
                        let (proof, public_inputs, public_outputs, num_steps) =
                            prover.prove(&pp, frames, &mut self.store, self.lang.clone())?;
                        let proof = proof.compress(&pp)?;
                        assert_eq!(self.rc * num_steps, n_frames);
                        assert!(proof.verify(&pp, num_steps, &public_inputs, &public_outputs)?);

                        let lurk_proof = LurkProof::Nova {
                            proof,
                            public_inputs,
                            public_outputs,
                            num_steps,
                            rc: self.rc,
                            lang: (*self.lang).clone(),
                        };

                        let lurk_proof_meta = LurkProofMeta {
                            iterations: *iterations,
                            expr,
                            env,
                            cont,
                            expr_out,
                            env_out,
                            cont_out,
                            zstore: zstore.unwrap(),
                        };

                        lurk_proof.persist(proof_id)?;
                        lurk_proof_meta.persist(proof_id)?;
                        commitment.persist(proof_id)?;
                    }
                    println!("Proof ID: \"{proof_id}\"");
                    Ok(())
                }
                Backend::SnarkPackPlus => todo!(),
            },
        }
    }

    #[cfg(not(target_arch = "wasm32"))]
    fn hide(&mut self, secret: F, payload: Ptr<F>) -> Result<()> {
        use super::commitment::Commitment;

        let commitment = Commitment::new(secret, payload, &mut self.store)?;
        let hash = &commitment.hidden.value().hex_digits();
        commitment.persist(hash)?;
        println!(
            "Data: {}\nHash: 0x{hash}",
            payload.fmt_to_string(&self.store)
        );
        Ok(())
    }

    #[cfg(not(target_arch = "wasm32"))]
    fn fetch(&mut self, hash: &str, print_data: bool) -> Result<()> {
        use super::{
            commitment::Commitment, field_data::non_wasm::load, paths::non_wasm::commitment_path,
        };

        let commitment: Commitment<F> = load(commitment_path(hash))?;
        if commitment.hidden.value().hex_digits() != hash {
            bail!("Hash mismatch. Corrupted commitment file.")
        } else {
            let comm = self
                .store
                .intern_z_expr_ptr(&commitment.hidden, &commitment.zstore)
                .unwrap();
            if print_data {
                let data = self.store.fetch_comm(&comm).unwrap().1;
                println!("{}", data.fmt_to_string(&self.store));
            } else {
                println!("Data is now available");
            }
        }
        Ok(())
    }

    #[inline]
    fn eval_expr(&mut self, expr_ptr: Ptr<F>) -> Result<(IO<F>, usize, Vec<Ptr<F>>)> {
        Ok(Evaluator::new(expr_ptr, self.env, &mut self.store, self.limit, &self.lang).eval()?)
    }

    fn peek1(&self, cmd: &str, args: &Ptr<F>) -> Result<Ptr<F>> {
        let (first, rest) = self.store.car_cdr(args)?;
        if !rest.is_nil() {
            bail!("`{cmd}` accepts at most one argument")
        }
        Ok(first)
    }

    fn peek2(&self, cmd: &str, args: &Ptr<F>) -> Result<(Ptr<F>, Ptr<F>)> {
        let (first, rest) = self.store.car_cdr(args)?;
        let (second, rest) = self.store.car_cdr(&rest)?;
        if !rest.is_nil() {
            bail!("`{cmd}` accepts at most two arguments")
        }
        Ok((first, second))
    }

    fn peek_usize(&self, cmd: &str, args: &Ptr<F>) -> Result<usize> {
        let first = self.peek1(cmd, args)?;
        match first.tag {
            ExprTag::Num => match self.store.fetch_num(&first).unwrap() {
                Num::U64(u) => Ok(*u as usize),
                _ => bail!(
                    "Invalid value for `{cmd}`: {}",
                    first.fmt_to_string(&self.store)
                ),
            },
            ExprTag::U64 => match self.store.fetch_uint(&first).unwrap() {
                UInt::U64(u) => Ok(u as usize),
            },
            _ => bail!(
                "Invalid value for `{cmd}`: {}",
                first.fmt_to_string(&self.store)
            ),
        }
    }

    #[allow(dead_code)]
    fn get_comm_hash(&mut self, cmd: &str, args: &Ptr<F>) -> Result<String> {
        let first = self.peek1(cmd, args)?;
        let n = self.store.lurk_sym("num");
        let expr = self.store.list(&[n, first]);
        let (expr_io, ..) = self
            .eval_expr(expr)
            .with_context(|| "evaluating first arg")?;
        let hash = self
            .store
            .fetch_num(&expr_io.expr)
            .expect("must be a number");
        Ok(hash.into_scalar().hex_digits())
    }

    fn handle_meta_cases(&mut self, cmd: &str, args: &Ptr<F>, pwd_path: &Path) -> Result<()> {
        match cmd {
            "def" => {
                // Extends env with a non-recursive binding.
                //
                // This: !(:def foo (lambda () 123))
                //
                // Gets macroexpanded to this: (let ((foo (lambda () 123)))
                //                               (current-env))
                //
                // And the state's env is set to the result.
                let (first, second) = self.peek2(cmd, args)?;
                let l = &self.store.lurk_sym("let");
                let current_env = &self.store.lurk_sym("current-env");
                let binding = &self.store.list(&[first, second]);
                let bindings = &self.store.list(&[*binding]);
                let current_env_call = &self.store.list(&[*current_env]);
                let expanded = &self.store.list(&[*l, *bindings, *current_env_call]);
                let (expanded_io, ..) = self.eval_expr(*expanded)?;

                self.env = expanded_io.expr;

                let (new_binding, _) = &self.store.car_cdr(&expanded_io.expr)?;
                let (new_name, _) = self.store.car_cdr(new_binding)?;
                println!("{}", new_name.fmt_to_string(&self.store));
            }
            "defrec" => {
                // Extends env with a recursive binding.
                //
                // This: !(:defrec foo (lambda () 123))
                //
                // Gets macroexpanded to this: (letrec ((foo (lambda () 123)))
                //                               (current-env))
                //
                // And the state's env is set to the result.
                let (first, second) = self.peek2(cmd, args)?;
                let l = &self.store.lurk_sym("letrec");
                let current_env = &self.store.lurk_sym("current-env");
                let binding = &self.store.list(&[first, second]);
                let bindings = &self.store.list(&[*binding]);
                let current_env_call = &self.store.list(&[*current_env]);
                let expanded = &self.store.list(&[*l, *bindings, *current_env_call]);
                let (expanded_io, ..) = self.eval_expr(*expanded)?;

                self.env = expanded_io.expr;

                let (new_binding_outer, _) = &self.store.car_cdr(&expanded_io.expr)?;
                let (new_binding_inner, _) = &self.store.car_cdr(new_binding_outer)?;
                let (new_name, _) = self.store.car_cdr(new_binding_inner)?;
                println!("{}", new_name.fmt_to_string(&self.store));
            }
            "load" => {
                let first = self.peek1(cmd, args)?;
                match self.store.fetch_string(&first) {
                    Some(path) => {
                        let joined = pwd_path.join(Path::new(&path));
                        self.load_file(&joined)?
                    }
                    _ => bail!("Argument of `load` must be a string."),
                }
                std::io::Write::flush(&mut std::io::stdout()).unwrap();
            }
            "assert" => {
                let first = self.peek1(cmd, args)?;
                let (first_io, ..) = self.eval_expr(first)?;
                if first_io.expr.is_nil() {
                    eprintln!(
                        "`assert` failed. {} evaluates to nil",
                        first.fmt_to_string(&self.store)
                    );
                    process::exit(1);
                }
            }
            "assert-eq" => {
                let (first, second) = self.peek2(cmd, args)?;
                let (first_io, ..) = self
                    .eval_expr(first)
                    .with_context(|| "evaluating first arg")?;
                let (second_io, ..) = self
                    .eval_expr(second)
                    .with_context(|| "evaluating second arg")?;
                if !&self.store.ptr_eq(&first_io.expr, &second_io.expr)? {
                    eprintln!(
                        "`assert-eq` failed. Expected:\n  {} = {}\nGot:\n  {} ≠ {}",
                        first.fmt_to_string(&self.store),
                        second.fmt_to_string(&self.store),
                        first_io.expr.fmt_to_string(&self.store),
                        second_io.expr.fmt_to_string(&self.store)
                    );
                    process::exit(1);
                }
            }
            "assert-emitted" => {
                let (first, second) = self.peek2(cmd, args)?;
                let (first_io, ..) = self
                    .eval_expr(first)
                    .with_context(|| "evaluating first arg")?;
                let (.., emitted) = self
                    .eval_expr(second)
                    .with_context(|| "evaluating second arg")?;
                let (mut first_emitted, mut rest_emitted) = self.store.car_cdr(&first_io.expr)?;
                for (i, elem) in emitted.iter().enumerate() {
                    if elem != &first_emitted {
                        eprintln!(
                            "`assert-emitted` failed at position {i}. Expected {}, but found {}.",
                            first_emitted.fmt_to_string(&self.store),
                            elem.fmt_to_string(&self.store),
                        );
                        process::exit(1);
                    }
                    (first_emitted, rest_emitted) = self.store.car_cdr(&rest_emitted)?;
                }
            }
            "assert-error" => {
                let first = self.peek1(cmd, args)?;
                let (first_io, ..) = self.eval_expr(first)?;
                if first_io.cont.tag != ContTag::Error {
                    eprintln!(
                        "`assert-error` failed. {} doesn't result on evaluation error.",
                        first.fmt_to_string(&self.store)
                    );
                    process::exit(1);
                }
            }
            "lurk.commit" => {
                #[cfg(not(target_arch = "wasm32"))]
                {
                    let first = self.peek1(cmd, args)?;
                    let (first_io, ..) = self.eval_expr(first)?;
                    self.hide(ff::Field::ZERO, first_io.expr)?;
                }
            }
            "lurk.hide" => {
                #[cfg(not(target_arch = "wasm32"))]
                {
                    let (first, second) = self.peek2(cmd, args)?;
                    let (first_io, ..) = self
                        .eval_expr(first)
                        .with_context(|| "evaluating first arg")?;
                    let (second_io, ..) = self
                        .eval_expr(second)
                        .with_context(|| "evaluating second arg")?;
                    let Some(secret) = self.store.fetch_num(&first_io.expr) else {
                    bail!("Secret must be a number. Got {}", first_io.expr.fmt_to_string(&self.store))
                };
                    self.hide(secret.into_scalar(), second_io.expr)?;
                }
            }
            "fetch" => {
                #[cfg(not(target_arch = "wasm32"))]
                {
                    let hash = self.get_comm_hash(cmd, args)?;
                    self.fetch(&hash, false)?;
                }
            }
            "lurk.open" => {
                #[cfg(not(target_arch = "wasm32"))]
                {
                    let hash = self.get_comm_hash(cmd, args)?;
                    self.fetch(&hash, true)?;
                }
            }
            "clear" => self.env = self.store.nil(),
            "set-env" => {
                // The state's env is set to the result of evaluating the first argument.
                let first = self.peek1(cmd, args)?;
                let (first_io, ..) = self.eval_expr(first)?;
                self.env = first_io.expr;
            }
            "set-limit" => {
                let limit = self.peek_usize(cmd, args)?;
                validate_non_zero("limit", limit)?;
                self.limit = limit;
            }
            "set-rc" => {
                let rc = self.peek_usize(cmd, args)?;
                validate_non_zero("rc", rc)?;
                self.rc = rc;
            }
            "prove" => {
                if !args.is_nil() {
                    self.eval_expr_and_memoize(self.peek1(cmd, args)?)?;
                }
                #[cfg(not(target_arch = "wasm32"))]
                self.prove_last_frames()?;
            }
            "verify" => {
                #[cfg(not(target_arch = "wasm32"))]
                {
                    let first = self.peek1(cmd, args)?;
                    match self.store.fetch_string(&first) {
                        None => bail!(
                            "Proof ID {} not parsed as a string",
                            first.fmt_to_string(&self.store)
                        ),
                        Some(proof_id) => {
                            LurkProof::verify_proof(&proof_id)?;
                        }
                    }
                }
            }
            _ => bail!("Unsupported meta command: {cmd}"),
        }
        Ok(())
    }

    fn handle_meta(&mut self, expr_ptr: Ptr<F>, pwd_path: &Path) -> Result<()> {
        let (car, cdr) = self.store.car_cdr(&expr_ptr)?;
        match &self.store.fetch_symbol(&car) {
            Some(symbol) => {
                self.handle_meta_cases(format!("{}", symbol).as_str(), &cdr, pwd_path)?
            }
            None => bail!(
                "Meta command must be a symbol. Found {}",
                car.fmt_to_string(&self.store)
            ),
        }
        Ok(())
    }

    fn eval_expr_and_memoize(&mut self, expr_ptr: Ptr<F>) -> Result<(IO<F>, usize)> {
        let frames = Evaluator::new(expr_ptr, self.env, &mut self.store, self.limit, &self.lang)
            .get_frames()?;

        let last_frame_idx = frames.len() - 1;
        let last_frame = &frames[last_frame_idx];
        let last_output = last_frame.output;

        let iterations = if last_frame.is_complete() {
            last_frame_idx
        } else {
            last_frame_idx + 1
        };

        self.evaluation = Some(Evaluation {
            frames,
            last_frame_idx,
            iterations,
        });

        Ok((last_output, iterations))
    }

    fn handle_non_meta(&mut self, expr_ptr: Ptr<F>) -> Result<()> {
        self.eval_expr_and_memoize(expr_ptr)
            .map(|(output, iterations)| {
                let iterations_display = if iterations != 1 {
                    format!("{iterations} iterations")
                } else {
                    "1 iteration".into()
                };
                match output.cont.tag {
                    ContTag::Terminal => {
                        println!(
                            "[{iterations_display}] => {}",
                            output.expr.fmt_to_string(&self.store)
                        )
                    }
                    ContTag::Error => println!("ERROR after {iterations_display}"),
                    _ => println!("LIMIT REACHED after {iterations_display}"),
                }
            })
    }

    fn handle_form<'a>(
        &mut self,
        input: parser::Span<'a>,
        pwd_path: &Path,
    ) -> Result<parser::Span<'a>> {
        let (input, ptr, is_meta) = self.store.read_maybe_meta(input)?;

        if is_meta {
            self.handle_meta(ptr, pwd_path)?;
        } else {
            self.handle_non_meta(ptr)?;
        }
        Ok(input)
    }

    pub fn load_file(&mut self, file_path: &Path) -> Result<()> {
        let input = read_to_string(file_path)?;
        println!("Loading {}", file_path.display());

        let mut input = parser::Span::new(&input);
        loop {
            match self.handle_form(input, file_path) {
                Ok(new_input) => input = new_input,
                Err(e) => {
                    if let Some(parser::Error::NoInput) = e.downcast_ref::<parser::Error>() {
                        // It's ok, it just means we've hit the EOF
                        return Ok(());
                    } else {
                        return Err(e);
                    }
                }
            }
        }
    }

    pub fn start(&mut self) -> Result<()> {
        println!("Lurk REPL welcomes you.");

        let pwd_path = &std::env::current_dir()?;

        let mut editor: Editor<InputValidator, DefaultHistory> = Editor::with_config(
            Config::builder()
                .color_mode(rustyline::ColorMode::Enabled)
                .auto_add_history(true)
                .build(),
        )?;

        editor.set_helper(Some(InputValidator {
            brackets: MatchingBracketValidator::new(),
        }));

        #[cfg(not(target_arch = "wasm32"))]
        let history_path = &crate::cli::paths::non_wasm::repl_history();

        #[cfg(not(target_arch = "wasm32"))]
        if history_path.exists() {
            editor.load_history(history_path)?;
        }

        loop {
            match editor.readline("> ") {
                Ok(line) => {
                    #[cfg(not(target_arch = "wasm32"))]
                    editor.save_history(history_path)?;
                    match self.store.read_maybe_meta(parser::Span::new(&line)) {
                        Ok((_, expr_ptr, is_meta)) => {
                            if is_meta {
                                if let Err(e) = self.handle_meta(expr_ptr, pwd_path) {
                                    println!("!Error: {e}");
                                }
                            } else if let Err(e) = self.handle_non_meta(expr_ptr) {
                                println!("Error: {e}");
                            }
                        }
                        Err(parser::Error::NoInput) => (),
                        Err(e) => {
                            println!("Read error: {e}")
                        }
                    }
                }
                Err(ReadlineError::Interrupted | ReadlineError::Eof) => {
                    println!("Exiting...");
                    break;
                }
                Err(err) => {
                    println!("Read line error: {err}");
                    break;
                }
            }
        }
        Ok(())
    }
}

mod test {
    #[test]
    fn test_padding() {
        use crate::cli::repl::pad;
        assert_eq!(pad(61, 10), 70);
        assert_eq!(pad(1, 10), 10);
        assert_eq!(pad(61, 1), 61);
        assert_eq!(pad(610, 10), 610);
        assert_eq!(pad(619, 20), 620);
    }
}
