use std::cell::RefCell;
use std::fs::read_to_string;
use std::process;
use std::rc::Rc;
use std::sync::Arc;

use anyhow::{bail, Context, Result};
use camino::{Utf8Path, Utf8PathBuf};
use log::info;
use rustyline::{
    error::ReadlineError,
    history::DefaultHistory,
    validate::{MatchingBracketValidator, ValidationContext, ValidationResult, Validator},
    Config, Editor,
};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};

use super::{
    backend::Backend,
    commitment::Commitment,
    field_data::load,
    lurk_proof::{LurkProof, LurkProofMeta},
    paths::commitment_path,
};

use crate::{
    cli::paths::{proof_path, public_params_dir},
    eval::{
        lang::{Coproc, Lang},
        Evaluator, Frame, Witness, IO,
    },
    field::LurkField,
    lurk_sym_ptr,
    package::{Package, SymbolRef},
    parser,
    proof::{nova::NovaProver, Prover},
    ptr::Ptr,
    public_parameters::public_params,
    state::State,
    store::Store,
    tag::{ContTag, ExprTag},
    writer::Write,
    z_ptr::ZExprPtr,
    z_store::ZStore,
    Num, Symbol,
};

#[derive(Completer, Helper, Highlighter, Hinter)]
struct InputValidator {
    brackets: MatchingBracketValidator,
}

impl Validator for InputValidator {
    fn validate(&self, ctx: &mut ValidationContext<'_>) -> rustyline::Result<ValidationResult> {
        self.brackets.validate(ctx)
    }
}

#[allow(dead_code)]
struct Evaluation<F: LurkField> {
    frames: Vec<Frame<IO<F>, Witness<F>, Coproc<F>>>,
    iterations: usize,
}

#[allow(dead_code)]
pub(crate) struct Repl<F: LurkField> {
    store: Store<F>,
    state: Rc<RefCell<State>>,
    env: Ptr<F>,
    lang: Arc<Lang<F, Coproc<F>>>,
    rc: usize,
    limit: usize,
    backend: Backend,
    evaluation: Option<Evaluation<F>>,
}

pub(crate) fn validate_non_zero(name: &str, x: usize) -> Result<()> {
    if x == 0 {
        bail!("`{name}` can't be zero")
    }
    Ok(())
}

/// `pad(a, m)` returns the first multiple of `m` that's equal or greater than `a`
///
/// Panics if `m` is zero
#[inline]
fn pad(a: usize, m: usize) -> usize {
    (a + m - 1) / m * m
}

type F = pasta_curves::pallas::Scalar; // TODO: generalize this

impl Repl<F> {
    pub(crate) fn new(
        store: Store<F>,
        env: Ptr<F>,
        rc: usize,
        limit: usize,
        backend: Backend,
    ) -> Self {
        let limit = pad(limit, rc);
        info!(
            "Launching REPL with backend {backend}, field {}, rc {rc} and limit {limit}",
            F::FIELD
        );
        Self {
            store,
            state: State::init_lurk_state().rccell(),
            env,
            lang: Arc::new(Lang::new()),
            rc,
            limit,
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

    #[allow(dead_code)]
    fn proof_key(backend: &Backend, rc: &usize, claim_hash: &str) -> String {
        let field = F::FIELD;
        format!("{backend}_{field}_{rc}_{claim_hash}")
    }

    pub(crate) fn prove_last_frames(&mut self) -> Result<()> {
        match self.evaluation.as_mut() {
            None => bail!("No evaluation to prove"),
            Some(Evaluation { frames, iterations }) => match self.backend {
                Backend::Nova => {
                    info!("Hydrating the store");
                    self.store.hydrate_scalar_cache();

                    let mut n_frames = frames.len();

                    // saving to avoid clones
                    let input = &frames[0].input;
                    let output = &frames[n_frames - 1].output;
                    let mut zstore = Some(ZStore::<F>::default());
                    let expr = self.store.get_z_expr(&input.expr, &mut zstore)?.0;
                    let env = self.store.get_z_expr(&input.env, &mut zstore)?.0;
                    let cont = self.store.get_z_cont(&input.cont, &mut zstore)?.0;
                    let expr_out = self.store.get_z_expr(&output.expr, &mut zstore)?.0;
                    let env_out = self.store.get_z_expr(&output.env, &mut zstore)?.0;
                    let cont_out = self.store.get_z_cont(&output.cont, &mut zstore)?.0;

                    let claim = Self::proof_claim(
                        &mut self.store,
                        (input.expr, output.expr),
                        (input.env, output.env),
                        (cont.parts(), cont_out.parts()),
                    );

                    let claim_comm = Commitment::new(None, claim, &mut self.store)?;
                    let claim_hash = &claim_comm.hash.hex_digits();
                    let proof_key = &Self::proof_key(&self.backend, &self.rc, claim_hash);
                    let proof_path = proof_path(proof_key);

                    if proof_path.exists() {
                        info!("Proof already cached");
                        // TODO: make sure that the proof file is not corrupted
                    } else {
                        info!("Proof not cached");
                        // padding the frames, if needed
                        let n_pad = pad(n_frames, self.rc) - n_frames;
                        if n_pad != 0 {
                            frames.extend(vec![frames[n_frames - 1].clone(); n_pad]);
                            n_frames = frames.len();
                        }

                        info!("Loading public parameters");
                        let pp = public_params(self.rc, self.lang.clone(), &public_params_dir())?;

                        let prover = NovaProver::new(self.rc, (*self.lang).clone());

                        info!("Proving");
                        let (proof, public_inputs, public_outputs, num_steps) =
                            prover.prove(&pp, frames, &mut self.store, self.lang.clone())?;
                        info!("Compressing proof");
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

                        lurk_proof.persist(proof_key)?;
                        lurk_proof_meta.persist(proof_key)?;
                        claim_comm.persist()?;
                    }
                    println!("Claim hash: 0x{claim_hash}");
                    println!("Proof key: \"{proof_key}\"");
                    Ok(())
                }
                Backend::SnarkPackPlus => todo!(),
            },
        }
    }

    fn hide(&mut self, secret: F, payload: Ptr<F>) -> Result<()> {
        let commitment = Commitment::new(Some(secret), payload, &mut self.store)?;
        let hash_str = &commitment.hash.hex_digits();
        commitment.persist()?;
        println!(
            "Data: {}\nHash: 0x{hash_str}",
            payload.fmt_to_string(&self.store, &self.state.borrow())
        );
        Ok(())
    }

    fn fetch(&mut self, hash: &F, print_data: bool) -> Result<()> {
        let commitment: Commitment<F> = load(commitment_path(&hash.hex_digits()))?;
        let comm_hash = commitment.hash;
        if &comm_hash != hash {
            bail!("Hash mismatch. Corrupted commitment file.")
        } else {
            // create a ZExprPtr with the intended hash
            let comm_zptr = &ZExprPtr::from_parts(ExprTag::Comm, comm_hash);
            // populate the REPL's store with the data
            let comm_ptr = self
                .store
                .intern_z_expr_ptr(comm_zptr, &commitment.zstore)
                .unwrap();
            if print_data {
                let data = self.store.fetch_comm(&comm_ptr).unwrap().1;
                println!("{}", data.fmt_to_string(&self.store, &self.state.borrow()));
            } else {
                println!("Data is now available");
            }
        }
        Ok(())
    }

    fn pretty_iterations_display(iterations: usize) -> String {
        if iterations != 1 {
            format!("{iterations} iterations")
        } else {
            "1 iteration".into()
        }
    }

    fn eval_expr(&mut self, expr_ptr: Ptr<F>) -> Result<(IO<F>, usize, Vec<Ptr<F>>)> {
        let ret =
            Evaluator::new(expr_ptr, self.env, &mut self.store, self.limit, &self.lang).eval()?;
        match ret.0.cont.tag {
            ContTag::Terminal => Ok(ret),
            t => {
                let iterations_display = Self::pretty_iterations_display(ret.1);
                match t {
                    ContTag::Error => {
                        bail!("Evaluation encountered an error after {iterations_display}")
                    }
                    _ => bail!("Limit reached after {iterations_display}"),
                }
            }
        }
    }

    fn eval_expr_and_memoize(&mut self, expr_ptr: Ptr<F>) -> Result<(IO<F>, usize)> {
        let frames = Evaluator::new(expr_ptr, self.env, &mut self.store, self.limit, &self.lang)
            .get_frames()?;

        let n_frames = frames.len();
        let last_frame = &frames[n_frames - 1];
        let last_output = last_frame.output;

        let iterations = if last_frame.is_complete() {
            // do not consider the identity frame
            n_frames - 1
        } else {
            n_frames
        };

        self.evaluation = Some(Evaluation { frames, iterations });

        Ok((last_output, iterations))
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

    #[allow(dead_code)]
    fn get_comm_hash(&mut self, cmd: &str, args: &Ptr<F>) -> Result<F> {
        let first = self.peek1(cmd, args)?;
        let num = lurk_sym_ptr!(self.store, num);
        let expr = self.store.list(&[num, first]);
        let (expr_io, ..) = self
            .eval_expr(expr)
            .with_context(|| "evaluating first arg")?;
        let hash = self
            .store
            .fetch_num(&expr_io.expr)
            .expect("must be a number");
        Ok(hash.into_scalar())
    }

    fn get_string(&self, ptr: &Ptr<F>) -> Result<String> {
        match self.store.fetch_string(ptr) {
            None => bail!(
                "Expected string. Got {}",
                ptr.fmt_to_string(&self.store, &self.state.borrow())
            ),
            Some(string) => Ok(string),
        }
    }

    fn get_symbol(&self, ptr: &Ptr<F>) -> Result<Symbol> {
        match self.store.fetch_symbol(ptr) {
            None => bail!(
                "Expected symbol. Got {}",
                ptr.fmt_to_string(&self.store, &self.state.borrow())
            ),
            Some(symbol) => Ok(symbol),
        }
    }

    fn handle_meta_cases(&mut self, cmd: &str, args: &Ptr<F>, pwd_path: &Utf8Path) -> Result<()> {
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
                let l = lurk_sym_ptr!(&self.store, let_);
                let current_env = lurk_sym_ptr!(&self.store, current_env);
                let binding = &self.store.list(&[first, second]);
                let bindings = &self.store.list(&[*binding]);
                let current_env_call = &self.store.list(&[current_env]);
                let expanded = &self.store.list(&[l, *bindings, *current_env_call]);
                let (expanded_io, ..) = self.eval_expr(*expanded)?;

                self.env = expanded_io.expr;

                let (new_binding, _) = &self.store.car_cdr(&expanded_io.expr)?;
                let (new_name, _) = self.store.car_cdr(new_binding)?;
                println!(
                    "{}",
                    new_name.fmt_to_string(&self.store, &self.state.borrow())
                );
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
                let l = lurk_sym_ptr!(&self.store, letrec);
                let current_env = lurk_sym_ptr!(&self.store, current_env);
                let binding = &self.store.list(&[first, second]);
                let bindings = &self.store.list(&[*binding]);
                let current_env_call = &self.store.list(&[current_env]);
                let expanded = &self.store.list(&[l, *bindings, *current_env_call]);
                let (expanded_io, ..) = self.eval_expr(*expanded)?;

                self.env = expanded_io.expr;

                let (new_binding_outer, _) = &self.store.car_cdr(&expanded_io.expr)?;
                let (new_binding_inner, _) = &self.store.car_cdr(new_binding_outer)?;
                let (new_name, _) = self.store.car_cdr(new_binding_inner)?;
                println!(
                    "{}",
                    new_name.fmt_to_string(&self.store, &self.state.borrow())
                );
            }
            "load" => {
                let first = self.peek1(cmd, args)?;
                match self.store.fetch_string(&first) {
                    Some(path) => {
                        let joined = pwd_path.join(Utf8Path::new(&path));
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
                        first.fmt_to_string(&self.store, &self.state.borrow())
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
                        first.fmt_to_string(&self.store, &self.state.borrow()),
                        second.fmt_to_string(&self.store, &self.state.borrow()),
                        first_io
                            .expr
                            .fmt_to_string(&self.store, &self.state.borrow()),
                        second_io
                            .expr
                            .fmt_to_string(&self.store, &self.state.borrow())
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
                            first_emitted.fmt_to_string(&self.store, &self.state.borrow()),
                            elem.fmt_to_string(&self.store, &self.state.borrow()),
                        );
                        process::exit(1);
                    }
                    (first_emitted, rest_emitted) = self.store.car_cdr(&rest_emitted)?;
                }
            }
            "assert-error" => {
                let first = self.peek1(cmd, args)?;
                if self.eval_expr(first).is_ok() {
                    eprintln!(
                        "`assert-error` failed. {} doesn't result on evaluation error.",
                        first.fmt_to_string(&self.store, &self.state.borrow())
                    );
                    process::exit(1);
                }
            }
            "commit" => {
                let first = self.peek1(cmd, args)?;
                let (first_io, ..) = self.eval_expr(first)?;
                self.hide(ff::Field::ZERO, first_io.expr)?;
            }
            "hide" => {
                let (first, second) = self.peek2(cmd, args)?;
                let (first_io, ..) = self
                    .eval_expr(first)
                    .with_context(|| "evaluating first arg")?;
                let (second_io, ..) = self
                    .eval_expr(second)
                    .with_context(|| "evaluating second arg")?;
                let Some(secret) = self.store.fetch_num(&first_io.expr) else {
                    bail!(
                        "Secret must be a number. Got {}",
                        first_io.expr.fmt_to_string(&self.store, &self.state.borrow())
                    )
                };
                self.hide(secret.into_scalar(), second_io.expr)?;
            }
            "fetch" => {
                let hash = self.get_comm_hash(cmd, args)?;
                self.fetch(&hash, false)?;
            }
            "open" => {
                let hash = self.get_comm_hash(cmd, args)?;
                self.fetch(&hash, true)?;
            }
            "clear" => self.env = lurk_sym_ptr!(&self.store, nil),
            "set-env" => {
                // The state's env is set to the result of evaluating the first argument.
                let first = self.peek1(cmd, args)?;
                let (first_io, ..) = self.eval_expr(first)?;
                self.env = first_io.expr;
            }
            "prove" => {
                if !args.is_nil() {
                    self.eval_expr_and_memoize(self.peek1(cmd, args)?)?;
                }
                self.prove_last_frames()?;
            }
            "verify" => {
                let first = self.peek1(cmd, args)?;
                let proof_id = self.get_string(&first)?;
                LurkProof::verify_proof(&proof_id)?;
            }
            "defpackage" => {
                // TODO: handle args
                let (name, _args) = self.store.car_cdr(args)?;
                let name = match name.tag {
                    ExprTag::Str => self.state.borrow_mut().intern(self.get_string(&name)?),
                    ExprTag::Sym => self.get_symbol(&name)?.into(),
                    _ => bail!("Package name must be a string or a symbol"),
                };
                println!("{}", self.state.borrow().fmt_to_string(&name));
                let package = Package::new(name);
                self.state.borrow_mut().add_package(package);
            }
            "import" => {
                // TODO: handle pkg
                let (mut symbols, _pkg) = self.store.car_cdr(args)?;
                if symbols.tag == ExprTag::Sym {
                    let sym = SymbolRef::new(self.get_symbol(&symbols)?);
                    self.state.borrow_mut().import(&[sym])?;
                } else {
                    let mut symbols_vec = vec![];
                    loop {
                        {
                            let (head, tail) = self.store.car_cdr(&symbols)?;
                            let sym = self.get_symbol(&head)?;
                            symbols_vec.push(SymbolRef::new(sym));
                            if tail.is_nil() {
                                break;
                            }
                            symbols = tail;
                        }
                    }
                    self.state.borrow_mut().import(&symbols_vec)?;
                }
            }
            "in-package" => {
                let first = self.peek1(cmd, args)?;
                match first.tag {
                    ExprTag::Str => {
                        let name = self.get_string(&first)?;
                        let package_name = self.state.borrow_mut().intern(name);
                        self.state.borrow_mut().set_current_package(package_name)?;
                    }
                    ExprTag::Sym => {
                        let package_name = self.get_symbol(&first)?;
                        self.state
                            .borrow_mut()
                            .set_current_package(package_name.into())?;
                    }
                    _ => bail!(
                        "Expected string or symbol. Got {}",
                        first.fmt_to_string(&self.store, &self.state.borrow())
                    ),
                }
            }
            _ => bail!("Unsupported meta command: {cmd}"),
        }
        Ok(())
    }

    fn handle_non_meta(&mut self, expr_ptr: Ptr<F>) -> Result<()> {
        self.eval_expr_and_memoize(expr_ptr)
            .map(|(output, iterations)| {
                let iterations_display = Self::pretty_iterations_display(iterations);
                match output.cont.tag {
                    ContTag::Terminal => {
                        println!(
                            "[{iterations_display}] => {}",
                            output.expr.fmt_to_string(&self.store, &self.state.borrow())
                        )
                    }
                    ContTag::Error => {
                        println!("Evaluation encountered an error after {iterations_display}")
                    }
                    _ => println!("Limit reached after {iterations_display}"),
                }
            })
    }

    fn handle_meta(&mut self, expr_ptr: Ptr<F>, pwd_path: &Utf8Path) -> Result<()> {
        let (car, cdr) = self.store.car_cdr(&expr_ptr)?;
        match &self.store.fetch_sym(&car) {
            Some(symbol) => self.handle_meta_cases(symbol.name()?, &cdr, pwd_path)?,
            None => bail!(
                "Meta command must be a symbol. Found {}",
                car.fmt_to_string(&self.store, &self.state.borrow())
            ),
        }
        Ok(())
    }

    fn handle_form<'a>(
        &mut self,
        input: parser::Span<'a>,
        pwd_path: &Utf8Path,
    ) -> Result<parser::Span<'a>> {
        let (input, ptr, is_meta) = self
            .store
            .read_maybe_meta_with_state(self.state.clone(), input)?;

        if is_meta {
            self.handle_meta(ptr, pwd_path)?;
        } else {
            self.handle_non_meta(ptr)?;
        }
        Ok(input)
    }

    pub(crate) fn load_file(&mut self, file_path: &Utf8Path) -> Result<()> {
        let input = read_to_string(file_path)?;
        println!("Loading {}", file_path);

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

    pub(crate) fn start(&mut self) -> Result<()> {
        println!("Lurk REPL welcomes you.");

        let pwd_path = Utf8PathBuf::from_path_buf(std::env::current_dir()?)
            .expect("path contains invalid Unicode");

        let mut editor: Editor<InputValidator, DefaultHistory> = Editor::with_config(
            Config::builder()
                .color_mode(rustyline::ColorMode::Enabled)
                .auto_add_history(true)
                .build(),
        )?;

        editor.set_helper(Some(InputValidator {
            brackets: MatchingBracketValidator::new(),
        }));

        let history_path = &crate::cli::paths::repl_history();

        if history_path.exists() {
            editor.load_history(history_path)?;
        }

        loop {
            match editor.readline(&format!(
                "{}> ",
                self.state
                    .borrow()
                    .fmt_to_string(self.state.borrow().get_current_package_name())
            )) {
                Ok(line) => {
                    editor.save_history(history_path)?;
                    match self
                        .store
                        .read_maybe_meta_with_state(self.state.clone(), parser::Span::new(&line))
                    {
                        Ok((_, expr_ptr, is_meta)) => {
                            if is_meta {
                                if let Err(e) = self.handle_meta(expr_ptr, &pwd_path) {
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
