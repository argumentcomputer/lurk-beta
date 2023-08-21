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
use std::{cell::RefCell, fs::read_to_string, process, rc::Rc};

use crate::{
    cli::{commitment_lem::Commitment, paths::proof_path},
    eval::lang::Lang,
    field::LurkField,
    lem::{
        eval::eval_step,
        interpreter::Frame,
        pointers::{Ptr, ZPtr},
        store::Store,
        zstore::{populate_store, populate_z_store, ZStore},
        Func, Tag,
    },
    package::{Package, SymbolRef},
    parser,
    proof::{
        nova_lem::{public_params, NovaProver},
        Prover,
    },
    state::State,
    tag::ContTag::*,
    tag::ExprTag::*,
    Symbol,
};

use super::{backend::Backend, field_data::load, lurk_proof::LurkProof, paths::commitment_path};

#[allow(dead_code)]
struct Evaluation<F: LurkField> {
    frames: Vec<Frame<F>>,
    iterations: usize,
}

pub(crate) struct ReplLEM<F: LurkField> {
    store: Store<F>,
    state: Rc<RefCell<State>>,
    env: Ptr<F>,
    rc: usize,
    limit: usize,
    backend: Backend,
    func: Func,
    evaluation: Option<Evaluation<F>>,
}

type F = pasta_curves::pallas::Scalar; // TODO: generalize this

#[derive(Completer, Helper, Highlighter, Hinter)]
struct InputValidator {
    brackets: MatchingBracketValidator,
}

impl Validator for InputValidator {
    fn validate(&self, ctx: &mut ValidationContext<'_>) -> rustyline::Result<ValidationResult> {
        self.brackets.validate(ctx)
    }
}

/// `pad(a, m)` returns the first multiple of `m` that's equal or greater than `a`
///
/// Panics if `m` is zero
#[inline]
fn pad(a: usize, m: usize) -> usize {
    (a + m - 1) / m * m
}

impl ReplLEM<F> {
    pub(crate) fn new(store: Option<Store<F>>, rc: usize, limit: usize, backend: Backend) -> Self {
        let limit = pad(limit, rc);
        info!(
            "Launching REPL with backend {backend}, field {}, rc {rc} and limit {limit}",
            F::FIELD
        );
        let func = eval_step();
        let mut store = store.unwrap_or_else(|| func.init_store());
        let env = store.intern_nil();
        Self {
            store,
            state: State::init_lurk_state().rccell(),
            env,
            rc,
            limit,
            backend,
            func,
            evaluation: None,
        }
    }

    fn proof_claim(
        store: &mut Store<F>,
        exprs: (Ptr<F>, Ptr<F>),
        envs: (Ptr<F>, Ptr<F>),
        conts: (Ptr<F>, Ptr<F>),
    ) -> Ptr<F> {
        let expr_key = store.key("expr");
        let env_key = store.key("env");
        let cont_key = store.key("cont");
        let expr_out_key = store.key("expr-out");
        let env_out_key = store.key("env-out");
        let cont_out_key = store.key("cont-out");
        store.list(vec![
            expr_key,
            exprs.0,
            env_key,
            envs.0,
            cont_key,
            conts.0,
            expr_out_key,
            exprs.1,
            env_out_key,
            envs.1,
            cont_out_key,
            conts.1,
        ])
    }

    #[allow(dead_code)]
    fn proof_key(backend: &Backend, rc: &usize, claim_hash: &str) -> String {
        let field = F::FIELD;
        format!("{backend}_{field}_{rc}_{claim_hash}")
    }

    pub(crate) fn prove_last_frames(&mut self) -> Result<()> {
        if let Some(Evaluation {
            frames,
            iterations: _,
        }) = self.evaluation.as_mut()
        {
            match self.backend {
                Backend::Nova => {
                    info!("Hydrating the store");
                    self.store.hydrate_z_cache();

                    let mut n_frames = frames.len();

                    // saving to avoid clones
                    let input = &frames[0].input;
                    let output = &frames[n_frames - 1].output;
                    let mut z_store = ZStore::<F>::default();
                    let expr = populate_z_store(&mut z_store, &input[0], &self.store)?;
                    let env = populate_z_store(&mut z_store, &input[1], &self.store)?;
                    let cont = populate_z_store(&mut z_store, &input[2], &self.store)?;
                    let expr_out = populate_z_store(&mut z_store, &output[0], &self.store)?;
                    let env_out = populate_z_store(&mut z_store, &output[1], &self.store)?;
                    let cont_out = populate_z_store(&mut z_store, &output[2], &self.store)?;

                    let claim = Self::proof_claim(
                        &mut self.store,
                        (input[0], output[0]),
                        (input[1], output[1]),
                        (input[2], output[2]),
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
                        let pp = public_params(&self.func, self.rc);

                        let prover = NovaProver::new(self.rc, Lang::new());

                        info!("Proving");
                        let (proof, public_inputs, public_outputs, num_steps) =
                            prover.prove(&self.func, &pp, frames, &mut self.store)?;
                        assert_eq!(self.rc * num_steps, n_frames);

                        info!("Compressing proof");
                        let proof = proof.compress(&pp)?;
                        assert!(proof.verify(&pp, num_steps, &public_inputs, &public_outputs)?);

                        // TODO: persist proof
                        claim_comm.persist()?;
                    }
                    println!("Claim hash: 0x{claim_hash}");
                    println!("Proof key: \"{proof_key}\"");
                    Ok(())
                }
                Backend::SnarkPackPlus => todo!(),
            }
        } else {
            bail!("No evaluation to prove")
        }
    }

    fn pretty_iterations_display(iterations: usize) -> String {
        if iterations != 1 {
            format!("{iterations} iterations")
        } else {
            "1 iteration".into()
        }
    }

    fn eval_expr(&mut self, expr_ptr: Ptr<F>) -> Result<(Vec<Ptr<F>>, usize, Vec<Ptr<F>>)> {
        let outermost = Ptr::null(Tag::Cont(Outermost));
        let terminal = Ptr::null(Tag::Cont(Terminal));
        let error = Ptr::null(Tag::Cont(Error));
        let nil = self.store.intern_nil();

        let stop_cond = |output: &[Ptr<F>]| output[2] == terminal || output[2] == error;

        let input = vec![expr_ptr, nil, outermost];
        self.func
            .call_until_simple(input, &mut self.store, stop_cond, self.limit)
    }

    fn eval_expr_and_memoize(&mut self, expr_ptr: Ptr<F>) -> Result<(Vec<Ptr<F>>, usize)> {
        let outermost = Ptr::null(Tag::Cont(Outermost));
        let terminal = Ptr::null(Tag::Cont(Terminal));
        let error = Ptr::null(Tag::Cont(Error));
        let nil = self.store.intern_nil();

        let stop_cond = |output: &[Ptr<F>]| output[2] == terminal || output[2] == error;

        let input = [expr_ptr, nil, outermost];

        let (frames, iterations, _) =
            self.func
                .call_until(&input, &mut self.store, stop_cond, self.limit)?;

        let output = frames[frames.len() - 1].output.clone();

        self.evaluation = Some(Evaluation { frames, iterations });

        Ok((output, iterations))
    }

    fn peek1(&mut self, cmd: &str, args: &Ptr<F>) -> Result<Ptr<F>> {
        let (first, rest) = self.store.car_cdr(args)?;
        if !rest.is_nil() {
            bail!("`{cmd}` accepts at most one argument")
        }
        Ok(first)
    }

    fn peek2(&mut self, cmd: &str, args: &Ptr<F>) -> Result<(Ptr<F>, Ptr<F>)> {
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
        let num = self.store.intern_lurk_sym("num");
        let expr = self.store.list(vec![num, first]);
        let (expr_io, ..) = self
            .eval_expr(expr)
            .with_context(|| "evaluating first arg")?;
        let Ptr::Leaf(Tag::Expr(Num), hash) = expr_io[0] else {
            bail!("hash must be a number")
        };
        Ok(hash)
    }

    fn get_string(&self, ptr: &Ptr<F>) -> &String {
        self.store
            .fetch_string(ptr)
            .expect("string must have been interned")
    }

    fn get_symbol(&self, ptr: &Ptr<F>) -> &Symbol {
        self.store
            .fetch_symbol(ptr)
            .expect("symbol must have been interned")
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
            let (secret, z_payload) = commitment.open()?;
            let payload = populate_store(&mut self.store, z_payload, &commitment.z_store)?;
            self.store.hide(*secret, payload)?;
            if print_data {
                println!(
                    "{}",
                    payload.fmt_to_string(&self.store, &self.state.borrow())
                );
            } else {
                println!("Data is now available");
            }
        }
        Ok(())
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
                let l = self.store.intern_lurk_sym("let");
                let current_env = self.store.intern_lurk_sym("current-env");
                let binding = self.store.list(vec![first, second]);
                let bindings = self.store.list(vec![binding]);
                let current_env_call = self.store.list(vec![current_env]);
                let expanded = self.store.list(vec![l, bindings, current_env_call]);
                let (expanded_io, ..) = self.eval_expr(expanded)?;

                self.env = expanded_io[1];

                let (new_binding, _) = &self.store.car_cdr(&expanded_io[0])?;
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
                let l = self.store.intern_lurk_sym("letrec");
                let current_env = self.store.intern_lurk_sym("current-env");
                let binding = self.store.list(vec![first, second]);
                let bindings = self.store.list(vec![binding]);
                let current_env_call = self.store.list(vec![current_env]);
                let expanded = self.store.list(vec![l, bindings, current_env_call]);
                let (expanded_io, ..) = self.eval_expr(expanded)?;

                self.env = expanded_io[1];

                let (new_binding_outer, _) = &self.store.car_cdr(&expanded_io[0])?;
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
                if first_io[0].is_nil() {
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
                if first_io[0] != second_io[0] {
                    eprintln!(
                        "`assert-eq` failed. Expected:\n  {} = {}\nGot:\n  {} ≠ {}",
                        first.fmt_to_string(&self.store, &self.state.borrow()),
                        second.fmt_to_string(&self.store, &self.state.borrow()),
                        first_io[0].fmt_to_string(&self.store, &self.state.borrow()),
                        second_io[0].fmt_to_string(&self.store, &self.state.borrow())
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
                let (mut first_emitted, mut rest_emitted) = self.store.car_cdr(&first_io[0])?;
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
                self.hide(ff::Field::ZERO, first_io[0])?;
            }
            "hide" => {
                let (first, second) = self.peek2(cmd, args)?;
                let (first_io, ..) = self
                    .eval_expr(first)
                    .with_context(|| "evaluating first arg")?;
                let (second_io, ..) = self
                    .eval_expr(second)
                    .with_context(|| "evaluating second arg")?;
                let Ptr::Leaf(Tag::Expr(Num), secret) = first_io[0] else {
                    bail!(
                        "Secret must be a number. Got {}",
                        first_io[0].fmt_to_string(&self.store, &self.state.borrow())
                    )
                };
                self.hide(secret, second_io[0])?;
            }
            "fetch" => {
                let hash = self.get_comm_hash(cmd, args)?;
                self.fetch(&hash, false)?;
            }
            "open" => {
                let hash = self.get_comm_hash(cmd, args)?;
                self.fetch(&hash, true)?;
            }
            "clear" => self.env = self.store.intern_nil(),
            "set-env" => {
                // The state's env is set to the result of evaluating the first argument.
                let first = self.peek1(cmd, args)?;
                let (first_io, ..) = self.eval_expr(first)?;
                self.env = first_io[0];
            }
            "prove" => {
                if !args.is_nil() {
                    let expr = self.peek1(cmd, args)?;
                    self.eval_expr_and_memoize(expr)?;
                }
                self.prove_last_frames()?;
            }
            "verify" => {
                let first = self.peek1(cmd, args)?;
                let proof_id = self.get_string(&first);
                LurkProof::verify_proof(proof_id)?;
            }
            "defpackage" => {
                // TODO: handle args
                let (name, _args) = self.store.car_cdr(args)?;
                let name = match name.tag() {
                    Tag::Expr(Str) => self.state.borrow_mut().intern(self.get_string(&name)),
                    Tag::Expr(Sym) => self.get_symbol(&name).clone().into(),
                    _ => bail!("Package name must be a string or a symbol"),
                };
                println!("{}", self.state.borrow().fmt_to_string(&name));
                let package = Package::new(name);
                self.state.borrow_mut().add_package(package);
            }
            "import" => {
                // TODO: handle pkg
                let (mut symbols, _pkg) = self.store.car_cdr(args)?;
                if symbols.tag() == &Tag::Expr(Sym) {
                    let sym = SymbolRef::new(self.get_symbol(&symbols).clone());
                    self.state.borrow_mut().import(&[sym])?;
                } else {
                    let mut symbols_vec = vec![];
                    loop {
                        {
                            let (head, tail) = self.store.car_cdr(&symbols)?;
                            symbols_vec.push(SymbolRef::new(self.get_symbol(&head).clone()));
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
                match first.tag() {
                    Tag::Expr(Str) => {
                        let name = self.get_string(&first);
                        let package_name = self.state.borrow_mut().intern(name);
                        self.state.borrow_mut().set_current_package(package_name)?;
                    }
                    Tag::Expr(Sym) => {
                        let package_name = self.get_symbol(&first).clone();
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
                match output[2].tag() {
                    Tag::Cont(Terminal) => {
                        println!(
                            "[{iterations_display}] => {}",
                            output[0].fmt_to_string(&self.store, &self.state.borrow())
                        )
                    }
                    Tag::Cont(Error) => {
                        println!("Evaluation encountered an error after {iterations_display}")
                    }
                    _ => println!("Limit reached after {iterations_display}"),
                }
            })
    }

    fn handle_meta(&mut self, expr_ptr: Ptr<F>, pwd_path: &Utf8Path) -> Result<()> {
        let (car, cdr) = self.store.car_cdr(&expr_ptr)?;
        match self.store.fetch_sym(&car).cloned() {
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
        let (ptr, is_meta) = self.store.read_maybe_meta(self.state.clone(), &input)?;
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
                    match self.store.read_maybe_meta(self.state.clone(), &line) {
                        Ok((expr_ptr, is_meta)) => {
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
