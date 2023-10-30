mod meta_cmd;

use anyhow::{bail, Context, Result};
use camino::{Utf8Path, Utf8PathBuf};
use rustyline::{
    error::ReadlineError,
    history::DefaultHistory,
    validate::{MatchingBracketValidator, ValidationContext, ValidationResult, Validator},
    Config, Editor,
};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};
use std::{cell::RefCell, collections::HashMap, fs::read_to_string, io::Write, rc::Rc, sync::Arc};
use tracing::info;

use crate::{
    cli::paths::proof_path,
    eval::lang::{Coproc, Lang},
    field::LurkField,
    lem::{
        eval::{evaluate, evaluate_simple},
        interpreter::Frame,
        multiframe::MultiFrame,
        pointers::Ptr,
        store::Store,
        Tag,
    },
    parser,
    proof::{nova::NovaProver, Prover},
    public_parameters::{
        instance::{Instance, Kind},
        public_params,
    },
    state::State,
    tag::{ContTag, ExprTag},
    Symbol,
};

use super::{
    backend::Backend,
    commitment::Commitment,
    field_data::load,
    lurk_proof::{LurkProof, LurkProofMeta},
    paths::commitment_path,
    zstore::{populate_store, populate_z_store, ZStore},
};

use meta_cmd::MetaCmd;

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
    frames: Vec<Frame<F>>,
    iterations: usize,
}

#[allow(dead_code)]
pub struct Repl<F: LurkField> {
    store: Store<F>,
    state: Rc<RefCell<State>>,
    env: Ptr<F>,
    lang: Arc<Lang<F, Coproc<F>>>,
    rc: usize,
    limit: usize,
    backend: Backend,
    evaluation: Option<Evaluation<F>>,
    pwd_path: Utf8PathBuf,
    meta: HashMap<&'static str, MetaCmd<F>>,
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

impl<F: LurkField> Repl<F> {
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
}

type F = pasta_curves::pallas::Scalar; // TODO: generalize this

impl Repl<F> {
    pub fn new(store: Store<F>, rc: usize, limit: usize, backend: Backend) -> Repl<F> {
        let limit = pad(limit, rc);
        info!(
            "Launching REPL with backend {backend}, field {}, rc {rc} and limit {limit}",
            F::FIELD
        );
        let current_dir = std::env::current_dir().expect("couldn't capture current directory");
        let pwd_path =
            Utf8PathBuf::from_path_buf(current_dir).expect("path contains invalid Unicode");
        let env = store.intern_nil();
        Repl {
            store,
            state: State::init_lurk_state().rccell(),
            env,
            lang: Arc::new(Lang::new()),
            rc,
            limit,
            backend,
            evaluation: None,
            pwd_path,
            meta: MetaCmd::cmds(),
        }
    }

    #[allow(dead_code)]
    fn proof_claim(
        store: &Store<F>,
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
        let (expr, expr_out) = exprs;
        let (env, env_out) = envs;
        let ((cont_tag, cont_val), (cont_out_tag, cont_out_val)) = conts;
        let cont = store.cons(Ptr::num(cont_tag), Ptr::num(cont_val));
        let cont_out = store.cons(Ptr::num(cont_out_tag), Ptr::num(cont_out_val));
        store.list(vec![
            expr_key,
            expr,
            env_key,
            env,
            cont_key,
            cont,
            expr_out_key,
            expr_out,
            env_out_key,
            env_out,
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
        match self.evaluation.as_ref() {
            None => bail!("No evaluation to prove"),
            Some(Evaluation { frames, iterations }) => match self.backend {
                Backend::Nova => {
                    info!("Hydrating the store");
                    self.store.hydrate_z_cache();

                    let n_frames = frames.len();

                    // saving to avoid clones
                    let input = &frames[0].input;
                    let output = &frames[n_frames - 1].output;
                    let mut z_store = ZStore::<F>::default();
                    let mut cache = HashMap::default();
                    let expr = populate_z_store(&mut z_store, &input[0], &self.store, &mut cache)?;
                    let env = populate_z_store(&mut z_store, &input[1], &self.store, &mut cache)?;
                    let cont = populate_z_store(&mut z_store, &input[2], &self.store, &mut cache)?;
                    let expr_out =
                        populate_z_store(&mut z_store, &output[0], &self.store, &mut cache)?;
                    let env_out =
                        populate_z_store(&mut z_store, &output[1], &self.store, &mut cache)?;
                    let cont_out =
                        populate_z_store(&mut z_store, &output[2], &self.store, &mut cache)?;

                    let claim = Self::proof_claim(
                        &self.store,
                        (input[0], output[0]),
                        (input[1], output[1]),
                        (cont.parts(), cont_out.parts()),
                    );

                    let claim_comm = Commitment::new(None, claim, &self.store)?;
                    let claim_hash = &claim_comm.hash.hex_digits();
                    let proof_key = &Self::proof_key(&self.backend, &self.rc, claim_hash);
                    let proof_path = proof_path(proof_key);

                    if proof_path.exists() {
                        info!("Proof already cached");
                        // TODO: make sure that the proof file is not corrupted
                    } else {
                        info!("Proof not cached");

                        info!("Loading public parameters");
                        let instance =
                            Instance::new(self.rc, self.lang.clone(), true, Kind::NovaPublicParams);
                        let pp = public_params(&instance)?;

                        let prover = NovaProver::<F, Coproc<F>, MultiFrame<'_, F, Coproc<F>>>::new(
                            self.rc,
                            (*self.lang).clone(),
                        );

                        info!("Proving");
                        let (proof, public_inputs, public_outputs, num_steps) =
                            prover.prove(&pp, frames, &self.store, &self.lang)?;
                        info!("Compressing proof");
                        let proof = proof.compress(&pp)?;
                        assert_eq!(self.rc * num_steps, pad(n_frames, self.rc));
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
                            z_store,
                        };

                        lurk_proof.persist(proof_key)?;
                        lurk_proof_meta.persist(proof_key)?;
                        claim_comm.persist()?;
                    }
                    println!("Claim hash: 0x{claim_hash}");
                    println!("Proof key: \"{proof_key}\"");
                    Ok(())
                }
            },
        }
    }

    fn hide(&mut self, secret: F, payload: Ptr<F>) -> Result<()> {
        let commitment = Commitment::new(Some(secret), payload, &self.store)?;
        let hash_str = &commitment.hash.hex_digits();
        commitment.persist()?;
        println!(
            "Data: {}\nHash: 0x{hash_str}",
            payload.fmt_to_string(&self.store, &self.state.borrow())
        );
        Ok(())
    }

    fn fetch(&mut self, hash: &F, print_data: bool) -> Result<()> {
        let commitment: Commitment<F> = load(&commitment_path(&hash.hex_digits()))?;
        let comm_hash = commitment.hash;
        if &comm_hash != hash {
            bail!("Hash mismatch. Corrupted commitment file.")
        } else {
            let (secret, z_payload) = commitment.open()?;
            let payload = populate_store(
                &self.store,
                z_payload,
                &commitment.z_store,
                &mut Default::default(),
            )?;
            self.store.hide(*secret, payload);
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

    fn pretty_iterations_display(iterations: usize) -> String {
        if iterations != 1 {
            format!("{iterations} iterations")
        } else {
            "1 iteration".into()
        }
    }

    fn eval_expr(&mut self, expr_ptr: Ptr<F>) -> Result<(Vec<Ptr<F>>, usize, Vec<Ptr<F>>)> {
        let (ptrs, iterations, emitted) =
            evaluate_simple::<F, Coproc<F>>(None, expr_ptr, &self.store, self.limit)?;
        match ptrs[2].tag() {
            Tag::Cont(ContTag::Terminal) => Ok((ptrs, iterations, emitted)),
            t => {
                let iterations_display = Self::pretty_iterations_display(iterations);
                if t == &Tag::Cont(ContTag::Error) {
                    bail!("Evaluation encountered an error after {iterations_display}")
                } else {
                    bail!("Limit reached after {iterations_display}")
                }
            }
        }
    }

    fn eval_expr_allowing_error_continuation(
        &mut self,
        expr_ptr: Ptr<F>,
    ) -> Result<(Vec<Ptr<F>>, usize, Vec<Ptr<F>>)> {
        let (ptrs, iterations, emitted) =
            evaluate_simple::<F, Coproc<F>>(None, expr_ptr, &self.store, self.limit)?;
        if matches!(
            ptrs[2].tag(),
            Tag::Cont(ContTag::Terminal) | Tag::Cont(ContTag::Error)
        ) {
            Ok((ptrs, iterations, emitted))
        } else {
            bail!(
                "Limit reached after {}",
                Self::pretty_iterations_display(iterations)
            )
        }
    }

    fn eval_expr_and_memoize(&mut self, expr_ptr: Ptr<F>) -> Result<(Vec<Ptr<F>>, usize)> {
        let (frames, iterations) =
            evaluate::<F, Coproc<F>>(None, expr_ptr, &self.store, self.limit)?;
        let output = frames[frames.len() - 1].output.clone();
        self.evaluation = Some(Evaluation { frames, iterations });
        Ok((output, iterations))
    }

    // #[allow(dead_code)]
    fn get_comm_hash(&mut self, cmd: &str, args: &Ptr<F>) -> Result<F> {
        let first = self.peek1(cmd, args)?;
        let num = self.store.intern_lurk_symbol("num");
        let expr = self.store.list(vec![num, first]);
        let (expr_io, ..) = self
            .eval_expr(expr)
            .with_context(|| "evaluating first arg")?;
        let Ptr::Atom(Tag::Expr(ExprTag::Num), hash) = expr_io[0] else {
            bail!("hash must be a number")
        };
        Ok(hash)
    }

    fn handle_non_meta(&mut self, expr_ptr: Ptr<F>) -> Result<()> {
        self.eval_expr_and_memoize(expr_ptr)
            .map(|(output, iterations)| {
                let iterations_display = Self::pretty_iterations_display(iterations);
                match output[2].tag() {
                    Tag::Cont(ContTag::Terminal) => {
                        println!(
                            "[{iterations_display}] => {}",
                            output[0].fmt_to_string(&self.store, &self.state.borrow())
                        )
                    }
                    Tag::Cont(ContTag::Error) => {
                        println!("Evaluation encountered an error after {iterations_display}")
                    }
                    _ => println!("Limit reached after {iterations_display}"),
                }
            })
    }

    fn handle_meta(&mut self, expr_ptr: Ptr<F>) -> Result<()> {
        let (car, cdr) = self.store.car_cdr(&expr_ptr)?;
        match &self.store.fetch_sym(&car) {
            Some(symbol) => {
                let cmdstr = symbol.name()?;
                match self.meta.get(cmdstr) {
                    Some(cmd) => match (cmd.run)(self, cmdstr, &cdr) {
                        Ok(()) => (),
                        Err(e) => println!("meta command failed with {}", e),
                    },
                    None => bail!("Unsupported meta command: {cmdstr}"),
                }
            }
            None => bail!(
                "Meta command must be a symbol. Found {}",
                car.fmt_to_string(&self.store, &self.state.borrow())
            ),
        }
        Ok(())
    }

    #[inline]
    fn input_marker(&self) -> String {
        format!(
            "{}> ",
            self.state
                .borrow()
                .fmt_to_string(self.state.borrow().get_current_package_name())
        )
    }

    fn handle_form<'a>(&mut self, input: parser::Span<'a>, demo: bool) -> Result<parser::Span<'a>> {
        let (syntax_start, mut new_input, ptr, is_meta) =
            self.store.read_maybe_meta(self.state.clone(), &input)?;
        if demo {
            let potential_commentaries = &input[..syntax_start];
            let actual_syntax = &input[syntax_start..new_input.location_offset()];
            let input_marker = &self.input_marker();
            if actual_syntax.contains('\n') {
                // print the expression on a new line to avoid messing with the user's formatting
                print!("{potential_commentaries}{input_marker}\n{actual_syntax}");
            } else {
                print!("{potential_commentaries}{input_marker}{actual_syntax}");
            }
            std::io::stdout().flush()?;
            // wait for ENTER to be pressed
            std::io::stdin().read_line(&mut String::new())?;
            // ENTER already prints a new line so we can remove it from the start of incoming input
            new_input = parser::Span::new(new_input.trim_start_matches('\n'));
        }
        if is_meta {
            self.handle_meta(ptr)?;
        } else {
            self.handle_non_meta(ptr)?;
        }
        Ok(new_input)
    }

    pub fn load_file(&mut self, file_path: &Utf8Path, demo: bool) -> Result<()> {
        let input = read_to_string(file_path)?;
        if demo {
            println!("Loading {file_path} in demo mode");
        } else {
            println!("Loading {file_path}");
        }

        let mut input = parser::Span::new(&input);
        loop {
            match self.handle_form(input, demo) {
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
            match editor.readline(&self.input_marker()) {
                Ok(line) => {
                    editor.save_history(history_path)?;
                    match self.store.read_maybe_meta(self.state.clone(), &line) {
                        Ok((.., expr_ptr, is_meta)) => {
                            if is_meta {
                                if let Err(e) = self.handle_meta(expr_ptr) {
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
