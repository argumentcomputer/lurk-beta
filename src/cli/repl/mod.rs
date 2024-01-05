mod meta_cmd;

use abomonation::Abomonation;
use anyhow::{anyhow, bail, Context, Result};
use camino::{Utf8Path, Utf8PathBuf};
use ff::PrimeField;
use nova::traits::Engine;
use rustyline::{
    error::ReadlineError,
    history::DefaultHistory,
    validate::{MatchingBracketValidator, ValidationContext, ValidationResult, Validator},
    Config, Editor,
};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};
use serde::{de::DeserializeOwned, Serialize};
use std::{
    cell::{OnceCell, RefCell},
    collections::HashMap,
    fs::read_to_string,
    io::Write,
    rc::Rc,
    sync::Arc,
};
use tracing::info;

use crate::{
    coprocessor::Coprocessor,
    eval::lang::Lang,
    field::LurkField,
    lem::{
        eval::{
            evaluate_simple_with_env, evaluate_with_env, make_cprocs_funcs_from_lang,
            make_eval_step_from_config, EvalConfig,
        },
        interpreter::Frame,
        multiframe::MultiFrame,
        pointers::{Ptr, RawPtr},
        store::Store,
        tag::Tag,
        Func,
    },
    parser,
    proof::{
        nova::{CurveCycleEquipped, NovaProver},
        Prover, RecursiveSNARKTrait,
    },
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
    paths::{commitment_path, repl_history},
    zstore::ZDag,
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
struct Evaluation {
    frames: Vec<Frame>,
    iterations: usize,
}

impl Evaluation {
    #[inline]
    fn get_result(&self) -> Option<&Ptr> {
        self.frames.last().and_then(|frame| frame.output.first())
    }
}

#[allow(dead_code)]
pub(crate) struct Repl<F: LurkField, C: Coprocessor<F> + Serialize + DeserializeOwned> {
    store: Store<F>,
    state: Rc<RefCell<State>>,
    lang: Arc<Lang<F, C>>,
    lurk_step: Func,
    cprocs: Vec<Func>,
    env: Ptr,
    rc: usize,
    limit: usize,
    backend: Backend,
    evaluation: Option<Evaluation>,
    pwd_path: Utf8PathBuf,
    meta: HashMap<&'static str, MetaCmd<F, C>>,
    apply_fn: OnceCell<Ptr>,
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

impl<F: LurkField, C: Coprocessor<F> + Serialize + DeserializeOwned> Repl<F, C> {
    fn get_evaluation(&self) -> &Option<Evaluation> {
        &self.evaluation
    }

    fn peek1(&self, args: &Ptr) -> Result<Ptr> {
        let (first, rest) = self.store.car_cdr(args)?;
        if !rest.is_nil() {
            bail!("At most one argument is accepted")
        }
        Ok(first)
    }

    fn peek2(&self, args: &Ptr) -> Result<(Ptr, Ptr)> {
        let (first, rest) = self.store.car_cdr(args)?;
        let (second, rest) = self.store.car_cdr(&rest)?;
        if !rest.is_nil() {
            bail!("At most two arguments are accepted")
        }
        Ok((first, second))
    }

    #[inline]
    fn get_string(&self, ptr: &Ptr) -> Result<String> {
        self.store.fetch_string(ptr).ok_or_else(|| {
            anyhow!(
                "Expected string. Got {}",
                ptr.fmt_to_string(&self.store, &self.state.borrow())
            )
        })
    }

    #[inline]
    fn get_symbol(&self, ptr: &Ptr) -> Result<Symbol> {
        self.store.fetch_symbol(ptr).ok_or_else(|| {
            anyhow!(
                "Expected symbol. Got {}",
                ptr.fmt_to_string(&self.store, &self.state.borrow())
            )
        })
    }
}

impl<
        F: CurveCycleEquipped + Serialize + DeserializeOwned,
        C: Coprocessor<F> + Serialize + DeserializeOwned + 'static,
    > Repl<F, C>
where
    <F as PrimeField>::Repr: Abomonation,
    <<<F as CurveCycleEquipped>::E2 as Engine>::Scalar as PrimeField>::Repr: Abomonation,
{
    pub(crate) fn new(
        store: Store<F>,
        lang: Lang<F, C>,
        rc: usize,
        limit: usize,
        backend: Backend,
    ) -> Repl<F, C> {
        let limit = pad(limit, rc);
        info!(
            "Launching REPL with backend {backend}, field {}, rc {rc} and limit {limit}",
            F::FIELD
        );
        let current_dir = std::env::current_dir().expect("couldn't capture current directory");
        let pwd_path =
            Utf8PathBuf::from_path_buf(current_dir).expect("path contains invalid Unicode");
        let env = store.intern_nil();
        let lurk_step = make_eval_step_from_config(&EvalConfig::new_ivc(&lang));
        let cprocs = make_cprocs_funcs_from_lang(&lang);
        Repl {
            store,
            state: State::init_lurk_state().rccell(),
            lang: Arc::new(lang),
            lurk_step,
            cprocs,
            env,
            rc,
            limit,
            backend,
            evaluation: None,
            pwd_path,
            meta: MetaCmd::cmds(),
            apply_fn: OnceCell::new(),
        }
    }

    fn lang_setup(&self) -> (&Func, &[Func], &Lang<F, C>) {
        (&self.lurk_step, &self.cprocs, &self.lang)
    }

    fn get_apply_fn(&self) -> &Ptr {
        self.apply_fn.get_or_init(|| {
            let ptr = self
                .store
                .read_with_default_state(
                    "(letrec ((apply (lambda (fn args)
                         (if args
                           (if (cdr args)
                             (apply (fn (car args)) (cdr args))
                             (fn (car args)))
                           (fn)))))
                       apply)",
                )
                .unwrap();
            let (io, ..) = self
                .eval_expr_with_env(ptr, self.store.intern_nil())
                .unwrap();
            io[0]
        })
    }

    /// Returns a map containing the the key/value pairs from a property list whose
    /// keys are listed on the `properties` slice.
    fn get_properties(&self, list: &Ptr, properties: &[&str]) -> Result<HashMap<String, Ptr>> {
        let (list, None) = self
            .store
            .fetch_list(list)
            .ok_or_else(|| anyhow!("list not interned"))?
        else {
            bail!("property lists must be proper")
        };
        let mut map = HashMap::default();
        for &property in properties {
            let property_ptr = self.store.intern_symbol(&Symbol::key(&[property]));
            if let Some(property_idx) = list.iter().position(|ptr| ptr == &property_ptr) {
                map.insert(property.to_string(), list[property_idx + 1]);
            }
        }
        Ok(map)
    }

    #[allow(dead_code)]
    fn proof_claim(
        store: &Store<F>,
        exprs: (Ptr, Ptr),
        envs: (Ptr, Ptr),
        conts: ((F, F), (F, F)),
    ) -> Ptr {
        let expr_key = store.key("expr");
        let env_key = store.key("env");
        let cont_key = store.key("cont");
        let expr_out_key = store.key("expr-out");
        let env_out_key = store.key("env-out");
        let cont_out_key = store.key("cont-out");
        let (expr, expr_out) = exprs;
        let (env, env_out) = envs;
        let ((cont_tag, cont_val), (cont_out_tag, cont_out_val)) = conts;
        let cont = store.cons(store.num(cont_tag), store.num(cont_val));
        let cont_out = store.cons(store.num(cont_out_tag), store.num(cont_out_val));
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

    /// Proves a computation and returns the proof key
    pub(crate) fn prove_frames(&self, frames: &[Frame], iterations: usize) -> Result<String> {
        match self.backend {
            Backend::Nova => {
                info!("Hydrating the store");
                self.store.hydrate_z_cache();

                let n_frames = frames.len();

                // saving to avoid clones
                let input = &frames[0].input;
                let output = &frames[n_frames - 1].output;
                let mut z_dag = ZDag::<F>::default();
                let mut cache = HashMap::default();
                let expr = z_dag.populate_with(&input[0], &self.store, &mut cache);
                let env = z_dag.populate_with(&input[1], &self.store, &mut cache);
                let cont = z_dag.populate_with(&input[2], &self.store, &mut cache);
                let expr_out = z_dag.populate_with(&output[0], &self.store, &mut cache);
                let env_out = z_dag.populate_with(&output[1], &self.store, &mut cache);
                let cont_out = z_dag.populate_with(&output[2], &self.store, &mut cache);

                let claim = Self::proof_claim(
                    &self.store,
                    (input[0], output[0]),
                    (input[1], output[1]),
                    (cont.parts(), cont_out.parts()),
                );

                let claim_comm = Commitment::new(None, claim, &self.store);
                let claim_hash = &claim_comm.hash.hex_digits();
                let proof_key = Self::proof_key(&self.backend, &self.rc, claim_hash);

                let lurk_proof_meta = LurkProofMeta {
                    iterations,
                    expr_io: (expr, expr_out),
                    env_io: Some((env, env_out)),
                    cont_io: (cont, cont_out),
                    z_dag,
                };

                if LurkProof::<_, _, MultiFrame<'_, _, C>>::is_cached(&proof_key) {
                    info!("Proof already cached");
                } else {
                    info!("Proof not cached. Loading public parameters");
                    let instance =
                        Instance::new(self.rc, self.lang.clone(), true, Kind::NovaPublicParams);
                    let pp = public_params(&instance)?;

                    let prover =
                        NovaProver::<_, _, MultiFrame<'_, F, C>>::new(self.rc, self.lang.clone());

                    info!("Proving");
                    let (proof, public_inputs, public_outputs, num_steps) =
                        prover.prove(&pp, frames, &self.store)?;
                    info!("Compressing proof");
                    let proof = proof.compress(&pp)?;
                    assert_eq!(self.rc * num_steps, pad(n_frames, self.rc));
                    assert!(proof.verify(&pp, &public_inputs, &public_outputs)?);

                    let lurk_proof = LurkProof::Nova {
                        proof,
                        public_inputs,
                        public_outputs,
                        rc: self.rc,
                        lang: (*self.lang).clone(),
                    };

                    lurk_proof.persist(&proof_key)?;
                }
                lurk_proof_meta.persist(&proof_key)?;
                claim_comm.persist()?;
                println!("Claim hash: 0x{claim_hash}");
                println!("Proof key: \"{proof_key}\"");
                Ok(proof_key)
            }
        }
    }

    /// Proves the last cached computation and returns the proof key
    pub(crate) fn prove_last_frames(&self) -> Result<String> {
        match self.evaluation.as_ref() {
            None => bail!("No evaluation to prove"),
            Some(Evaluation { frames, iterations }) => self.prove_frames(frames, *iterations),
        }
    }

    fn hide(&mut self, secret: F, payload: Ptr) -> Result<()> {
        let commitment = Commitment::new(Some(secret), payload, &self.store);
        let hash_str = &commitment.hash.hex_digits();
        commitment.persist()?;
        println!("Hash: 0x{hash_str}");
        Ok(())
    }

    fn fetch(&mut self, hash: &F, print_data: bool) -> Result<()> {
        let commitment: Commitment<F> = load(&commitment_path(&hash.hex_digits()))?;
        if &commitment.hash != hash {
            bail!("Hash mismatch. Corrupted commitment file.")
        } else {
            let (secret, z_payload) = commitment.open()?;
            let payload = commitment.z_store.populate_store(
                z_payload,
                &self.store,
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

    fn eval_expr_with_env(&self, expr: Ptr, env: Ptr) -> Result<(Vec<Ptr>, usize, Vec<Ptr>)> {
        let (ptrs, iterations, emitted) = evaluate_simple_with_env::<F, C>(
            Some(self.lang_setup()),
            expr,
            env,
            &self.store,
            self.limit,
        )?;
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

    #[inline]
    fn eval_expr(&self, expr: Ptr) -> Result<(Vec<Ptr>, usize, Vec<Ptr>)> {
        self.eval_expr_with_env(expr, self.env)
    }

    fn eval_expr_allowing_error_continuation(
        &mut self,
        expr_ptr: Ptr,
    ) -> Result<(Vec<Ptr>, usize, Vec<Ptr>)> {
        let (ptrs, iterations, emitted) = evaluate_simple_with_env::<F, C>(
            Some(self.lang_setup()),
            expr_ptr,
            self.env,
            &self.store,
            self.limit,
        )?;
        if matches!(ptrs[2].tag(), Tag::Cont(ContTag::Terminal | ContTag::Error)) {
            Ok((ptrs, iterations, emitted))
        } else {
            bail!(
                "Limit reached after {}",
                Self::pretty_iterations_display(iterations)
            )
        }
    }

    fn eval_expr_and_memoize(&mut self, expr_ptr: Ptr) -> Result<(Vec<Ptr>, usize)> {
        let frames = evaluate_with_env::<F, C>(
            Some(self.lang_setup()),
            expr_ptr,
            self.env,
            &self.store,
            self.limit,
        )?;
        let iterations = frames.len();
        let output = frames
            .last()
            .expect("evaluation should return at least one frame")
            .output
            .clone();
        self.evaluation = Some(Evaluation { frames, iterations });
        Ok((output, iterations))
    }

    fn get_comm_hash(&mut self, args: &Ptr) -> Result<&F> {
        let first = self.peek1(args)?;
        let num = self.store.intern_lurk_symbol("num");
        let expr = self.store.list(vec![num, first]);
        let (expr_io, ..) = self
            .eval_expr(expr)
            .with_context(|| "evaluating first arg")?;
        let (Tag::Expr(ExprTag::Num), RawPtr::Atom(hash_idx)) = &expr_io[0].parts() else {
            bail!("hash must be a number")
        };
        Ok(self.store.expect_f(*hash_idx))
    }

    pub(crate) fn handle_non_meta(&mut self, expr_ptr: Ptr) -> Result<()> {
        let (output, iterations) = self.eval_expr_and_memoize(expr_ptr)?;
        let iterations_display = Self::pretty_iterations_display(iterations);
        match output[2].tag() {
            Tag::Cont(ContTag::Terminal) => {
                println!(
                    "[{iterations_display}] => {}",
                    output[0].fmt_to_string(&self.store, &self.state.borrow())
                );
                Ok(())
            }
            Tag::Cont(ContTag::Error) => {
                bail!("Evaluation encountered an error after {iterations_display}")
            }
            _ => bail!("Limit reached after {iterations_display}"),
        }
    }

    fn handle_meta(&mut self, expr_ptr: Ptr) -> Result<()> {
        let (car, cdr) = self.store.car_cdr(&expr_ptr)?;
        match &self.store.fetch_sym(&car) {
            Some(symbol) => {
                let cmdstr = symbol.name()?;
                match self.meta.get(cmdstr) {
                    Some(cmd) => match (cmd.run)(self, &cdr) {
                        Ok(()) => (),
                        Err(e) => bail!("Meta command failed with: {}", e),
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
            // adjustment to print the exclamation mark in the right place
            let syntax_start = syntax_start - usize::from(is_meta);
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

    pub(crate) fn load_file(&mut self, file_path: &Utf8Path, demo: bool) -> Result<()> {
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

        let history_path = &repl_history();

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
                                    eprintln!("!Error: {e}")
                                }
                            } else if let Err(e) = self.handle_non_meta(expr_ptr) {
                                eprintln!("Error: {e}")
                            }
                        }
                        Err(parser::Error::NoInput) => (),
                        Err(e) => eprintln!("Read error: {e}"),
                    }
                }
                Err(ReadlineError::Interrupted | ReadlineError::Eof) => {
                    println!("Exiting...");
                    break;
                }
                Err(e) => {
                    eprintln!("Read line error: {e}");
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
