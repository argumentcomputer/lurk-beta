use ::nova::supernova::StepCircuit;
use abomonation::Abomonation;
use anyhow::{anyhow, bail, Context, Result};
use camino::{Utf8Path, Utf8PathBuf};
use ff::PrimeField;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::{collections::HashMap, process};

use crate::{
    cli::{
        backend::Backend,
        field_data::{dump, load, HasFieldModulus},
        lurk_proof::{LurkProof, LurkProofMeta, LurkProofWrapper},
        paths::proof_path,
        zstore::ZDag,
    },
    coprocessor::Coprocessor,
    field::LurkField,
    lem::{
        eval::evaluate_with_env_and_cont,
        pointers::{Ptr, RawPtr, ZPtr},
        store::expect_ptrs,
        tag::Tag,
    },
    package::{Package, SymbolRef},
    proof::{
        nova::{self, CurveCycleEquipped, Dual, C1LEM},
        supernova, RecursiveSNARKTrait,
    },
    public_parameters::{
        instance::{Instance, Kind},
        public_params, supernova_public_params,
    },
    tag::{ContTag, ExprTag},
};

use super::Repl;

pub(super) struct MetaCmd<F: LurkField, C: Coprocessor<F> + Serialize + DeserializeOwned> {
    name: &'static str,
    summary: &'static str,
    format: &'static str,
    description: &'static [&'static str],
    example: &'static [&'static str],
    pub(super) run: fn(repl: &mut Repl<F, C>, args: &Ptr, file_path: &Utf8Path) -> Result<()>,
}

impl<
        'a,
        F: CurveCycleEquipped + Serialize + DeserializeOwned,
        C: Coprocessor<F> + Serialize + DeserializeOwned + 'static,
    > MetaCmd<F, C>
where
    F::Repr: Abomonation,
    <Dual<F> as PrimeField>::Repr: Abomonation,
{
    const LOAD: MetaCmd<F, C> = MetaCmd {
        name: "load",
        summary: "Load lurk expressions from a file.",
        format: "!(load <string>)",
        description: &[],
        example: &["!(load \"my_file.lurk\")"],
        run: |repl, args, path| {
            let first = repl.peek1(args)?;
            if let Some(load_path) = repl.store.fetch_string(&first) {
                repl.load_file(&path.join(load_path), false)
            } else {
                bail!("Argument of `load` must be a string.")
            }
        },
    };

    const DEF: MetaCmd<F, C> = MetaCmd {
        name: "def",
        summary: "Extends env with a non-recursive binding.",
        format: "!(def <binding> <body>)",
        description: &[
            "Gets macroexpanded to this: (let ((foo (lambda () 123))) (current-env))",
            "The state's env is set to the result.",
        ],
        example: &["!(def foo (lambda () 123))"],
        run: |repl, args, _path| {
            let (first, second) = repl.peek2(args)?;
            let new_name = first.fmt_to_string(&repl.store, &repl.state.borrow());
            let l = repl.store.intern_lurk_symbol("let");
            let current_env = repl.store.intern_lurk_symbol("current-env");
            let binding = repl.store.list(vec![first, second]);
            let bindings = repl.store.list(vec![binding]);
            let current_env_call = repl.store.list(vec![current_env]);
            let expanded = repl.store.list(vec![l, bindings, current_env_call]);
            let (expanded_io, ..) = repl.eval_expr(expanded)?;
            repl.env = expanded_io[0];
            println!("{new_name}");
            Ok(())
        },
    };

    const DEFREC: MetaCmd<F, C> = MetaCmd {
        name: "defrec",
        summary: "Extends the env with a recursive binding.",
        format: "!(defrec <binding> <body>)",
        description: &[
            "Gets macroexpanded to this: (letrec ((foo (lambda () 123))) (current-env))",
            "The state's env is set to the result.",
        ],
        example: &[
            "!(defrec sum (lambda (l) (if (eq l nil) 0 (+ (car l) (sum (cdr l))))))",
            "(sum '(1 2 3))",
        ],
        run: |repl, args, _path| {
            let (first, second) = repl.peek2(args)?;
            let new_name = first.fmt_to_string(&repl.store, &repl.state.borrow());
            let l = repl.store.intern_lurk_symbol("letrec");
            let current_env = repl.store.intern_lurk_symbol("current-env");
            let binding = repl.store.list(vec![first, second]);
            let bindings = repl.store.list(vec![binding]);
            let current_env_call = repl.store.list(vec![current_env]);
            let expanded = repl.store.list(vec![l, bindings, current_env_call]);
            let (expanded_io, ..) = repl.eval_expr(expanded)?;
            repl.env = expanded_io[0];
            println!("{new_name}");
            Ok(())
        },
    };

    const ASSERT: MetaCmd<F, C> = MetaCmd {
        name: "assert",
        summary: "Assert that an expression evaluates to true.",
        format: "!(assert <expr>)",
        description: &[],
        example: &["!(assert t)", "!(assert (eq 3 (+ 1 2)))"],
        run: |repl, args, _path| {
            let first = repl.peek1(args)?;
            let (first_io, ..) = repl.eval_expr(first)?;
            if first_io[0].is_nil() {
                eprintln!(
                    "`assert` failed. {} evaluates to nil",
                    first.fmt_to_string(&repl.store, &repl.state.borrow())
                );
                process::exit(1);
            }
            Ok(())
        },
    };

    const ASSERT_EQ: MetaCmd<F, C> = MetaCmd {
        name: "assert-eq",
        summary: "Assert that two expressions evaluate to the same value.",
        format: "!(assert-eq <expr> <expr>)",
        description: &[],
        example: &["!(assert-eq 3 (+ 1 2))"],
        run: |repl, args, _path| {
            let (first, second) = repl.peek2(args)?;
            let (first_io, ..) = repl
                .eval_expr(first)
                .with_context(|| "evaluating first arg")?;
            let (second_io, ..) = repl
                .eval_expr(second)
                .with_context(|| "evaluating second arg")?;
            let (first_io_expr, second_io_expr) = (&first_io[0], &second_io[0]);
            if !repl.store.ptr_eq(first_io_expr, second_io_expr) {
                eprintln!(
                    "`assert-eq` failed. Expected:\n  {} = {}\nGot:\n  {} ≠ {}",
                    first.fmt_to_string(&repl.store, &repl.state.borrow()),
                    second.fmt_to_string(&repl.store, &repl.state.borrow()),
                    first_io_expr.fmt_to_string(&repl.store, &repl.state.borrow()),
                    second_io_expr.fmt_to_string(&repl.store, &repl.state.borrow())
                );
                process::exit(1);
            }
            Ok(())
        },
    };

    const ASSERT_EMITTED: MetaCmd<F, C> = MetaCmd {
        name:
            "assert-emitted",
        summary:
            "Assert that the evaluation of an expr emits values",
        format:
            "!(assert-emitted <expr> <expr>)",
        description: &[
            "Assert that the list of values in the first <expr> are emitted by the validation of the second <expr>.",
        ],
        example: &[
            "!(assert-emitted '(1 2) (begin (emit 1) (emit 2)))"
        ],
        run: |repl, args, _path| {
            let (first, second) = repl.peek2(args)?;
            let (first_io, ..) = repl
                .eval_expr(first)
                .with_context(|| "evaluating first arg")?;
            let (.., emitted) = repl
                .eval_expr(second)
                .with_context(|| "evaluating second arg")?;
            let (mut first_emitted, mut rest_emitted) = repl.store.car_cdr(&first_io[0])?;
            for (i, elem) in emitted.iter().enumerate() {
                if elem != &first_emitted {
                    eprintln!(
                        "`assert-emitted` failed at position {i}. Expected {}, but found {}.",
                        first_emitted.fmt_to_string(&repl.store, &repl.state.borrow()),
                        elem.fmt_to_string(&repl.store, &repl.state.borrow()),
                    );
                    process::exit(1);
                }
                (first_emitted, rest_emitted) = repl.store.car_cdr(&rest_emitted)?;
            }
            Ok(())
        },
    };

    const ASSERT_ERROR: MetaCmd<F, C> = MetaCmd {
        name: "assert-error",
        summary: "Assert that a evaluation of <expr> fails.",
        format: "!(assert-error <expr>)",
        description: &[],
        example: &["!(assert-error (1 1))"],
        run: |repl, args, _path| {
            let first = repl.peek1(args)?;
            let (first_io, ..) = repl.eval_expr_allowing_error_continuation(first)?;
            if first_io[2].tag() != &Tag::Cont(ContTag::Error) {
                eprintln!(
                    "`assert-error` failed. {} doesn't result on evaluation error.",
                    first.fmt_to_string(&repl.store, &repl.state.borrow())
                );
                process::exit(1);
            }
            Ok(())
        },
    };

    const COMMIT: MetaCmd<F, C> = MetaCmd {
        name:
            "commit",
        summary:
            "Compute the commitment of <expr>.",
        format:
            "!(commit <expr>)",
        description: &[],
        example: &[
            "!(commit '(13 . 21))",
            "(let ((n (open 0x178217493faea2931df4e333837ba9312d0bb9f59bb787c1f40fd3af6d845001))) (* (car n) (cdr n)))",
        ],
        run: |repl, args, _path| {
            let first = repl.peek1(args)?;
            let (first_io, ..) = repl.eval_expr(first)?;
            repl.hide(F::NON_HIDING_COMMITMENT_SECRET, first_io[0])
        }
    };

    const HIDE: MetaCmd<F, C> = MetaCmd {
        name: "hide",
        summary: "Return and persist the commitment of <exp> using secret <secret>.",
        format: "!(hide <secret> <expr>)",
        description: &[],
        example: &[
            "!(hide 12345 '(13 . 21))",
            "(secret (comm 0x1884a703eea837ffae6ae99ec9af8e90d3fce7666c7953ffbe5eac7463ed1819))",
            "(open 0x1884a703eea837ffae6ae99ec9af8e90d3fce7666c7953ffbe5eac7463ed1819)",
        ],
        run: |repl, args, _path| {
            let (first, second) = repl.peek2(args)?;
            let (first_io, ..) = repl
                .eval_expr(first)
                .with_context(|| "evaluating first arg")?;
            let (second_io, ..) = repl
                .eval_expr(second)
                .with_context(|| "evaluating second arg")?;
            let (Tag::Expr(ExprTag::Num), RawPtr::Atom(secret)) = first_io[0].parts() else {
                bail!(
                    "Secret must be a number. Got {}",
                    first_io[0].fmt_to_string(&repl.store, &repl.state.borrow())
                )
            };
            let secret = *repl.store.expect_f(*secret);
            repl.hide(secret, second_io[0])?;
            Ok(())
        },
    };

    const FETCH: MetaCmd<F, C> = MetaCmd {
        name: "fetch",
        summary: "Add data from a commitment to the repl store.",
        format: "!(fetch <commitment>)",
        description: &[],
        example: &[
            "!(commit '(13 . 21))",
            "!(fetch 0x178217493faea2931df4e333837ba9312d0bb9f59bb787c1f40fd3af6d845001)",
        ],
        run: |repl, args, _path| {
            let hash_expr = repl.peek1(args)?;
            let hash = *repl.get_comm_hash(hash_expr)?;
            repl.fetch(&hash, false)
        },
    };

    const OPEN: MetaCmd<F, C> = MetaCmd {
        name: "open",
        summary: "Open a commitment.",
        format: "!(open <commitment>)",
        description: &[],
        example: &[
            "!(commit '(13 . 21))",
            "!(open 0x178217493faea2931df4e333837ba9312d0bb9f59bb787c1f40fd3af6d845001)",
        ],
        run: |repl, args, _path| {
            let hash_expr = repl.peek1(args)?;
            let hash = *repl.get_comm_hash(hash_expr)?;
            repl.fetch(&hash, true)
        },
    };

    const CLEAR: MetaCmd<F, C> = MetaCmd {
        name: "clear",
        summary: "Reset the current environment to be empty.",
        format: "!(clear)",
        description: &[],
        example: &["!(def a 1)", "(current-env)", "!(clear)", "(current-env)"],
        run: |repl, _args, _path| {
            repl.env = repl.store.intern_empty_env();
            Ok(())
        },
    };

    const SET_ENV: MetaCmd<F, C> = MetaCmd {
        name: "set-env",
        summary: "Set the env to the result of evaluating the first argument.",
        format: "!(set-env <expr>)",
        description: &[],
        example: &["!(set-env '((a . 1) (b . 2)))", "a"],
        run: |repl, args, _path| {
            let first = repl.peek1(args)?;
            let (first_io, ..) = repl.eval_expr(first)?;
            let env = first_io[0];
            if *env.tag() != Tag::Expr(ExprTag::Env) {
                return Err(anyhow!("Value must be an environment"));
            }
            repl.env = env;
            Ok(())
        },
    };

    const PROVE: MetaCmd<F, C> = MetaCmd {
        name:
            "prove",
        summary:
            "Evaluate and prove <expr>",
        format:
            "!(prove <expr>)",
        description: &[
            "Persist the proof and prints the proof id.",
        ],
        example: &[
            "!(prove '(1 2 3))",
            "!(verify \"supernova_bn256_10_048476fa5e4804639fe4ccfe73d43bf96da6183f670f0b08e4ac8c82bf8efa47\")",
            "!(open 0x048476fa5e4804639fe4ccfe73d43bf96da6183f670f0b08e4ac8c82bf8efa47)",
        ],
        run: |repl, args, _path| {
            if !args.is_nil() {
                repl.eval_expr_and_memoize(repl.peek1(args)?)?;
            }
            repl.prove_last_frames()?;
            Ok(())
        }
    };

    const VERIFY: MetaCmd<F, C> = MetaCmd {
        name: "verify",
        summary: "Verify a proof",
        format: "!(verify <string>)",
        description: &["Verify proof key <string> and print the result."],
        example: &[
            "!(prove '(1 2 3))",
            "!(verify \"supernova_bn256_10_048476fa5e4804639fe4ccfe73d43bf96da6183f670f0b08e4ac8c82bf8efa47\")",
            "!(open 0x048476fa5e4804639fe4ccfe73d43bf96da6183f670f0b08e4ac8c82bf8efa47)",
        ],
        run: |repl, args, _path| {
            let first = repl.peek1(args)?;
            let proof_id = repl.get_string(&first)?;
            LurkProof::<_, C>::verify_proof(
                &proof_id,
            )
        }
    };

    const DEFPACKAGE: MetaCmd<F, C> = MetaCmd {
        name: "defpackage",
        summary: "Add a package to the state.",
        format: "!(defpackage <string|symbol>)",
        description: &[],
        example: &["!(defpackage abc)"],
        run: |repl, args, _path| {
            // TODO: handle args
            let (name, _args) = repl.store.car_cdr(args)?;
            let name = match name.tag() {
                Tag::Expr(ExprTag::Str) => repl.state.borrow_mut().intern(repl.get_string(&name)?),
                Tag::Expr(ExprTag::Sym) => repl.get_symbol(&name)?.into(),
                _ => bail!("Package name must be a string or a symbol"),
            };
            println!("{}", repl.state.borrow().fmt_to_string(&name));
            let package = Package::new(name);
            repl.state.borrow_mut().add_package(package);
            Ok(())
        },
    };

    const IMPORT: MetaCmd<F, C> = MetaCmd {
        name: "import",
        summary: "Import a single or several packages.",
        format: "!(import <string|package> ...)",
        description: &[],
        example: &[],
        run: |repl, args, _path| {
            // TODO: handle pkg
            let (mut symbols, _pkg) = repl.store.car_cdr(args)?;
            if symbols.tag() == &Tag::Expr(ExprTag::Sym) {
                let sym = SymbolRef::new(repl.get_symbol(&symbols)?);
                repl.state.borrow_mut().import(&[sym])?;
            } else {
                let mut symbols_vec = vec![];
                loop {
                    {
                        let (head, tail) = repl.store.car_cdr(&symbols)?;
                        let sym = repl.get_symbol(&head)?;
                        symbols_vec.push(SymbolRef::new(sym));
                        if tail.is_nil() {
                            break;
                        }
                        symbols = tail;
                    }
                }
                repl.state.borrow_mut().import(&symbols_vec)?;
            }
            Ok(())
        },
    };

    const IN_PACKAGE: MetaCmd<F, C> = MetaCmd {
        name: "in-package",
        summary: "set the current package.",
        format: "!(in-package <string|symbol>)",
        description: &[],
        example: &[
            "!(defpackage abc)",
            "!(in-package abc)",
            "!(def two (.lurk.+ 1 1))",
            "!(in-package .lurk.user)",
            "(.lurk.user.abc.two)",
        ],
        run: |repl, args, _path| {
            let first = repl.peek1(args)?;
            match first.tag() {
                Tag::Expr(ExprTag::Str) => {
                    let name = repl.get_string(&first)?;
                    let package_name = repl.state.borrow_mut().intern(name);
                    repl.state.borrow_mut().set_current_package(package_name)
                }
                Tag::Expr(ExprTag::Sym) => {
                    let package_name = repl.get_symbol(&first)?;
                    repl.state
                        .borrow_mut()
                        .set_current_package(package_name.into())
                }
                _ => bail!(
                    "Expected string or symbol. Got {}",
                    first.fmt_to_string(&repl.store, &repl.state.borrow())
                ),
            }
        },
    };

    const HELP: MetaCmd<F, C> = MetaCmd {
        name: "help",
        summary: "Print help message.",
        format: "!(help <string|symbol>)",
        description: &[
            "Without arguments it prints a summary of all available commands.",
            "Otherwise the full help for the command in the first argument is printed.",
        ],
        example: &["!(help)", "!(help verify)", "!(help \"load\")"],
        run: |repl, args, _path| {
            let first = repl.peek1(args)?;
            match first.tag() {
                Tag::Expr(ExprTag::Str) => {
                    let name = repl.get_string(&first)?;
                    Self::meta_help(&name);
                }
                Tag::Expr(ExprTag::Sym) => {
                    let sym = repl.get_symbol(&first)?;
                    let name = sym.path().last().unwrap();
                    Self::meta_help(name);
                }
                Tag::Expr(ExprTag::Nil) => {
                    use itertools::Itertools;
                    println!("Available commands:");
                    for (_, i) in MetaCmd::<F, C>::cmds().iter().sorted_by_key(|x| x.0) {
                        println!("  {} - {}", i.name, i.summary);
                    }
                }
                _ => bail!("The optional argument of `help` must be a string or symbol"),
            }
            Ok(())
        },
    };

    fn meta_help(cmd: &str) {
        match MetaCmd::<F, C>::cmds().get(cmd) {
            Some(i) => {
                println!("{} - {}", i.name, i.summary);
                for &e in i.description.iter() {
                    println!("  {}", e);
                }
                println!("  Usage: {}", i.format);
                if !i.example.is_empty() {
                    println!("  Example:");
                }
                for &e in i.example.iter() {
                    println!("    {}", e);
                }
            }
            None => println!("unknown command {}", cmd),
        }
    }

    fn call(repl: &mut Repl<F, C>, args: &Ptr, _path: &Utf8Path) -> Result<()> {
        let (hash_expr, args) = repl.store.car_cdr(args)?;
        let hash = *repl.get_comm_hash(hash_expr)?;
        // check if the data is already available on the store before trying to
        // fetch it from the file system
        if repl.store.open(hash).is_none() {
            repl.fetch(&hash, false)?;
        }
        let open = repl.store.intern_lurk_symbol("open");
        let open_expr = repl.store.list(vec![open, repl.store.num(hash)]);
        let (args_vec, _) = repl
            .store
            .fetch_list(&args)
            .expect("list of arguments must have been interned");
        let mut expr_vec = Vec::with_capacity(args_vec.len() + 1);
        expr_vec.push(open_expr);
        expr_vec.extend(args_vec);
        repl.handle_non_meta(repl.store.list(expr_vec))
    }

    const CALL: MetaCmd<F, C> = MetaCmd {
        name: "call",
        summary: "Open a functional commitment then apply arguments to it",
        format: "!(call <hash> <args>)",
        description: &[],
        example: &[
            "(commit (lambda (x) x))",
            "!(call 0x2f31ee658b82c09daebbd2bd976c9d6669ad3bd6065056763797d5aaf4a3001b 0)",
        ],
        run: Self::call,
    };

    const CHAIN: MetaCmd<F, C> = MetaCmd {
        name: "chain",
        summary: "Chain a functional commitment by applying the provided arguments to it",
        format: "!(chain <hash> <args>)",
        description: &[
            "Chain a functional commitment by applying the provided arguments to it.",
            "The chained function must return a pair whose first component is the actual result",
            "  and the second is a commitment to the next function",
        ],
        example: &[
            "!(commit (letrec ((add (lambda (counter x)
                       (let ((counter (+ counter x)))
                         (cons counter (commit (add counter)))))))
               (add 0)))",
            "!(chain 0x2b444b40b27bac0dff8416c0f3c708a505a636d86ba66bdbe86497c515afb651 1)",
        ],
        run: |repl, args, path| {
            Self::call(repl, args, path)?;
            let ev = repl
                .get_evaluation()
                .as_ref()
                .expect("evaluation must have been set");
            let result = ev
                .get_result()
                .expect("evaluation result must have been set");
            let (_, comm) = repl.store.car_cdr(result)?;
            let (Tag::Expr(ExprTag::Comm), RawPtr::Atom(hash)) = comm.parts() else {
                bail!("Second component of a chain must be a commitment")
            };
            let hash = *repl.store.expect_f(*hash);
            // retrieve from store to persist
            let (secret, fun) = repl
                .store
                .open(hash)
                .expect("data must have been committed");
            repl.hide(*secret, *fun)
        },
    };

    fn inspect(repl: &mut Repl<F, C>, args: &Ptr, full: bool) -> Result<()> {
        let first = repl.peek1(args)?;
        let proof_id = repl.get_string(&first)?;
        LurkProofMeta::<F>::inspect_proof(
            &proof_id,
            Some((&repl.store, &repl.state.borrow())),
            full,
        )
    }

    const INSPECT: MetaCmd<F, C> = MetaCmd {
        name: "inspect",
        summary: "Print part of a proof claim",
        format: "!(inspect <string>)",
        description: &[],
        example: &[
            "!(prove '(1 2 3))",
            "!(inspect \"supernova_bn256_10_048476fa5e4804639fe4ccfe73d43bf96da6183f670f0b08e4ac8c82bf8efa47\")",
        ],
        run: |repl, args, _path| {
            Self::inspect(repl, args, false)
        }
    };

    const INSPECT_FULL: MetaCmd<F, C> = MetaCmd {
        name: "inspect-full",
        summary: "Print a proof claim",
        format: "!(inspect-full <string>)",
        description: &[],
        example: &[
            "!(prove '(1 2 3))",
            "!(inspect-full \"supernova_bn256_10_048476fa5e4804639fe4ccfe73d43bf96da6183f670f0b08e4ac8c82bf8efa47\")",
        ],
        run: |repl, args, _path| {
            Self::inspect(repl, args, true)
        }
    };

    const DUMP_DATA: MetaCmd<F, C> = MetaCmd {
        name: "dump-data",
        summary: "Write Lurk data to the file system",
        format: "!(dump-data <expr> <string>)",
        description: &[],
        example: &["!(dump-data (+ 1 1) \"my_file\")"],
        run: |repl, args, _path| {
            let (expr, path) = repl.peek2(args)?;
            let path = get_path(repl, &path)?;
            let (io, ..) = repl
                .eval_expr(expr)
                .with_context(|| "evaluating predicate")?;
            let mut z_dag = ZDag::default();
            let z_ptr = z_dag.populate_with(&io[0], &repl.store, &mut Default::default());
            dump(LurkData { z_ptr, z_dag }, &path)
        },
    };

    const DEF_LOAD_DATA: MetaCmd<F, C> = MetaCmd {
        name: "def-load-data",
        summary: "Read Lurk data from the file system and bind it to a symbol",
        format: "!(def-load-data <symbol> <string>)",
        description: &[],
        example: &["!(def-load-data x \"my_file\")"],
        run: |repl, args, _path| {
            let (sym, path) = repl.peek2(args)?;
            if !sym.is_sym() {
                bail!(
                    "Bound variable must be a symbol. Got {}",
                    sym.fmt_to_string(&repl.store, &repl.state.borrow())
                )
            }
            let path = get_path(repl, &path)?;
            let LurkData::<F> { z_ptr, z_dag } = load(&path)?;
            let ptr = z_dag.populate_store(&z_ptr, &repl.store, &mut Default::default())?;
            repl.env = repl.store.push_binding(sym, ptr, repl.env);
            Ok(())
        },
    };

    const DEFPROTOCOL: MetaCmd<F, C> = MetaCmd {
        name: "defprotocol",
        summary: "Defines a protocol",
        format: "!(defprotocol <symbol> <vars> <body> options...)",
        description: &[
            "The protocol body cannot have any free variable besides the ones",
            "  declared in the vars list. The body must return a pair such that:",
            "* The first component is a list containing the CEK inputs that the",
            "  proof must accept. This list has 6 elements and follows the order",
            "  (expr-in env-in cont-in expr-out env-out cont-out).",
            "  The protocol can reject the proof by returning nil instead.",
            "* The second component is a 0-arg predicate that will run after the",
            "  proof verification to further constrain the proof, if needed.",
            "  If this is not necessary, this component can simply be nil.",
            "",
            "defprotocol accepts the following options:",
            "  :backend can be \"nova\" or \"supernova\", defaulting to the REPL's config",
            "  :rc is the reduction count, defaulting to the REPL's one",
            "  :lang defines the Lang (ignored for now)",
            "  :description is a description of the protocol, defaulting to \"\""
        ],
        example: &[
            "!(defprotocol my-protocol (hash pair)",
            "  (let ((list6 (lambda (a b c d e f) (cons a (cons b (cons c (cons d (cons e (cons f nil))))))))",
            "        (mk-open-expr (lambda (hash) (cons 'open (cons hash nil)))))",
            "    (cons",
            "      (if (= (+ (car pair) (cdr pair)) 30)",
            "        (list6 (mk-open-expr hash) (empty-env) :outermost pair (empty-env) :terminal)",
            "        nil)",
            "      (lambda () (> (car pair) 10))))",
            "  :backend \"supernova\"",
            "  :rc 10",
            "  :description \"example protocol\")",
        ],
        run: |repl, args, _path| {
            let (name, rest) = repl.store.car_cdr(args)?;
            let (vars, rest) = repl.store.car_cdr(&rest)?;
            let (body, props) = repl.store.car_cdr(&rest)?;
            if !name.is_sym() {
                bail!(
                    "Protocol name must be a symbol. Got {}",
                    name.fmt_to_string(&repl.store, &repl.state.borrow())
                )
            }
            if !vars.is_list() {
                bail!(
                    "Protocol vars must be a list. Got {}",
                    vars.fmt_to_string(&repl.store, &repl.state.borrow())
                )
            }

            let lambda = repl.store.list(vec![repl.store.intern_lurk_symbol("lambda"), vars, body]);
            let (io, ..) = repl.eval_expr_with_env(lambda, repl.store.intern_empty_env())?;
            let fun = io[0];
            if !fun.is_fun() {
                bail!(
                    "Protocol definition failed to evaluate to a function. Got {}",
                    fun.fmt_to_string(&repl.store, &repl.state.borrow())
                )
            }

            let prop_map = repl.get_properties(&props, &["backend", "rc", "lang", "description"])?;

            let get_prop = |key, accepts: fn(&Repl<F, C>, &Ptr) -> bool, def: fn(&Repl<F, C>) -> Ptr| -> Result<Ptr> {
                match prop_map.get(key) {
                    Some(val) => {
                        if accepts(repl, val) {
                            Ok(*val)
                        } else {
                            bail!("Invalid value for {key}")
                        }
                    }
                    None => Ok(def(repl)),
                }
            };

            let backend = get_prop(
                "backend",
                |repl, ptr| {
                    let backend_str = repl.store.fetch_string(ptr);
                    backend_str == Some("nova".to_string()) || backend_str == Some("supernova".to_string())
                },
                |repl| repl.store.intern_string(&repl.backend.to_string())
            )?;

            let rc = get_prop(
                "rc",
                |_, ptr| ptr.is_num(),
                |repl| repl.store.num_u64(repl.rc.try_into().unwrap())
            )?;

            // TODO: handle lang properly
            let lang = get_prop(
                "lang",
                |_, _| true, // accept anything for now
                |repl| repl.store.intern_nil()
            )?;

            let description = get_prop(
                "description",
                |_, ptr| ptr.is_str(),
                |repl| repl.store.intern_string("")
            )?;

            // the standard format for a processed protocol as Lurk data
            let protocol = repl.store.list(vec![fun, backend, rc, lang, description]);
            repl.env = repl.store.push_binding(name, protocol, repl.env);
            Ok(())
        },
    };

    /// Returns the protocol function, the backend and reduction count
    ///
    /// # Errors
    /// * If the protocol evaluation fails
    /// * If the backend is not a string or has invalid value
    /// * If the reduction count is not a number or can't be converted to `u64`
    fn get_fun_backend_and_rc(repl: &Repl<F, C>, ptcl: Ptr) -> Result<(Ptr, Backend, usize)> {
        let (io, ..) = repl
            .eval_expr(ptcl)
            .with_context(|| "evaluating protocol")?;
        let ptcl = &io[0];

        let (fun, rest) = repl.store.car_cdr(ptcl)?;

        let (car, rest) = repl.store.car_cdr(&rest)?;
        let Some(backend) = repl.store.fetch_string(&car) else {
            bail!("Backend must be a string")
        };
        let backend = match backend.as_str() {
            "nova" => Backend::Nova,
            "supernova" => Backend::SuperNova,
            _ => bail!("Invalid value for backend"),
        };

        let (car, _) = repl.store.car_cdr(&rest)?;
        let (Tag::Expr(ExprTag::Num), RawPtr::Atom(rc_idx)) = car.parts() else {
            bail!("Reduction count must be a Num")
        };
        let Some(rc) = repl.store.expect_f(*rc_idx).to_u64().map(|u| u as usize) else {
            bail!("Invalid value for reduction count")
        };
        Ok((fun, backend, rc))
    }

    /// Returns a vector containing the elements of a list.
    ///
    /// # Errors
    /// Errors if the the list of arguments is not proper
    fn get_args_vec(repl: &Repl<F, C>, args: &Ptr) -> Result<Vec<Ptr>> {
        let Some((args_vec, None)) = repl.store.fetch_list(args) else {
            bail!("Protocol arguments must be a list")
        };

        Ok(args_vec)
    }

    /// Runs the protocol `body` with an environment built from the bindings
    /// created with `vars` and `args` and returns the proof input and the
    /// post-verify function.
    ///
    /// # Errors
    /// * If the protocol function call evaluation fails
    /// * If the protocol function call doesn't evaluate to a pair
    /// * If the proof input can't be built (first component of the pair is nil)
    /// * If the proof input is not a list with length 6
    fn get_cek_io_and_post_verify_fn(
        repl: &Repl<F, C>,
        fun: Ptr,
        args: Ptr,
    ) -> Result<(Vec<Ptr>, Ptr)> {
        let quoted_args = repl
            .store
            .list(vec![repl.store.intern_lurk_symbol("quote"), args]);
        let apply_call = repl
            .store
            .list(vec![*repl.get_apply_fn(), fun, quoted_args]);

        let (io, ..) = repl
            .eval_expr_with_env(apply_call, repl.store.intern_empty_env())
            .with_context(|| "evaluating protocol function call")?;

        let (Tag::Expr(ExprTag::Cons), RawPtr::Hash4(idx)) = &io[0].parts() else {
            bail!(
                "Protocol function must return a pair. Got {}",
                io[0].fmt_to_string(&repl.store, &repl.state.borrow())
            )
        };
        let [pre_verify, post_verify] = &expect_ptrs!(repl.store, 2, *idx);

        if pre_verify.is_nil() {
            bail!("Pre-verification predicate rejected the input")
        }

        let Some((cek_io, None)) = repl.store.fetch_list(pre_verify) else {
            bail!("Pre-verification predicate must return a list")
        };
        if cek_io.len() != 6 {
            bail!("Pre-verification predicate return must have length 6")
        }
        Ok((cek_io, *post_verify))
    }

    /// Runs the post-verify predicate (if it's not nil)
    ///
    /// # Errors
    /// * If the predicate is not a function
    /// * If the predicate evaluation fails
    /// * If the predicate rejects the proof (evaluation returns nil)
    fn post_verify_check(repl: &Repl<F, C>, post_verify: Ptr) -> Result<()> {
        if !post_verify.is_nil() {
            let call = repl.store.list(vec![post_verify]);
            let (io, ..) = repl
                .eval_expr_with_env(call, repl.store.intern_empty_env())
                .with_context(|| "evaluating post-verify call")?;
            if io[0].is_nil() {
                bail!("Post-verification predicate rejected the input")
            }
        }
        Ok(())
    }

    /// Returns the corresponding continuation pointer, currently specified as a
    /// keyword
    ///
    /// # Errors
    /// Errors if the continuation specifier does not represent a valid continuation
    fn get_cont_ptr(repl: &Repl<F, C>, cont_key: &Ptr) -> Result<Ptr> {
        let store = &repl.store;
        if cont_key == &store.key("outermost") {
            Ok(store.cont_outermost())
        } else if cont_key == &store.key("terminal") {
            Ok(store.cont_terminal())
        } else if cont_key == &store.key("error") {
            Ok(store.cont_error())
        } else {
            Err(anyhow!(
                "Invalid continuation: {}",
                cont_key.fmt_to_string(store, &repl.state.borrow())
            ))
        }
    }

    const PROVE_PROTOCOL: MetaCmd<F, C> = MetaCmd {
        name: "prove-protocol",
        summary: "Creates a proof for a protocol",
        format: "!(prove-protocol <protocol> <string> args...)",
        description: &[
            "The proof is created only if the protocol can be satisfied by the",
            "  provided arguments.",
            "The second (string) argument for this meta command is the path to",
            "  the file where the protocol proof will be saved.",
        ],
        example: &[
            "(commit '(13 . 17))",
            "!(prove-protocol my-protocol",
            "  \"protocol-proof\"",
            "  0x237fe43a25f3830ab6ac86451b93e74e8ef6ef1e8735a3f53478b7fe76b1a466",
            "  '(13 . 17))",
        ],
        run: |repl, args, _path| {
            let (ptcl, rest) = repl.store.car_cdr(args)?;
            let (path, args) = repl.store.car_cdr(&rest)?;

            let path = get_path(repl, &path)?;

            let (fun, backend, proto_rc) = Self::get_fun_backend_and_rc(repl, ptcl)?;
            if backend != repl.backend {
                bail!(
                    "Protocol uses backend={backend} but the REPL was initialized with backend={}",
                    repl.backend
                )
            }

            if proto_rc != repl.rc {
                bail!(
                    "Protocol uses rc={proto_rc} but the REPL was initialized with rc={}",
                    repl.rc
                )
            }

            let args_vec = Self::get_args_vec(repl, &args)?;

            let mut args_vec_evaled = Vec::with_capacity(args_vec.len());
            for a in args_vec {
                let (io, ..) = repl.eval_expr(a)?;
                args_vec_evaled.push(io[0]);
            }

            // shadowing original `args` with evaluated ones
            let args = repl.store.list(args_vec_evaled.clone());

            let (cek_io, post_verify) = Self::get_cek_io_and_post_verify_fn(repl, fun, args)?;

            Self::post_verify_check(repl, post_verify)?;

            let frames = evaluate_with_env_and_cont::<F, C>(
                Some(repl.lang_setup()),
                cek_io[0],
                cek_io[1],
                Self::get_cont_ptr(repl, &cek_io[2])?,
                &repl.store,
                repl.limit,
            )?;

            let iterations = frames.len();

            {
                // making sure the output matches expectation before proving
                let res = &frames.last().expect("frames can't be empty").output;
                if cek_io[3] != res[0]
                    || cek_io[4] != res[1]
                    || Self::get_cont_ptr(repl, &cek_io[5])? != res[2]
                {
                    bail!("Mismatch between expected output and computed output")
                }
            }

            let proof_key = repl.prove_frames(&frames, iterations)?;
            let mut z_dag = ZDag::default();
            let z_ptr = z_dag.populate_with(&args, &repl.store, &mut Default::default());
            let args = LurkData { z_ptr, z_dag };
            let LurkProof { proof, .. } = load::<LurkProof<'_, _, C>>(&proof_path(&proof_key))?;
            match proof {
                LurkProofWrapper::Nova(proof) => {
                    assert_eq!(backend, Backend::Nova);
                    assert_eq!(repl.backend, Backend::Nova);
                    let proof = ProtocolProofWrapper::Nova(proof);
                    dump(ProtocolProof { args, proof }, &path)?;
                    println!("Protocol (Nova) proof saved at {path}");
                }
                LurkProofWrapper::SuperNova(proof) => {
                    assert_eq!(backend, Backend::SuperNova);
                    assert_eq!(repl.backend, Backend::SuperNova);
                    let proof = ProtocolProofWrapper::SuperNova(proof);
                    dump(ProtocolProof { args, proof }, &path)?;
                    println!("Protocol proof saved at {path}");
                }
            }
            Ok(())
        },
    };

    const VERIFY_PROTOCOL: MetaCmd<F, C> = MetaCmd {
        name: "verify-protocol",
        summary: "Verifies a proof for a protocol",
        format: "!(verify-protocol <protocol> <string>)",
        description: &[
            "Reconstructs the proof input with the args provided by the prover",
            "  according to the protocol and then verifies the proof.",
            "If verification succeeds, runs the post-verification predicate,",
            "  failing if the predicate returns nil.",
            "The second (string) argument is the path to the file containing the",
            "  protocol proof.",
        ],
        example: &["!(verify-protocol my-protocol \"protocol-proof\")"],
        run: |repl, args, _path| {
            let (ptcl, path) = repl.peek2(args)?;

            let path = get_path(repl, &path)?;

            let (fun, backend, proto_rc) = Self::get_fun_backend_and_rc(repl, ptcl)?;

            let ProtocolProof {
                args: LurkData { z_ptr, z_dag },
                proof,
            } = load::<ProtocolProof<F, C1LEM<'a, F, C>>>(&path)?;

            let args = z_dag.populate_store(&z_ptr, &repl.store, &mut Default::default())?;

            let (mut cek_io, post_verify) = Self::get_cek_io_and_post_verify_fn(repl, fun, args)?;

            cek_io[2] = Self::get_cont_ptr(repl, &cek_io[2])?; // cont-in
            cek_io[5] = Self::get_cont_ptr(repl, &cek_io[5])?; // cont-out

            let public_inputs = repl.store.to_scalar_vector(&cek_io[..3]);
            let public_outputs = repl.store.to_scalar_vector(&cek_io[3..]);

            match proof {
                ProtocolProofWrapper::Nova(proof) => {
                    assert_eq!(backend, Backend::Nova);
                    let instance =
                        Instance::new(proto_rc, repl.lang.clone(), true, Kind::NovaPublicParams);
                    let pp = public_params(&instance)?;

                    if !proof.verify(&pp, &public_inputs, &public_outputs)? {
                        bail!("Proof verification failed")
                    }
                }
                ProtocolProofWrapper::SuperNova(proof) => {
                    assert_eq!(backend, Backend::SuperNova);
                    let instance =
                        Instance::new(proto_rc, repl.lang.clone(), true, Kind::SuperNovaAuxParams);
                    let pp = supernova_public_params(&instance)?;

                    if !proof.verify(&pp, &public_inputs, &public_outputs)? {
                        bail!("Proof verification failed")
                    }
                }
            }

            Self::post_verify_check(repl, post_verify)?;
            println!("Proof accepted by the protocol");
            Ok(())
        },
    };

    const CMDS: [MetaCmd<F, C>; 28] = [
        MetaCmd::LOAD,
        MetaCmd::DEF,
        MetaCmd::DEFREC,
        MetaCmd::ASSERT,
        MetaCmd::ASSERT_EQ,
        MetaCmd::ASSERT_EMITTED,
        MetaCmd::ASSERT_ERROR,
        MetaCmd::COMMIT,
        MetaCmd::HIDE,
        MetaCmd::FETCH,
        MetaCmd::OPEN,
        MetaCmd::CLEAR,
        MetaCmd::SET_ENV,
        MetaCmd::PROVE,
        MetaCmd::VERIFY,
        MetaCmd::DEFPACKAGE,
        MetaCmd::IMPORT,
        MetaCmd::IN_PACKAGE,
        MetaCmd::HELP,
        MetaCmd::CALL,
        MetaCmd::CHAIN,
        MetaCmd::INSPECT,
        MetaCmd::INSPECT_FULL,
        MetaCmd::DUMP_DATA,
        MetaCmd::DEF_LOAD_DATA,
        MetaCmd::DEFPROTOCOL,
        MetaCmd::PROVE_PROTOCOL,
        MetaCmd::VERIFY_PROTOCOL,
    ];

    pub(super) fn cmds() -> std::collections::HashMap<&'static str, MetaCmd<F, C>> {
        HashMap::from(Self::CMDS.map(|x| (x.name, x)))
    }
}

#[derive(Serialize, Deserialize)]
struct LurkData<F: LurkField> {
    z_ptr: ZPtr<F>,
    z_dag: ZDag<F>,
}

impl<F: LurkField> HasFieldModulus for LurkData<F> {
    fn field_modulus() -> String {
        F::MODULUS.to_string()
    }
}

/// Returns a `Utf8PathBuf` from a pointer
///
/// # Errors
/// Errors if a string can't be fetched with the pointer
fn get_path<F: LurkField, C: Coprocessor<F> + Serialize + DeserializeOwned>(
    repl: &Repl<F, C>,
    path: &Ptr,
) -> Result<Utf8PathBuf> {
    let Some(path) = repl.store.fetch_string(path) else {
        bail!(
            "Path must be a string. Got {}",
            path.fmt_to_string(&repl.store, &repl.state.borrow())
        )
    };
    Ok(Utf8PathBuf::from(path))
}

#[non_exhaustive]
#[derive(Serialize, Deserialize)]
#[serde(bound(serialize = "F: Serialize", deserialize = "F: DeserializeOwned"))]
enum ProtocolProofWrapper<F: CurveCycleEquipped, S> {
    Nova(nova::Proof<F, S>),
    SuperNova(supernova::Proof<F, S>),
}

/// Contains the data needed for proof validation (according to some protocol)
/// and verification
#[non_exhaustive]
#[derive(Serialize, Deserialize)]
#[serde(bound(serialize = "F: Serialize", deserialize = "F: DeserializeOwned"))]
struct ProtocolProof<F: CurveCycleEquipped, S> {
    args: LurkData<F>,
    proof: ProtocolProofWrapper<F, S>,
}

impl<F: CurveCycleEquipped, S: StepCircuit<F>> HasFieldModulus for ProtocolProof<F, S> {
    fn field_modulus() -> String {
        F::MODULUS.to_owned()
    }
}
