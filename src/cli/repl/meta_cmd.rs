use ::nova::traits::Engine;
use abomonation::Abomonation;
use anyhow::{anyhow, bail, Context, Result};
use camino::Utf8PathBuf;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::{collections::HashMap, process};

use crate::{
    cli::{
        field_data::{dump, load, HasFieldModulus},
        lurk_proof::{LurkProof, LurkProofMeta},
        paths::proof_path,
        zstore::ZDag,
    },
    coprocessor::Coprocessor,
    eval::lang::Coproc,
    field::LurkField,
    lem::{
        eval::evaluate_with_env_and_cont,
        multiframe::MultiFrame,
        pointers::{Ptr, ZPtr},
        Tag,
    },
    package::{Package, SymbolRef},
    proof::{
        nova::{self, CurveCycleEquipped, E1, E2},
        MultiFrameTrait, RecursiveSNARKTrait,
    },
    public_parameters::{
        instance::{Instance, Kind},
        public_params,
    },
    tag::{ContTag, ExprTag},
};

use super::Repl;

pub(super) struct MetaCmd<F: LurkField> {
    name: &'static str,
    summary: &'static str,
    format: &'static str,
    description: &'static [&'static str],
    example: &'static [&'static str],
    pub(super) run: fn(repl: &mut Repl<F>, args: &Ptr) -> Result<()>,
}

type F = pasta_curves::pallas::Scalar; // TODO: generalize this

impl MetaCmd<F> {
    const LOAD: MetaCmd<F> = MetaCmd {
        name: "load",
        summary: "Load lurk expressions from a file.",
        format: "!(load <string>)",
        description: &[],
        example: &["!(load \"my_file.lurk\")"],
        run: |repl, args| {
            let first = repl.peek1(args)?;
            if let Some(path) = repl.store.fetch_string(&first) {
                repl.load_file(&repl.pwd_path.join(path), false)
            } else {
                bail!("Argument of `load` must be a string.")
            }
        },
    };
}

impl MetaCmd<F> {
    const DEF: MetaCmd<F> = MetaCmd {
        name: "def",
        summary: "Extends env with a non-recursive binding.",
        format: "!(def <binding> <body>)",
        description: &[
            "Gets macroexpanded to this: (let ((foo (lambda () 123))) (current-env))",
            "The state's env is set to the result.",
        ],
        example: &["!(def foo (lambda () 123))"],
        run: |repl: &mut Repl<F>, args: &Ptr| {
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
}

impl MetaCmd<F> {
    const DEFREC: MetaCmd<F> = MetaCmd {
        name: "defrec",
        summary: "Extends the env with a recursive binding.",
        format: "!(defrec <binding> <body>)",
        description: &[
            "Gets macroexpanded to this: (letrec ((foo (lambda () 123))) (current-env))",
            "The state's env is set ot the result.",
        ],
        example: &[
            "!(defrec sum (lambda (l) (if (eq l nil) 0 (+ (car l) (sum (cdr l))))))",
            "(sum '(1 2 3))",
        ],
        run: |repl, args| {
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
}

impl MetaCmd<F> {
    const ASSERT: MetaCmd<F> = MetaCmd {
        name: "assert",
        summary: "Assert that an expression evaluates to true.",
        format: "!(assert <expr>)",
        description: &[],
        example: &["!(assert t)", "!(assert (eq 3 (+ 1 2)))"],
        run: |repl, args| {
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
}

impl MetaCmd<F> {
    const ASSERT_EQ: MetaCmd<F> = MetaCmd {
        name: "assert-eq",
        summary: "Assert that two expressions evaluate to the same value.",
        format: "!(assert-eq <expr> <expr>)",
        description: &[],
        example: &["!(assert-eq 3 (+ 1 2))"],
        run: |repl, args| {
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
}

impl MetaCmd<F> {
    const ASSERT_EMITTED: MetaCmd<F> = MetaCmd {
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
        run: |repl, args| {
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
}

impl MetaCmd<F> {
    const ASSERT_ERROR: MetaCmd<F> = MetaCmd {
        name: "assert-error",
        summary: "Assert that a evaluation of <expr> fails.",
        format: "!(assert-error <expr>)",
        description: &[],
        example: &["!(assert-error (1 1))"],
        run: |repl, args| {
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
}

impl MetaCmd<F> {
    const COMMIT: MetaCmd<F> = MetaCmd {
        name:
            "commit",
        summary:
            "Compute the commitment of <expr>.",
        format:
            "!(commit <expr>)",
        description: &[],
        example: &[
            "!(commit '(13 . 21))",
            "(let ((n (open 0x0071a3fe5e3a0dea9f7257e3210ea719f3464f2aa52a2cd6e6176c8275a75b25))) (* (car n) (cdr n)))",
        ],
        run: |repl, args| {
            let first = repl.peek1(args)?;
            let (first_io, ..) = repl.eval_expr(first)?;
            repl.hide(F::NON_HIDING_COMMITMENT_SECRET, first_io[0])
        }
    };
}

impl MetaCmd<F> {
    const HIDE: MetaCmd<F> = MetaCmd {
        name: "hide",
        summary: "Return and persist the commitment of <exp> using secret <secret>.",
        format: "!(hide <secret> <expr>)",
        description: &[],
        example: &[
            "!(hide 12345 '(13 . 21))",
            "(secret (comm 0x3be5f551534baa53a9c180e49b48c4a75ed7642a82197be5f674d54681de4425))",
            "(open 0x3be5f551534baa53a9c180e49b48c4a75ed7642a82197be5f674d54681de4425)",
        ],
        run: |repl, args| {
            let (first, second) = repl.peek2(args)?;
            let (first_io, ..) = repl
                .eval_expr(first)
                .with_context(|| "evaluating first arg")?;
            let (second_io, ..) = repl
                .eval_expr(second)
                .with_context(|| "evaluating second arg")?;
            let Ptr::Atom(Tag::Expr(ExprTag::Num), secret) = first_io[0] else {
                bail!(
                    "Secret must be a number. Got {}",
                    first_io[0].fmt_to_string(&repl.store, &repl.state.borrow())
                )
            };
            let secret = *repl.store.expect_f(secret);
            repl.hide(secret, second_io[0])?;
            Ok(())
        },
    };
}

impl MetaCmd<F> {
    const FETCH: MetaCmd<F> = MetaCmd {
        name: "fetch",
        summary: "Add data from a commitment to the repl store.",
        format: "!(fetch <commitment>)",
        description: &[],
        example: &[
            "!(commit '(13 . 21))",
            "!(fetch 0x0071a3fe5e3a0dea9f7257e3210ea719f3464f2aa52a2cd6e6176c8275a75b25)",
        ],
        run: |repl, args| {
            let hash = *repl.get_comm_hash(args)?;
            repl.fetch(&hash, false)
        },
    };
}

impl MetaCmd<F> {
    const OPEN: MetaCmd<F> = MetaCmd {
        name: "open",
        summary: "Open a commitment.",
        format: "!(open <commitment>)",
        description: &[],
        example: &[
            "!(commit '(13 . 21))",
            "!(open 0x0071a3fe5e3a0dea9f7257e3210ea719f3464f2aa52a2cd6e6176c8275a75b25)",
        ],
        run: |repl, args| {
            let hash = *repl.get_comm_hash(args)?;
            repl.fetch(&hash, true)
        },
    };
}

impl<F: LurkField> MetaCmd<F> {
    const CLEAR: MetaCmd<F> = MetaCmd {
        name: "clear",
        summary: "Reset the current environment to be empty.",
        format: "!(clear)",
        description: &[],
        example: &["!(def a 1)", "(current-env)", "!(clear)", "(current-env)"],
        run: |repl, _args| {
            repl.env = repl.store.intern_nil();
            Ok(())
        },
    };
}

impl MetaCmd<F> {
    const SET_ENV: MetaCmd<F> = MetaCmd {
        name: "set-env",
        summary: "Set the env to the result of evaluating the first argument.",
        format: "!(set-env <expr>)",
        description: &[],
        example: &["!(set-env '((a . 1) (b . 2)))", "a"],
        run: |repl, args| {
            let first = repl.peek1(args)?;
            let (first_io, ..) = repl.eval_expr(first)?;
            repl.env = first_io[0];
            Ok(())
        },
    };
}

impl MetaCmd<F> {
    const PROVE: MetaCmd<F> = MetaCmd {
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
            "!(verify \"Nova_Pallas_10_002cd7baecd8e781d217cd1eb8b67d4f890005fd3763541e37ce49550bd9f4bf\")",
            "!(open 0x002cd7baecd8e781d217cd1eb8b67d4f890005fd3763541e37ce49550bd9f4bf)",
        ],
        run: |repl, args| {
            if !args.is_nil() {
                repl.eval_expr_and_memoize(repl.peek1(args)?)?;
            }
            repl.prove_last_frames()?;
            Ok(())
        }
    };
}

impl<F: CurveCycleEquipped + Serialize + DeserializeOwned> MetaCmd<F>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    const VERIFY: MetaCmd<F> = MetaCmd {
        name: "verify",
        summary: "Verify a proof",
        format: "!(verify <string>)",
        description: &["Verify proof key <string> and print the result."],
        example: &[
            "!(prove '(1 2 3))",
            "!(verify \"Nova_Pallas_10_166fafef9d86d1ddd29e7b62fa5e4fb2d7f4d885baf28e23187860d0720f74ca\")",
            "!(open 0x166fafef9d86d1ddd29e7b62fa5e4fb2d7f4d885baf28e23187860d0720f74ca)",
        ],
        run: |repl, args| {
            let first = repl.peek1(args)?;
            let proof_id = repl.get_string(&first)?;
            LurkProof::<_, _, MultiFrame<'_, _, Coproc<F>>>::verify_proof(
                &proof_id,
            )
        }
    };
}

impl<F: LurkField> MetaCmd<F> {
    const DEFPACKAGE: MetaCmd<F> = MetaCmd {
        name: "defpackage",
        summary: "Add a package to the state.",
        format: "!(defpackage <string|symbol>)",
        description: &[],
        example: &["!(defpackage abc)"],
        run: |repl, args| {
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
}

impl<F: LurkField> MetaCmd<F> {
    const IMPORT: MetaCmd<F> = MetaCmd {
        name: "import",
        summary: "Import a single or several packages.",
        format: "!(import <string|package> ...)",
        description: &[],
        example: &[],
        run: |repl, args| {
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
}

impl<F: LurkField> MetaCmd<F> {
    const IN_PACKAGE: MetaCmd<F> = MetaCmd {
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
        run: |repl, args| {
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
}

impl<F: LurkField> MetaCmd<F> {
    const HELP: MetaCmd<F> = MetaCmd {
        name: "help",
        summary: "Print help message.",
        format: "!(help <string|symbol>)",
        description: &[
            "Without arguments it prints a summary of all available commands.",
            "Otherwise the full help for the command in the first argument is printed.",
        ],
        example: &["!(help)", "!(help verify)", "!(help \"load\")"],
        run: |repl, args| {
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
                    for (_, i) in MetaCmd::cmds().iter().sorted_by_key(|x| x.0) {
                        println!("  {} - {}", i.name, i.summary);
                    }
                }
                _ => bail!("The optional argument of `help` must be a string or symbol"),
            }
            Ok(())
        },
    };

    fn meta_help(cmd: &str) {
        match MetaCmd::cmds().get(cmd) {
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
}

impl MetaCmd<F> {
    fn call(repl: &mut Repl<F>, args: &Ptr) -> Result<()> {
        let (hash_ptr, args) = repl.store.car_cdr(args)?;
        let hash_expr = match hash_ptr.tag() {
            Tag::Expr(ExprTag::Cons) => hash_ptr,
            _ => repl.store.list(vec![hash_ptr]),
        };
        let hash = *repl.get_comm_hash(&hash_expr)?;
        if repl.store.open(hash).is_none() {
            repl.fetch(&hash, false)?;
        }
        let open = repl.store.intern_lurk_symbol("open");
        let open_expr = repl.store.list(vec![open, repl.store.num(hash)]);
        let (args_vec, _) = repl
            .store
            .fetch_list(&args)
            .expect("data must have been interned");
        let mut expr_vec = Vec::with_capacity(args_vec.len() + 1);
        expr_vec.push(open_expr);
        expr_vec.extend(args_vec);
        repl.handle_non_meta(repl.store.list(expr_vec))
    }

    const CALL: MetaCmd<F> = MetaCmd {
        name: "call",
        summary: "Open a functional commitment then apply arguments to it",
        format: "!(call <hash> <args>)",
        description: &[],
        example: &[
            "(commit (lambda (x) x))",
            "!(call 0x39a14e7823d7af7275e83f0cb74f80ca4217c6c6930761b0bbd6879b123dbbc2 0)",
        ],
        run: Self::call,
    };
}

impl MetaCmd<F> {
    const CHAIN: MetaCmd<F> = MetaCmd {
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
            "!(chain 0x06042852d90bf409974d1ee3bc153c0f48ea5512c9b4f697561df9ad7b5abbe0 1)",
        ],
        run: |repl: &mut Repl<F>, args: &Ptr| {
            Self::call(repl, args)?;
            let ev = repl
                .get_evaluation()
                .as_ref()
                .expect("evaluation must have been set");
            let result = ev
                .get_result()
                .expect("evaluation result must have been set");
            let (_, comm) = repl.store.car_cdr(result)?;
            let Ptr::Atom(Tag::Expr(ExprTag::Comm), hash) = comm else {
                bail!("Second component of a chain must be a commitment")
            };
            let hash = *repl.store.expect_f(hash);
            // retrieve from store to persist
            let (secret, fun) = repl
                .store
                .open(hash)
                .expect("data must have been committed");
            repl.hide(*secret, *fun)
        },
    };
}

impl<F: LurkField + DeserializeOwned> MetaCmd<F> {
    fn inspect(repl: &mut Repl<F>, args: &Ptr, full: bool) -> Result<()> {
        let first = repl.peek1(args)?;
        let proof_id = repl.get_string(&first)?;
        LurkProofMeta::<F>::inspect_proof(
            &proof_id,
            Some((&repl.store, &repl.state.borrow())),
            full,
        )
    }

    const INSPECT: MetaCmd<F> = MetaCmd {
        name: "inspect",
        summary: "Print part of a proof claim",
        format: "!(inspect <string>)",
        description: &[],
        example: &[
            "!(prove '(1 2 3))",
            "!(inspect \"Nova_Pallas_10_002cd7baecd8e781d217cd1eb8b67d4f890005fd3763541e37ce49550bd9f4bf\")",
        ],
        run: |repl, args| {
            Self::inspect(repl, args, false)
        }
    };
}

impl<F: LurkField + DeserializeOwned> MetaCmd<F> {
    const INSPECT_FULL: MetaCmd<F> = MetaCmd {
        name: "inspect-full",
        summary: "Print a proof claim",
        format: "!(inspect-full <string>)",
        description: &[],
        example: &[
            "!(prove '(1 2 3))",
            "!(inspect-full \"Nova_Pallas_10_002cd7baecd8e781d217cd1eb8b67d4f890005fd3763541e37ce49550bd9f4bf\")",
        ],
        run: |repl, args| {
            Self::inspect(repl, args, true)
        }
    };
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
fn get_path<F: LurkField>(repl: &Repl<F>, path: &Ptr) -> Result<Utf8PathBuf> {
    let Some(path) = repl.store.fetch_string(path) else {
        bail!(
            "Path must be a string. Got {}",
            path.fmt_to_string(&repl.store, &repl.state.borrow())
        )
    };
    Ok(Utf8PathBuf::from(path))
}

impl MetaCmd<F> {
    const DUMP_DATA: MetaCmd<F> = MetaCmd {
        name: "dump-data",
        summary: "Write Lurk data to the file system",
        format: "!(dump-data <expr> <string>)",
        description: &[],
        example: &["!(dump-data (+ 1 1) \"my_file\")"],
        run: |repl, args| {
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
}

impl<F: LurkField + DeserializeOwned> MetaCmd<F> {
    const DEF_LOAD_DATA: MetaCmd<F> = MetaCmd {
        name: "def-load-data",
        summary: "Read Lurk data from the file system and bind it to a symbol",
        format: "!(def-load-data <symbol> <string>)",
        description: &[],
        example: &["!(def-load-data x \"my_file\")"],
        run: |repl, args| {
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
            let binding = repl.store.cons(sym, ptr);
            repl.env = repl.store.cons(binding, repl.env);
            Ok(())
        },
    };
}

impl MetaCmd<F> {
    const DEFPROTOCOL: MetaCmd<F> = MetaCmd {
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
            "        (list6 (mk-open-expr hash) nil :outermost pair nil :terminal)",
            "        nil)",
            "      (lambda () (> (car pair) 10))))",
            "  :rc 10",
            "  :description \"example protocol\")",
        ],
        run: |repl, args| {
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
            let (io, ..) = repl.eval_expr_with_env(lambda, repl.store.intern_nil())?;
            let fun = io[0];
            if !fun.is_fun() {
                bail!(
                    "Protocol definition failed to evaluate to a function. Got {}",
                    fun.fmt_to_string(&repl.store, &repl.state.borrow())
                )
            }

            let prop_map = repl.get_properties(&props, &["rc", "lang", "description"])?;

            let get_prop = |key, accepts: fn(&Ptr) -> bool, def: fn(&Repl<F>) -> Ptr| -> Result<Ptr> {
                match prop_map.get(key) {
                    Some(val) => {
                        if accepts(val) {
                            Ok(*val)
                        } else {
                            bail!("Invalid value for {key}")
                        }
                    }
                    None => Ok(def(repl)),
                }
            };

            let rc = get_prop(
                "rc",
                Ptr::is_num,
                |repl| repl.store.num_u64(repl.rc.try_into().unwrap())
            )?;

            // TODO: handle lang properly
            let lang = get_prop(
                "lang",
                |_| true, // accept anything for now
                |repl| repl.store.intern_nil()
            )?;

            let description = get_prop(
                "description",
                Ptr::is_str,
                |repl| repl.store.intern_string("")
            )?;

            // the standard format for a processed protocol as Lurk data
            let protocol = repl.store.list(vec![fun, rc, lang, description]);
            let binding = repl.store.cons(name, protocol);
            repl.env = repl.store.cons(binding, repl.env);
            Ok(())
        },
    };
}

/// Contains the data needed for proof validation (according to some protocol)
/// and verification
#[non_exhaustive]
#[derive(Serialize, Deserialize)]
#[serde(bound(serialize = "F: Serialize", deserialize = "F: DeserializeOwned"))]
enum ProtocolProof<
    'a,
    F: CurveCycleEquipped,
    C: Coprocessor<F> + Serialize + DeserializeOwned,
    M: MultiFrameTrait<'a, F, C>,
> where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    Nova {
        args: LurkData<F>,
        proof: nova::Proof<'a, F, C, M>,
        num_steps: usize,
    },
}

impl<
        'a,
        F: CurveCycleEquipped,
        C: Coprocessor<F> + 'a + Serialize + DeserializeOwned,
        M: MultiFrameTrait<'a, F, C>,
    > HasFieldModulus for ProtocolProof<'a, F, C, M>
where
    <<E1<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
    <<E2<F> as Engine>::Scalar as ff::PrimeField>::Repr: Abomonation,
{
    fn field_modulus() -> String {
        F::MODULUS.to_owned()
    }
}

impl MetaCmd<F> {
    /// Returns the protocol function and reduction count
    ///
    /// # Errors
    /// * If the protocol evaluation fails
    /// * If the reduction count is not a number or can't be converted to `u64`
    fn get_fun_and_rc(repl: &Repl<F>, ptcl: Ptr) -> Result<(Ptr, usize)> {
        let (io, ..) = repl
            .eval_expr(ptcl)
            .with_context(|| "evaluating protocol")?;
        let ptcl = &io[0];

        let (fun, rest) = repl.store.car_cdr(ptcl)?;

        let (Ptr::Atom(Tag::Expr(ExprTag::Num), rc_idx), _) = repl.store.car_cdr(&rest)? else {
            bail!("Reduction count must be a Num")
        };
        let Some(rc) = repl.store.expect_f(rc_idx).to_u64().map(|u| u as usize) else {
            bail!("Invalid value for reduction count")
        };
        Ok((fun, rc))
    }

    /// Returns a vector containing the elements of a list.
    ///
    /// # Errors
    /// Errors if the the list of arguments is not proper
    fn get_args_vec(repl: &Repl<F>, args: &Ptr) -> Result<Vec<Ptr>> {
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
        repl: &Repl<F>,
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
            .eval_expr_with_env(apply_call, repl.store.intern_nil())
            .with_context(|| "evaluating protocol function call")?;

        let Ptr::Tuple2(Tag::Expr(ExprTag::Cons), idx) = &io[0] else {
            bail!(
                "Protocol function must return a pair. Got {}",
                io[0].fmt_to_string(&repl.store, &repl.state.borrow())
            )
        };
        let (pre_verify, post_verify) = repl.store.fetch_2_ptrs(*idx).unwrap();

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
    fn post_verify_check(repl: &Repl<F>, post_verify: Ptr) -> Result<()> {
        if !post_verify.is_nil() {
            let call = repl.store.list(vec![post_verify]);
            let (io, ..) = repl
                .eval_expr_with_env(call, repl.store.intern_nil())
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
    fn get_cont_ptr(repl: &Repl<F>, cont_key: &Ptr) -> Result<Ptr> {
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

    const PROVE_PROTOCOL: MetaCmd<F> = MetaCmd {
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
            "  0x09910d31a7568d66855bcc83fccc4826063dfdf93fe5e1f736c83ec892ed139e",
            "  '(13 . 17))",
        ],
        run: |repl, args| {
            let (ptcl, rest) = repl.store.car_cdr(args)?;
            let (path, args) = repl.store.car_cdr(&rest)?;

            let path = get_path(repl, &path)?;

            let (fun, proto_rc) = Self::get_fun_and_rc(repl, ptcl)?;

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

            let (frames, iterations) = evaluate_with_env_and_cont::<F, Coproc<F>>(
                None,
                cek_io[0],
                cek_io[1],
                Self::get_cont_ptr(repl, &cek_io[2])?,
                &repl.store,
                repl.limit,
            )?;

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
            match load::<LurkProof<'_, _, _, MultiFrame<'_, _, Coproc<F>>>>(&proof_path(
                &proof_key,
            ))? {
                LurkProof::Nova {
                    proof,
                    public_inputs: _,
                    public_outputs: _,
                    num_steps,
                    ..
                } => {
                    dump(
                        ProtocolProof::Nova {
                            args,
                            proof,
                            num_steps,
                        },
                        &path,
                    )?;
                    println!("Protocol proof saved at {path}");
                    Ok(())
                }
            }
        },
    };
}

impl MetaCmd<F> {
    const VERIFY_PROTOCOL: MetaCmd<F> = MetaCmd {
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
        run: |repl, args| {
            let (ptcl, path) = repl.peek2(args)?;

            let path = get_path(repl, &path)?;

            let (fun, proto_rc) = Self::get_fun_and_rc(repl, ptcl)?;

            match load::<ProtocolProof<'_, _, _, MultiFrame<'_, _, Coproc<F>>>>(&path)? {
                ProtocolProof::Nova {
                    args: LurkData { z_ptr, z_dag },
                    proof,
                    num_steps,
                } => {
                    let args =
                        z_dag.populate_store(&z_ptr, &repl.store, &mut Default::default())?;

                    let (mut cek_io, post_verify) =
                        Self::get_cek_io_and_post_verify_fn(repl, fun, args)?;

                    cek_io[2] = Self::get_cont_ptr(repl, &cek_io[2])?; // cont-in
                    cek_io[5] = Self::get_cont_ptr(repl, &cek_io[5])?; // cont-out

                    let instance =
                        Instance::new(proto_rc, repl.lang.clone(), true, Kind::NovaPublicParams);
                    let pp = public_params(&instance)?;

                    if !proof.verify(
                        &pp,
                        &repl.store.to_scalar_vector(&cek_io[..3]),
                        &repl.store.to_scalar_vector(&cek_io[3..]),
                        num_steps,
                    )? {
                        bail!("Proof verification failed")
                    }

                    Self::post_verify_check(repl, post_verify)?;
                    println!("Proof accepted by the protocol");
                    Ok(())
                }
            }
        },
    };
}

impl MetaCmd<F> {
    const CMDS: [MetaCmd<F>; 28] = [
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

    pub(super) fn cmds() -> std::collections::HashMap<&'static str, MetaCmd<F>> {
        HashMap::from(Self::CMDS.map(|x| (x.name, x)))
    }
}
