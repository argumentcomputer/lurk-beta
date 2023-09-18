use anyhow::{bail, Context, Result};
use camino::Utf8Path;
use std::process;

use crate::{
    cli::lurk_proof::LurkProof,
    field::LurkField,
    lurk_sym_ptr,
    package::{Package, SymbolRef},
    ptr::Ptr,
    tag::{ContTag, ExprTag},
    writer::Write,
};

use super::Repl;

pub(super) struct MetaCmd<F: LurkField> {
    name: &'static str,
    summary: &'static str,
    format: &'static str,
    description: &'static [&'static str],
    example: &'static [&'static str],
    pub(super) run:
        fn(repl: &mut Repl<F>, cmd: &str, args: &Ptr<F>, pwd_path: &Utf8Path) -> Result<()>,
}

type F = pasta_curves::pallas::Scalar; // TODO: generalize this

impl MetaCmd<F> {
    const LOAD: MetaCmd<F> = MetaCmd {
        name: "load",
        summary: "Load lurk expressions from a file path.",
        format: "!(load <string>)",
        description: &[],
        example: &["Load lurk expressions from a file path."],
        run: |repl, cmd, args, pwd_path| {
            let first = repl.peek1(cmd, args)?;
            match repl.store.fetch_string(&first) {
                Some(path) => {
                    let joined = pwd_path.join(Utf8Path::new(&path));
                    repl.load_file(&joined)?
                }
                _ => bail!("Argument of `load` must be a string."),
            }
            return Ok(());
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
        run: |repl: &mut Repl<F>, cmd: &str, args: &Ptr<F>, _pwd_path: &Utf8Path| {
            let (first, second) = repl.peek2(cmd, args)?;
            let l = lurk_sym_ptr!(&repl.store, let_);
            let current_env = lurk_sym_ptr!(&repl.store, current_env);
            let binding = &repl.store.list(&[first, second]);
            let bindings = &repl.store.list(&[*binding]);
            let current_env_call = &repl.store.list(&[current_env]);
            let expanded = &repl.store.list(&[l, *bindings, *current_env_call]);
            let (expanded_io, ..) = repl.eval_expr(*expanded)?;
            repl.env = expanded_io.expr;
            let (new_binding, _) = &repl.store.car_cdr(&expanded_io.expr)?;
            let (new_name, _) = repl.store.car_cdr(new_binding)?;
            println!(
                "{}",
                new_name.fmt_to_string(&repl.store, &repl.state.borrow())
            );
            return Ok(());
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
        run: |repl, cmd, args, _pwd_path| {
            let (first, second) = repl.peek2(cmd, args)?;
            let l = lurk_sym_ptr!(&repl.store, letrec);
            let current_env = lurk_sym_ptr!(&repl.store, current_env);
            let binding = &repl.store.list(&[first, second]);
            let bindings = &repl.store.list(&[*binding]);
            let current_env_call = &repl.store.list(&[current_env]);
            let expanded = &repl.store.list(&[l, *bindings, *current_env_call]);
            let (expanded_io, ..) = repl.eval_expr(*expanded)?;

            repl.env = expanded_io.expr;

            let (new_binding_outer, _) = &repl.store.car_cdr(&expanded_io.expr)?;
            let (new_binding_inner, _) = &repl.store.car_cdr(new_binding_outer)?;
            let (new_name, _) = repl.store.car_cdr(new_binding_inner)?;
            println!(
                "{}",
                new_name.fmt_to_string(&repl.store, &repl.state.borrow())
            );
            return Ok(());
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
        run: |repl, cmd, args, _pwd_path| {
            let first = repl.peek1(cmd, args)?;
            let (first_io, ..) = repl.eval_expr(first)?;
            if first_io.expr.is_nil() {
                eprintln!(
                    "`assert` failed. {} evaluates to nil",
                    first.fmt_to_string(&repl.store, &repl.state.borrow())
                );
                process::exit(1);
            }
            return Ok(());
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
        run: |repl, cmd, args, _pwd_path| {
            let (first, second) = repl.peek2(cmd, args)?;
            let (first_io, ..) = repl
                .eval_expr(first)
                .with_context(|| "evaluating first arg")?;
            let (second_io, ..) = repl
                .eval_expr(second)
                .with_context(|| "evaluating second arg")?;
            if !&repl.store.ptr_eq(&first_io.expr, &second_io.expr)? {
                eprintln!(
                    "`assert-eq` failed. Expected:\n  {} = {}\nGot:\n  {} ≠ {}",
                    first.fmt_to_string(&repl.store, &repl.state.borrow()),
                    second.fmt_to_string(&repl.store, &repl.state.borrow()),
                    first_io
                        .expr
                        .fmt_to_string(&repl.store, &repl.state.borrow()),
                    second_io
                        .expr
                        .fmt_to_string(&repl.store, &repl.state.borrow())
                );
                process::exit(1);
            }
            return Ok(());
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
        run: |repl, cmd, args, _pwd_path| {
            let (first, second) = repl.peek2(cmd, args)?;
            let (first_io, ..) = repl
                .eval_expr(first)
                .with_context(|| "evaluating first arg")?;
            let (.., emitted) = repl
                .eval_expr(second)
                .with_context(|| "evaluating second arg")?;
            let (mut first_emitted, mut rest_emitted) = repl.store.car_cdr(&first_io.expr)?;
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
            return Ok(());
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
        run: |repl, cmd, args, _pwd_path| {
            let first = repl.peek1(cmd, args)?;
            let (first_io, ..) = repl.eval_expr_allowing_error_continuation(first)?;
            if first_io.cont.tag != ContTag::Error {
                eprintln!(
                    "`assert-error` failed. {} doesn't result on evaluation error.",
                    first.fmt_to_string(&repl.store, &repl.state.borrow())
                );
                process::exit(1);
            }
            return Ok(());
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
            "(let ((n (open 0x2c4e1dc8a344764c52d97c691ef0d8312e07b38e99f12cf2f200891c53fb36c0))) (* (car n) (cdr n)))",
        ],
        run: |repl, cmd, args, _pwd_path| {
            let first = repl.peek1(cmd, args)?;
            let (first_io, ..) = repl.eval_expr(first)?;
            repl.hide(ff::Field::ZERO, first_io.expr)?;
            return Ok(());
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
        run: |repl, cmd, args, _pwd_path| {
            let (first, second) = repl.peek2(cmd, args)?;
            let (first_io, ..) = repl
                .eval_expr(first)
                .with_context(|| "evaluating first arg")?;
            let (second_io, ..) = repl
                .eval_expr(second)
                .with_context(|| "evaluating second arg")?;
            let Some(secret) = repl.store.fetch_num(&first_io.expr) else {
                bail!(
                    "Secret must be a number. Got {}",
                    first_io.expr.fmt_to_string(&repl.store, &repl.state.borrow())
                )
            };
            repl.hide(secret.into_scalar(), second_io.expr)?;
            return Ok(());
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
            "(fetch 0x2c4e1dc8a344764c52d97c691ef0d8312e07b38e99f12cf2f200891c53fb36c0)",
        ],
        run: |repl, cmd, args, _pwd_path| {
            let hash = repl.get_comm_hash(cmd, args)?;
            repl.fetch(&hash, false)?;
            return Ok(());
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
            "!(open 0x2c4e1dc8a344764c52d97c691ef0d8312e07b38e99f12cf2f200891c53fb36c0)",
        ],
        run: |repl, cmd, args, _pwd_path| {
            let hash = repl.get_comm_hash(cmd, args)?;
            repl.fetch(&hash, true)?;
            return Ok(());
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
        run: |repl, _cmd, _args, _pwd_path| {
            repl.env = lurk_sym_ptr!(&repl.store, nil);
            return Ok(());
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
        run: |repl, cmd, args, _pwd_path| {
            // The state's env is set to the result of evaluating the first argument.
            let first = repl.peek1(cmd, args)?;
            let (first_io, ..) = repl.eval_expr(first)?;
            repl.env = first_io.expr;
            return Ok(());
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
            "!(verify \"Nova_Pallas_10_166fafef9d86d1ddd29e7b62fa5e4fb2d7f4d885baf28e23187860d0720f74ca\")",
            "!(open 0x166fafef9d86d1ddd29e7b62fa5e4fb2d7f4d885baf28e23187860d0720f74ca)",
        ],
        run: |repl, cmd, args, _pwd_path| {
            if !args.is_nil() {
                repl.eval_expr_and_memoize(repl.peek1(cmd, args)?)?;
            }
            repl.prove_last_frames()?;
            return Ok(());
        }
    };
}

impl<F: LurkField> MetaCmd<F> {
    const VERIFY: MetaCmd<F> = MetaCmd {
        name:
            "verify",
        summary:
            "Verify a proof",
        format:
            "!(verify <string>)",
        description: &[
            "Verify proof id <string> and print the result.",
        ],
        example: &[
            "!(prove '(1 2 3))",
            "!(verify \"Nova_Pallas_10_166fafef9d86d1ddd29e7b62fa5e4fb2d7f4d885baf28e23187860d0720f74ca\")",
            "!(open 0x166fafef9d86d1ddd29e7b62fa5e4fb2d7f4d885baf28e23187860d0720f74ca)",
        ],
        run: |repl, cmd, args, _pwd_path| {
            let first = repl.peek1(cmd, args)?;
            let proof_id = repl.get_string(&first)?;
            LurkProof::verify_proof(&proof_id)?;
            return Ok(());
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
        run: |repl, _cmd, args, _pwd_path| {
            // TODO: handle args
            let (name, _args) = repl.store.car_cdr(args)?;
            let name = match name.tag {
                ExprTag::Str => repl.state.borrow_mut().intern(repl.get_string(&name)?),
                ExprTag::Sym => repl.get_symbol(&name)?.into(),
                _ => bail!("Package name must be a string or a symbol"),
            };
            println!("{}", repl.state.borrow().fmt_to_string(&name));
            let package = Package::new(name);
            repl.state.borrow_mut().add_package(package);
            return Ok(());
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
        run: |repl, _cmd, args, _pwd_path| {
            // TODO: handle pkg
            let (mut symbols, _pkg) = repl.store.car_cdr(args)?;
            if symbols.tag == ExprTag::Sym {
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
            return Ok(());
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
        run: |repl, cmd, args, _pwd_path| {
            let first = repl.peek1(cmd, args)?;
            match first.tag {
                ExprTag::Str => {
                    let name = repl.get_string(&first)?;
                    let package_name = repl.state.borrow_mut().intern(name);
                    repl.state.borrow_mut().set_current_package(package_name)?;
                }
                ExprTag::Sym => {
                    let package_name = repl.get_symbol(&first)?;
                    repl.state
                        .borrow_mut()
                        .set_current_package(package_name.into())?;
                }
                _ => bail!(
                    "Expected string or symbol. Got {}",
                    first.fmt_to_string(&repl.store, &repl.state.borrow())
                ),
            }
            return Ok(());
        },
    };
}

impl<F: LurkField> MetaCmd<F> {
    const HELP: MetaCmd<F> = MetaCmd {
        name: "help",
        summary: "Print help message.",
        format: "!(help [<string>|<symbol>])",
        description: &[
            "Without arguments it prints a summary of all available commands.",
            "Otherwise the full help for the command in the first argument is printed.",
        ],
        example: &["!(help)", "!(help verify)", "!(help \"load\")"],
        run: |repl, cmd, args, _pwd_path| {
            let first = repl.peek1(cmd, args)?;
            match first.tag {
                ExprTag::Str => {
                    let name = repl.get_string(&first)?;
                    Self::meta_help(&name);
                }
                ExprTag::Sym => {
                    let sym = repl.get_symbol(&first)?;
                    let name = sym.path().last().unwrap();
                    Self::meta_help(name);
                }
                ExprTag::Nil => {
                    use itertools::Itertools;
                    println!("Available commands:");
                    for (_, i) in MetaCmd::cmds().iter().sorted_by_key(|x| x.0) {
                        println!("  {} - {}", i.name, i.summary);
                    }
                }
                _ => bail!("The optional argument of `help` must be a string or symbol"),
            }
            return Ok(());
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
                if i.example.len() > 0 {
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
    const CMDS: [MetaCmd<F>; 19] = [
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
    ];

    pub(super) fn cmds() -> std::collections::HashMap<&'static str, MetaCmd<F>> {
        return std::collections::HashMap::from(Self::CMDS.map(|x| (x.name, x)));
    }
}
