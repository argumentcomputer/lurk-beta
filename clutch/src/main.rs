use anyhow::Result;
use lurk::field::{LanguageField, LurkField};
use lurk::package::Package;
use lurk::proof::nova;
use lurk::repl::{repl, ReplState, ReplTrait};
use lurk::store::{Expression, Ptr, Store};
use lurk::writer::Write;
use std::io;
use std::path::Path;

struct ClutchState<F: LurkField>(ReplState<F>);

impl<F: LurkField> ReplTrait<F> for ClutchState<F> {
    fn new(s: &mut Store<F>, limit: usize) -> Self {
        Self(ReplState::new(s, limit))
    }

    fn handle_run<P: AsRef<Path> + Copy>(
        &mut self,
        store: &mut Store<F>,
        file_path: P,
        package: &Package,
    ) -> Result<()> {
        self.0.handle_run(store, file_path, package)
    }

    /// Returns two bools.
    /// First bool is true if input is a command.
    /// Second bool is true if processing should continue.
    fn maybe_handle_command(
        &mut self,
        store: &mut Store<F>,
        line: &str,
        package: &Package,
    ) -> Result<(bool, bool)> {
        self.0.maybe_handle_command(store, line, package)
    }

    fn handle_meta<P: AsRef<Path> + Copy>(
        &mut self,
        store: &mut Store<F>,
        expr_ptr: Ptr<F>,
        package: &Package,
        p: P,
    ) -> Result<()> {
        let expr = store.fetch(&expr_ptr).unwrap();

        macro_rules! delegate {
            () => {
                self.0.handle_meta(store, expr_ptr, package, p)
            };
        }

        let res: Option<Ptr<F>> = match expr {
            Expression::Cons(car, _rest) => match &store.fetch(&car).unwrap() {
                Expression::Sym(s) => {
                    if let Some(name) = s.simple_keyword_name() {
                        match name.as_str() {
                            "XXX" => {
                                println!("BOOM");
                                None
                            }
                            _ => return delegate!(),
                        }
                    } else {
                        return delegate!();
                    }
                }
                _ => return delegate!(),
            },
            _ => return delegate!(),
        };

        if let Some(expr) = res {
            let mut handle = io::stdout().lock();
            expr.fmt(store, &mut handle)?;
            println!();
        };
        Ok(())
    }

    fn handle_non_meta(
        &mut self,
        store: &mut Store<F>,
        expr_ptr: Ptr<F>,
        update_env: bool,
    ) -> Result<()> {
        self.0.handle_non_meta(store, expr_ptr, update_env)
    }
}

fn main() -> Result<()> {
    pretty_env_logger::init();

    // If an argument is passed, treat is as a Lurk file to run.
    let mut args = std::env::args();
    let lurk_file = if args.len() > 1 {
        Some(args.nth(1).expect("Lurk file missing"))
    } else {
        None
    };

    let default_field = LanguageField::Pallas;
    let field = if let Ok(lurk_field) = std::env::var("LURK_FIELD") {
        match lurk_field.as_str() {
            "BLS12-381" => LanguageField::BLS12_381,
            "PALLAS" => LanguageField::Pallas,
            "VESTA" => LanguageField::Vesta,
            _ => default_field,
        }
    } else {
        default_field
    };

    match field {
        LanguageField::BLS12_381 => {
            repl::<_, blstrs::Scalar, ClutchState<blstrs::Scalar>>(lurk_file.as_deref())
        }
        LanguageField::Pallas => repl::<_, nova::S1, ClutchState<nova::S1>>(lurk_file.as_deref()),
        LanguageField::Vesta => repl::<_, nova::S2, ClutchState<nova::S2>>(lurk_file.as_deref()),
    }
}
