use anyhow::{bail, Result};
use camino::Utf8PathBuf;
use rustyline::{
    history::DefaultHistory,
    validate::{MatchingBracketValidator, ValidationContext, ValidationResult, Validator},
    Config, Editor,
};
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};

use crate::field::LurkField;

use super::backend::Backend;

#[derive(Completer, Helper, Highlighter, Hinter)]
pub(crate) struct InputValidator {
    pub(crate) brackets: MatchingBracketValidator,
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
pub(crate) fn pad(a: usize, m: usize) -> usize {
    (a + m - 1) / m * m
}

/// Errors if the valua provided is zero
pub(crate) fn validate_non_zero(name: &str, x: usize) -> Result<()> {
    if x == 0 {
        bail!("`{name}` can't be zero")
    }
    Ok(())
}

/// Nice formatting to display the number of iterations
pub(crate) fn pretty_iterations_display(iterations: usize) -> String {
    if iterations != 1 {
        format!("{iterations} iterations")
    } else {
        "1 iteration".into()
    }
}

/// Formats the proof key
pub(crate) fn proof_key<F: LurkField>(backend: &Backend, rc: &usize, claim_hash: &str) -> String {
    let field = F::FIELD;
    format!("{backend}_{field}_{rc}_{claim_hash}")
}

/// Returns the PWD path, the history path and the REPL editor
pub(crate) fn get_repl_setup() -> Result<(
    Utf8PathBuf,
    Utf8PathBuf,
    Editor<InputValidator, DefaultHistory>,
)> {
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

    let history_path = crate::cli::paths::repl_history();

    if history_path.exists() {
        editor.load_history(&history_path)?;
    }

    Ok((pwd_path, history_path, editor))
}

mod test {
    #[test]
    fn test_padding() {
        use crate::cli::repl_aux::pad;
        assert_eq!(pad(61, 10), 70);
        assert_eq!(pad(1, 10), 10);
        assert_eq!(pad(61, 1), 61);
        assert_eq!(pad(610, 10), 610);
        assert_eq!(pad(619, 20), 620);
    }
}
