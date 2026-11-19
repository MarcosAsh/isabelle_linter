//! Commands that prove nothing but run on every build. Their times come from loading the file.

use crate::lint::{Answers, Finding, Lint, Options};
use crate::protocol::{Decl, Diagnostic, Edit, File, Question};

pub struct DiagnosticCommands;

/// Exploration is only of use while writing a proof, so its fix deletes it. A test may be meant,
/// and what only prints may document something, so those are reported and kept.
fn finding(command: &Diagnostic) -> Finding {
    let advice = match command.category.as_str() {
        "exploration" => "only of use while writing a proof",
        "test" => "checks something, so it could move to a test file",
        _ => "only prints",
    };
    let edits = match command.category.as_str() {
        "exploration" => vec![Edit {
            range: command.range,
            text: String::new(),
        }],
        _ => Vec::new(),
    };
    Finding {
        lint: "diagnostic_commands".to_string(),
        decl: String::new(),
        line: command.line,
        message: format!(
            "`{}` takes {} ms on every build and proves nothing ({advice})",
            command.text, command.ms
        ),
        edits,
    }
}

impl Lint for DiagnosticCommands {
    fn name(&self) -> &'static str {
        "diagnostic_commands"
    }

    fn ask(&self, _decls: &[Decl], _answers: &Answers, _options: &Options) -> Vec<Question> {
        Vec::new()
    }

    fn report(&self, _decls: &[Decl], _answers: &Answers, _options: &Options) -> Vec<Finding> {
        Vec::new()
    }

    fn read(&self, file: &File) -> Vec<Finding> {
        file.diagnostics.iter().map(finding).collect()
    }
}
