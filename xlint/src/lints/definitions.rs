//! Parts of a definition the file does not need, like a derived instance, or that have a cheaper
//! form, like a termination proof for structural recursion. The fix is checked on the whole file.

use crate::lint::{Answers, Finding, Lint, Options};
use crate::lints::unused::{IMPORTS, joined};
use crate::protocol::{Answer, Ask, Decl, Edit, Question};

pub struct Definitions;

/// Other files may use what a `public` piece makes, so its fix is only reported.
fn reported_only(kind: &str) -> bool {
    kind.starts_with("public ")
}

/// The pieces to change, with the median ms of the definition as written and with the fix.
struct Fix {
    edits: Vec<(usize, Edit)>,
    before: u64,
    after: u64,
}

struct Search<'a> {
    decl: &'a Decl,
    /// The declaration a run of which checks the whole file.
    file: Option<&'a Decl>,
    answers: &'a Answers,
    options: &'a Options,
}

fn texts(edits: &[(usize, Edit)]) -> Vec<Edit> {
    let (deleted, replaced): (Vec<Edit>, Vec<Edit>) = edits
        .iter()
        .map(|(_, e)| e.clone())
        .partition(|e| e.text.is_empty());
    let mut all = joined(deleted.iter().map(|e| e.range).collect());
    all.extend(replaced);
    all
}

impl Search<'_> {
    fn run(&self, on: &Decl, what: &str, edits: &[(usize, Edit)], timeout_ms: u64) -> Question {
        Question {
            key: format!("{}:definition:{what}", self.decl.key),
            decl: on.key.clone(),
            ask: Ask::Run {
                edits: texts(edits),
            },
            timeout_ms,
            runs: 1,
            serial: false,
        }
    }

    fn answered(&self, questions: Vec<Question>) -> Result<Vec<&Answer>, Vec<Question>> {
        let (known, missing): (Vec<Question>, Vec<Question>) = questions
            .into_iter()
            .partition(|q| self.answers.contains_key(&q.key));
        if missing.is_empty() {
            Ok(known.iter().map(|q| &self.answers[&q.key]).collect())
        } else {
            Err(missing)
        }
    }

    /// Per piece, its first replacement the definition still checks with; then the file.
    fn check(&self) -> Result<Option<Fix>, Vec<Question>> {
        let decl = self.decl;
        let original = self.run(decl, "original", &[], self.options.timeout_ms);
        let original = self.answered(vec![original])?[0];
        if !original.closes() {
            return Ok(None);
        }
        let budget_ms = self.options.budget_ms(original);
        let tries: Vec<(usize, Edit)> = decl
            .pieces
            .iter()
            .enumerate()
            .flat_map(|(i, piece)| {
                piece.replacements.iter().map(move |text| {
                    let (range, text) = (piece.range, text.clone());
                    (i, Edit { range, text })
                })
            })
            .collect();
        let one = |n: usize| self.run(decl, &format!("try:{n}"), &tries[n..=n], budget_ms);
        let tried = self.answered((0..tries.len()).map(one).collect())?;
        let mut working: Vec<(usize, Edit)> = Vec::new();
        for (edit, answer) in tries.iter().zip(tried) {
            if answer.closes() && working.iter().all(|(piece, _)| *piece != edit.0) {
                working.push(edit.clone());
            }
        }
        let kept = self.in_file(working)?;
        if kept.is_empty() {
            return Ok(None);
        }
        let timing = |what: &str, edits: &[(usize, Edit)]| Question {
            runs: self.options.runs,
            serial: true,
            ..self.run(decl, what, edits, budget_ms)
        };
        let times = self.answered(vec![
            timing("time:before", &[]),
            timing("time:after", &kept),
        ])?;
        Ok((times[0].closes() && times[1].closes()).then(|| Fix {
            edits: kept,
            before: times[0].median_ms(),
            after: times[1].median_ms(),
        }))
    }

    /// All at once, else those the file checks with alone, else the first of them.
    fn in_file(&self, edits: Vec<(usize, Edit)>) -> Result<Vec<(usize, Edit)>, Vec<Question>> {
        let Some(file) = self.file else {
            return Ok(edits);
        };
        if edits.is_empty() {
            return Ok(edits);
        }
        let timeout_ms = self.options.timeout_ms;
        if self.answered(vec![self.run(file, "file:all", &edits, timeout_ms)])?[0].closes() {
            return Ok(edits);
        }
        if edits.len() == 1 {
            return Ok(Vec::new());
        }
        let one = |n: usize| self.run(file, &format!("file:{n}"), &edits[n..=n], timeout_ms);
        let alone = self.answered((0..edits.len()).map(one).collect())?;
        let working: Vec<(usize, Edit)> = edits
            .into_iter()
            .zip(alone)
            .filter(|(_, a)| a.closes())
            .map(|(e, _)| e)
            .collect();
        if working.len() < 2
            || self.answered(vec![self.run(file, "file:working", &working, timeout_ms)])?[0]
                .closes()
        {
            return Ok(working);
        }
        Ok(working.into_iter().take(1).collect())
    }
}

fn searches<'a>(
    decls: &'a [Decl],
    answers: &'a Answers,
    options: &'a Options,
) -> impl Iterator<Item = Search<'a>> {
    let file = decls.iter().find(|d| d.kind == IMPORTS);
    decls
        .iter()
        .filter(|d| d.ok && d.kind == "definition")
        .map(move |decl| Search {
            decl,
            file,
            answers,
            options,
        })
}

impl Lint for Definitions {
    fn name(&self) -> &'static str {
        "definitions"
    }

    fn ask(&self, decls: &[Decl], answers: &Answers, options: &Options) -> Vec<Question> {
        searches(decls, answers, options)
            .flat_map(|s| s.check().err().unwrap_or_default())
            .collect()
    }

    fn report(&self, decls: &[Decl], answers: &Answers, options: &Options) -> Vec<Finding> {
        searches(decls, answers, options)
            .filter_map(|s| {
                let fix = s.check().ok().flatten()?;
                let mut lines = vec![format!(
                    "`{}` takes {} ms instead of {} ms (medians, alone), and the file still checks, with:",
                    s.decl.name, fix.after, fix.before
                )];
                for (i, edit) in &fix.edits {
                    let piece = &s.decl.pieces[*i];
                    let change = match edit.text.as_str() {
                        "" => "removed".to_string(),
                        text => format!("replaced by `{text}`"),
                    };
                    let note = match reported_only(&piece.kind) {
                        true => " (not fixed: the files that import this one were not checked)",
                        false => "",
                    };
                    lines.push(format!(
                        "  {} `{}` (line {}) {change}{note}",
                        piece.kind, piece.text, piece.line
                    ));
                }
                let fixed: Vec<(usize, Edit)> = fix
                    .edits
                    .into_iter()
                    .filter(|(i, _)| !reported_only(&s.decl.pieces[*i].kind))
                    .collect();
                Some(Finding {
                    lint: self.name().to_string(),
                    decl: s.decl.key.clone(),
                    line: s.decl.line,
                    message: lines.join("\n"),
                    edits: texts(&fixed),
                })
            })
            .collect()
    }
}
