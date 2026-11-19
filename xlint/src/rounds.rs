//! Ask a lint's questions in rounds and keep a log of every question and answer.

use crate::lint::{Answers, Lint, Options};
use crate::protocol::{Answer, Ask, Decl, Question};
use crate::prover::{Prover, Result};
use std::collections::HashSet;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;

pub fn run(
    prover: &mut dyn Prover,
    lint: &dyn Lint,
    decls: &[Decl],
    options: &Options,
    log: Option<&Path>,
) -> Result<Answers> {
    let mut answers = Answers::new();
    loop {
        let mut seen = HashSet::new();
        let round: Vec<Question> = lint
            .ask(decls, &answers, options)
            .into_iter()
            .filter(|q| !answers.contains_key(&q.key) && seen.insert(q.key.clone()))
            .collect();
        if round.is_empty() {
            return Ok(answers);
        }
        let (serial, parallel): (Vec<Question>, Vec<Question>) =
            round.into_iter().partition(|q| q.serial);
        eprintln!(
            "{}: asking {} questions, {} one at a time",
            lint.name(),
            serial.len() + parallel.len(),
            serial.len()
        );
        for batch in parallel.chunks(options.batch.max(1)) {
            ask(prover, lint.name(), batch, &mut answers, log)?;
        }
        for question in &serial {
            ask(
                prover,
                lint.name(),
                std::slice::from_ref(question),
                &mut answers,
                log,
            )?;
        }
    }
}

/// A question the server did not answer counts as unanswered, so the lint does not ask it forever.
fn ask(
    prover: &mut dyn Prover,
    lint: &str,
    batch: &[Question],
    answers: &mut Answers,
    log: Option<&Path>,
) -> Result<()> {
    let asked = prover.ask(batch);
    for answer in asked.as_deref().unwrap_or(&[]) {
        answers.insert(answer.key.clone(), answer.clone());
    }
    for question in batch {
        answers
            .entry(question.key.clone())
            .or_insert_with(|| Answer::unanswered(&question.key));
    }
    if let Some(path) = log {
        write_log(path, lint, batch, answers)
            .map_err(|e| format!("cannot write {}: {e}", path.display()))?;
    }
    asked.map(|_| ())
}

/// One TSV row per question: lint, key, what was asked, verdict, times.
fn write_log(
    path: &Path,
    lint: &str,
    batch: &[Question],
    answers: &Answers,
) -> std::io::Result<()> {
    let clean = |s: &str| s.replace(['\t', '\n'], " ");
    let mut file = OpenOptions::new().create(true).append(true).open(path)?;
    for question in batch {
        let answer = &answers[&question.key];
        let asked = match &question.ask {
            Ask::Run { edits } => {
                let edits: Vec<String> = edits
                    .iter()
                    .map(|e| format!("{}-{}:{}", e.range.start, e.range.stop, e.text))
                    .collect();
                format!("run {}", edits.join(" | "))
            }
            Ask::Step { step, text } => format!("step {step} {text}"),
            Ask::Suggest { step } => format!("suggest {step} {}", answer.suggestions.join(" | ")),
        };
        let ms: Vec<String> = answer.ms.iter().map(u64::to_string).collect();
        writeln!(
            file,
            "{lint}\t{}\t{}\t{}\t{}\t{}",
            clean(&question.key),
            clean(&asked),
            answer.verdict,
            ms.join(","),
            clean(&answer.message)
        )?;
    }
    Ok(())
}
