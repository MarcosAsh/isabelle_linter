//! `faster_step` against a prover that knows how long each text takes on a step.

use std::collections::HashMap;
use xlint::lint::{Lint, Options};
use xlint::lints::faster_step::FasterStep;
use xlint::protocol::{Answer, Ask, Decl, File, Hello, Question, Range, Step};
use xlint::prover::{Prover, Result};
use xlint::{fix, rounds};

const SOURCE: &str = "theorem t : goal := by slow";

/// Texts that close the step, with their ms. A whole-declaration check fails for `broken`.
struct Fake {
    ms: HashMap<&'static str, u64>,
    suggestions: Vec<String>,
    broken: &'static str,
}

impl Prover for Fake {
    fn hello(&mut self) -> Result<Hello> {
        Ok(Hello::default())
    }

    fn load(&mut self, _file: &str) -> Result<File> {
        let start = SOURCE.find("slow").unwrap();
        let step = Step {
            text: "slow".to_string(),
            range: Range {
                start,
                stop: SOURCE.len(),
            },
            line: 1,
            candidates: vec![
                "quick".to_string(),
                "quicker".to_string(),
                "wrong".to_string(),
                "slower".to_string(),
            ],
        };
        let range = Range {
            start: 0,
            stop: SOURCE.len(),
        };
        let decl = Decl {
            key: "T:0".into(),
            name: "t".into(),
            kind: String::new(),
            range,
            line: 1,
            ok: true,
            steps: vec![step],
            pieces: vec![],
        };
        Ok(File {
            decls: vec![decl],
            diagnostics: Vec::new(),
        })
    }

    fn ask(&mut self, questions: &[Question]) -> Result<Vec<Answer>> {
        Ok(questions.iter().map(|q| self.answer(q)).collect())
    }
}

impl Fake {
    fn answer(&self, question: &Question) -> Answer {
        let mut answer = Answer::unanswered(&question.key);
        match &question.ask {
            Ask::Suggest { .. } => {
                answer.verdict = "closes".to_string();
                answer.suggestions = self.suggestions.clone();
            }
            Ask::Step { text, .. } => match self.ms.get(text.as_str()) {
                Some(&ms) if ms <= question.timeout_ms => {
                    answer.verdict = "closes".to_string();
                    answer.ms = vec![ms; question.runs as usize];
                }
                Some(_) => answer.verdict = "timeout".to_string(),
                None => answer.verdict = "fails".to_string(),
            },
            Ask::Stats => {}
            Ask::Run { edits } => {
                let closes = edits.iter().all(|e| e.text != self.broken);
                answer.verdict = if closes { "closes" } else { "fails" }.to_string();
            }
        }
        answer
    }
}

fn lint(prover: &mut Fake) -> Vec<xlint::lint::Finding> {
    let decls = prover.load("T").unwrap().decls;
    let options = Options::default();
    let answers = rounds::run(prover, &FasterStep, &decls, &options, None).unwrap();
    FasterStep.report(&decls, &answers, &options)
}

fn fake(ms: &[(&'static str, u64)]) -> Fake {
    Fake {
        ms: ms.iter().copied().collect(),
        suggestions: Vec::new(),
        broken: "",
    }
}

#[test]
fn the_fastest_candidate_replaces_a_slow_step() {
    let findings = lint(&mut fake(&[
        ("slow", 4000),
        ("quick", 900),
        ("quicker", 300),
        ("slower", 9000),
    ]));
    assert_eq!(findings.len(), 1);
    assert_eq!(
        findings[0].message,
        "`quicker` takes 300 ms instead of 4000 ms for `slow`"
    );
    assert_eq!(
        fix::apply(SOURCE, &findings[0].edits).unwrap(),
        "theorem t : goal := by quicker"
    );
}

#[test]
fn a_fast_step_is_left_alone() {
    assert!(lint(&mut fake(&[("slow", 500), ("quick", 1)])).is_empty());
}

#[test]
fn a_candidate_under_twice_as_fast_is_not_enough() {
    assert!(lint(&mut fake(&[("slow", 4000), ("quick", 2500)])).is_empty());
}

#[test]
fn the_prover_can_suggest_candidates() {
    let mut prover = fake(&[("slow", 4000), ("simp only [a]", 100)]);
    prover.suggestions = vec!["simp only [a]".to_string()];
    assert_eq!(lint(&mut prover)[0].edits[0].text, "simp only [a]");
}

#[test]
fn a_replacement_that_breaks_the_declaration_is_dropped() {
    let mut prover = fake(&[("slow", 4000), ("quick", 100)]);
    prover.broken = "quick";
    assert!(lint(&mut prover).is_empty());
}
