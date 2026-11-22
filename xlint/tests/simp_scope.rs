//! `simp_scope` against a prover where each narrowed call saves a fixed time or breaks the proof.

use xlint::lint::{Finding, Lint, Options};
use xlint::lints::simp_scope::SimpScope;
use xlint::protocol::{Answer, Ask, Decl, File, Hello, Question, Range, Step};
use xlint::prover::{Prover, Result};
use xlint::{fix, rounds};

const SOURCE: &str = "theorem t : goal := by\n  simp at h\n  simp [a]\n  simp";

/// Per call: the ms narrowing it saves, or None if it breaks the proof. The proof takes `ms`.
struct Fake {
    ms: u64,
    saves: Vec<Option<u64>>,
    /// Narrowing more than one call at once breaks the proof.
    clash: bool,
}

fn call(text: &str, after: usize) -> Step {
    let start = after + SOURCE[after..].find(text).unwrap();
    Step {
        text: text.to_string(),
        range: Range {
            start,
            stop: start + text.len(),
        },
        line: 1 + SOURCE[..start].matches('\n').count(),
        candidates: Vec::new(),
    }
}

fn simps() -> Vec<Step> {
    let first = call("simp at h", 0);
    let second = call("simp [a]", first.range.stop);
    let third = call("simp", second.range.stop);
    vec![first, second, third]
}

impl Prover for Fake {
    fn hello(&mut self) -> Result<Hello> {
        Ok(Hello::default())
    }

    fn load(&mut self, _file: &str) -> Result<File> {
        let decl = Decl {
            key: "T:0".into(),
            name: "t".into(),
            kind: "theorem".into(),
            range: Range {
                start: 0,
                stop: SOURCE.len(),
            },
            line: 1,
            ok: true,
            steps: Vec::new(),
            simps: simps(),
            pieces: Vec::new(),
        };
        Ok(File {
            decls: vec![decl],
            diagnostics: Vec::new(),
            commands: Vec::new(),
        })
    }

    fn ask(&mut self, questions: &[Question]) -> Result<Vec<Answer>> {
        Ok(questions.iter().map(|q| self.answer(q)).collect())
    }
}

impl Fake {
    fn answer(&self, question: &Question) -> Answer {
        let mut answer = Answer::unanswered(&question.key);
        answer.verdict = "closes".to_string();
        match &question.ask {
            Ask::Narrow { call } => {
                answer.suggestions = vec![format!("simp only [r{call}]")];
            }
            Ask::Run { edits } => {
                let calls: Vec<usize> = edits
                    .iter()
                    .map(|e| simps().iter().position(|s| s.range == e.range).unwrap())
                    .collect();
                let saved: Option<u64> = calls.iter().map(|&c| self.saves[c]).sum();
                match saved {
                    Some(saved) if !(self.clash && calls.len() > 1) => {
                        answer.ms = vec![self.ms - saved; question.runs as usize]
                    }
                    _ => answer.verdict = "fails".to_string(),
                }
            }
            _ => answer.verdict = "error".to_string(),
        }
        answer
    }
}

fn lint(mut prover: Fake) -> Vec<Finding> {
    let decls = prover.load("T").unwrap().decls;
    let options = Options::default();
    let answers = rounds::run(&mut prover, &SimpScope, &decls, &options, None).unwrap();
    SimpScope.report(&decls, &answers, &options)
}

#[test]
fn every_call_is_narrowed_when_the_proof_still_checks() {
    let findings = lint(Fake {
        ms: 3000,
        saves: vec![Some(500), Some(500), Some(500)],
        clash: false,
    });
    assert_eq!(findings.len(), 1);
    assert!(
        findings[0]
            .message
            .starts_with("1500 ms instead of 3000 ms")
    );
    assert_eq!(
        fix::apply(SOURCE, &findings[0].edits).unwrap(),
        "theorem t : goal := by\n  simp only [r0]\n  simp only [r1]\n  simp only [r2]"
    );
}

#[test]
fn a_call_that_breaks_the_proof_narrowed_stays() {
    let findings = lint(Fake {
        ms: 3000,
        saves: vec![Some(900), None, Some(300)],
        clash: false,
    });
    assert_eq!(
        fix::apply(SOURCE, &findings[0].edits).unwrap(),
        "theorem t : goal := by\n  simp only [r0]\n  simp [a]\n  simp only [r2]"
    );
}

#[test]
fn calls_that_only_work_alone_leave_the_one_that_saves_most() {
    let findings = lint(Fake {
        ms: 3000,
        saves: vec![Some(600), Some(900), Some(300)],
        clash: true,
    });
    assert_eq!(
        fix::apply(SOURCE, &findings[0].edits).unwrap(),
        "theorem t : goal := by\n  simp at h\n  simp only [r1]\n  simp"
    );
}

#[test]
fn a_fast_proof_and_a_small_saving_are_left_alone() {
    assert!(
        lint(Fake {
            ms: 800,
            saves: vec![Some(500), Some(100), Some(100)],
            clash: false
        })
        .is_empty()
    );
    assert!(
        lint(Fake {
            ms: 3000,
            saves: vec![Some(100), Some(100), Some(100)],
            clash: false
        })
        .is_empty()
    );
}
