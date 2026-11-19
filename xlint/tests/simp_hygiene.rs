//! `simp_hygiene` against a prover that returns fixed rule counts per theorem.

use xlint::lint::{Lint, Options};
use xlint::lints::simp_hygiene::SimpHygiene;
use xlint::protocol::{Answer, Decl, File, Hello, Question, Range, Rule};
use xlint::prover::{Prover, Result};
use xlint::rounds;

struct Fake;

fn theorem(name: &str, line: usize) -> Decl {
    Decl {
        key: format!("T:{line}"),
        name: name.to_string(),
        kind: "theorem".to_string(),
        range: Range { start: 0, stop: 0 },
        line,
        ok: true,
        steps: Vec::new(),
        simps: Vec::new(),
        pieces: Vec::new(),
    }
}

fn rule(name: &str, tried: u64, used: u64) -> Rule {
    Rule {
        name: name.to_string(),
        tried,
        used,
    }
}

impl Prover for Fake {
    fn hello(&mut self) -> Result<Hello> {
        Ok(Hello::default())
    }

    fn load(&mut self, _file: &str) -> Result<File> {
        Ok(File {
            decls: vec![
                theorem("dead", 1),
                theorem("first", 5),
                theorem("second", 9),
            ],
            diagnostics: Vec::new(),
        })
    }

    /// `second` tries the rules more often than `first`; `dead` uses no simp.
    fn ask(&mut self, questions: &[Question]) -> Result<Vec<Answer>> {
        Ok(questions
            .iter()
            .map(|q| {
                let mut answer = Answer::unanswered(&q.key);
                answer.verdict = "closes".to_string();
                answer.rules = match q.decl.as_str() {
                    "T:5" => vec![rule("Ns.dead", 40, 0), rule("Lib.rare", 100, 5)],
                    "T:9" => vec![
                        rule("Ns.dead", 80, 0),
                        rule("Lib.rare", 200, 5),
                        rule("Lib.good", 500, 400),
                        rule("Lib.few", 20, 0),
                    ],
                    _ => Vec::new(),
                };
                answer
            })
            .collect())
    }
}

#[test]
fn rules_tried_often_for_nothing_are_reported_where_they_are_declared_or_tried_most() {
    let decls = Fake.load("T").unwrap().decls;
    let options = Options::default();
    let answers = rounds::run(&mut Fake, &SimpHygiene, &decls, &options, None).unwrap();
    let findings = SimpHygiene.report(&decls, &answers, &options);
    let lines: Vec<(usize, &str)> = findings
        .iter()
        .map(|f| (f.line, f.message.lines().next().unwrap()))
        .collect();
    assert_eq!(
        lines,
        vec![
            (
                9,
                "simp rule `Lib.rare` tried 300 times in 2 theorems, rewrote 10 times"
            ),
            (
                1,
                "simp rule `Ns.dead` tried 120 times in 2 theorems, never rewrote"
            ),
        ]
    );
    assert!(findings.iter().all(|f| f.edits.is_empty()));
    assert!(findings[0].message.contains("counted over 3 of 3 theorems"));
}
