//! `unused` against a prover that knows which pieces each declaration needs.

use std::collections::HashMap;
use xlint::lint::{Lint, Options};
use xlint::lints::unused::Unused;
use xlint::protocol::{Answer, Ask, Decl, File, Hello, Piece, Question, Range};
use xlint::prover::{Prover, Result};
use xlint::{fix, rounds};

/// A declaration closes if every dropped piece is unneeded, and `frees` pieces become unneeded
/// once the piece that used them is dropped.
struct Fake {
    decls: Vec<Decl>,
    needed: HashMap<String, Vec<usize>>,
    frees: HashMap<String, Vec<(usize, usize)>>,
    asked: usize,
}

impl Prover for Fake {
    fn hello(&mut self) -> Result<Hello> {
        Ok(Hello::default())
    }

    fn load(&mut self, _file: &str) -> Result<File> {
        Ok(File {
            decls: self.decls.clone(),
            diagnostics: Vec::new(),
        })
    }

    fn ask(&mut self, questions: &[Question]) -> Result<Vec<Answer>> {
        self.asked += questions.len();
        Ok(questions.iter().map(|q| self.answer(q)).collect())
    }
}

impl Fake {
    fn answer(&self, question: &Question) -> Answer {
        let decl = self.decls.iter().find(|d| d.key == question.decl).unwrap();
        let Ask::Run { edits } = &question.ask else {
            panic!("unused only runs declarations")
        };
        let dropped: Vec<usize> = (0..decl.pieces.len())
            .filter(|&i| {
                edits
                    .iter()
                    .any(|e| e.range.contains(&decl.pieces[i].range))
            })
            .collect();
        let freed = |i: &usize| {
            self.frees.get(&decl.key).is_some_and(|f| {
                f.iter()
                    .any(|(user, used)| used == i && dropped.contains(user))
            })
        };
        let fails = dropped
            .iter()
            .any(|i| self.needed[&decl.key].contains(i) && !freed(i));
        let ms = vec![if dropped.is_empty() { 40 } else { 30 }; question.runs as usize];
        Answer {
            key: question.key.clone(),
            verdict: if fails { "fails" } else { "closes" }.to_string(),
            ms,
            message: String::new(),
            suggestions: Vec::new(),
            rules: Vec::new(),
        }
    }
}

fn piece(kind: &str, text: &str, start: usize) -> Piece {
    Piece {
        kind: kind.to_string(),
        text: text.to_string(),
        range: Range {
            start,
            stop: start + text.len(),
        },
        line: 1,
    }
}

fn decl(key: &str, source: &str, pieces: &[(&str, &str)]) -> Decl {
    let pieces = pieces
        .iter()
        .map(|(kind, text)| {
            piece(
                kind,
                text,
                if *kind == "fact" {
                    source.rfind(text)
                } else {
                    source.find(text)
                }
                .unwrap(),
            )
        })
        .collect();
    Decl {
        key: key.to_string(),
        name: key.to_string(),
        kind: String::new(),
        range: Range {
            start: 0,
            stop: source.len(),
        },
        line: 1,
        ok: true,
        steps: Vec::new(),
        simps: Vec::new(),
        pieces,
    }
}

const SOURCE: &str = "lemma l: assumes a shows g proof - have h1 by x have h2 using h1 by y show g using h2 f1 f2 by z qed";

fn fake(needed: &[usize], frees: &[(usize, usize)]) -> Fake {
    let pieces = [
        ("assumption", "assumes a "),
        ("have", "have h1 by x "),
        ("have", "have h2 using h1 by y "),
        ("fact", "h2 "),
        ("fact", "f1 "),
        ("fact", "f2 "),
    ];
    let d = decl("T:0", SOURCE, &pieces);
    Fake {
        needed: HashMap::from([(d.key.clone(), needed.to_vec())]),
        frees: HashMap::from([(d.key.clone(), frees.to_vec())]),
        decls: vec![d],
        asked: 0,
    }
}

fn lint(prover: &mut Fake) -> Vec<xlint::lint::Finding> {
    let decls = prover.load("T").unwrap().decls;
    let options = Options::default();
    let answers = rounds::run(prover, &Unused, &decls, &options, None).unwrap();
    Unused.report(&decls, &answers, &options)
}

#[test]
fn nothing_to_remove() {
    assert!(lint(&mut fake(&[0, 1, 2, 3, 4, 5], &[])).is_empty());
}

#[test]
fn removes_what_is_unneeded_and_reports_assumptions() {
    // f1 is not needed, and neither is the assumption; the rest is
    let findings = lint(&mut fake(&[1, 2, 3, 5], &[]));
    assert_eq!(findings.len(), 1);
    let message = &findings[0].message;
    assert!(message.contains("not needed:\n  fact `f1 `"), "{message}");
    assert!(
        message.contains("time: 40 ms as written, 30 ms with the fix"),
        "{message}"
    );
    assert!(
        message.contains("changes the statement:\n  assumption `assumes a `"),
        "{message}"
    );
    let fixed = fix::apply(SOURCE, &findings[0].edits).unwrap();
    assert_eq!(fixed, SOURCE.replace("f1 ", ""));
}

#[test]
fn a_dropped_fact_frees_the_haves_behind_it() {
    // h2 is not needed in the last step, and without it have h2 can go
    let findings = lint(&mut fake(&[0, 1, 2, 4, 5], &[(3, 2)]));
    let fixed = fix::apply(SOURCE, &findings[0].edits).unwrap();
    assert_eq!(
        fixed,
        "lemma l: assumes a shows g proof - have h1 by x show g using f1 f2 by z qed"
    );
}

#[test]
fn pieces_that_only_go_alone_are_taken_one_by_one() {
    // f1 or f2 can go, but not both, so the first one goes
    let mut prover = fake(&[0, 1, 2, 3], &[]);
    prover.needed.insert("T:0".to_string(), vec![0, 1, 2, 3]);
    let d = prover.decls[0].clone();
    struct Either(Fake);
    impl Prover for Either {
        fn hello(&mut self) -> Result<Hello> {
            self.0.hello()
        }
        fn load(&mut self, file: &str) -> Result<File> {
            self.0.load(file)
        }
        fn ask(&mut self, questions: &[Question]) -> Result<Vec<Answer>> {
            let mut answers = self.0.ask(questions)?;
            for (answer, question) in answers.iter_mut().zip(questions) {
                let Ask::Run { edits } = &question.ask else {
                    unreachable!()
                };
                let both = [4, 5].iter().all(|&i| {
                    edits
                        .iter()
                        .any(|e| e.range.contains(&self.0.decls[0].pieces[i].range))
                });
                if both {
                    answer.verdict = "fails".to_string();
                }
            }
            Ok(answers)
        }
    }
    let mut prover = Either(prover);
    let options = Options::default();
    let answers = rounds::run(
        &mut prover,
        &Unused,
        std::slice::from_ref(&d),
        &options,
        None,
    )
    .unwrap();
    let findings = Unused.report(&[d], &answers, &options);
    assert_eq!(
        fix::apply(SOURCE, &findings[0].edits).unwrap(),
        SOURCE.replace("f1 ", "")
    );
}

#[test]
fn overlapping_edits_are_refused() {
    let edits = [
        xlint::protocol::Edit {
            range: Range { start: 0, stop: 5 },
            text: String::new(),
        },
        xlint::protocol::Edit {
            range: Range { start: 3, stop: 8 },
            text: String::new(),
        },
    ];
    assert!(fix::apply(SOURCE, &edits).is_err());
}
