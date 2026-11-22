//! `definitions` against a prover where some replacements break the definition or the file.

use xlint::lint::{Finding, Lint, Options};
use xlint::lints::definitions::Definitions;
use xlint::protocol::{Answer, Ask, Decl, File, Hello, Piece, Question, Range};
use xlint::prover::{Prover, Result};
use xlint::{fix, rounds};

const SOURCE: &str = "import A\ntype T deriving Show, Eq\ndef f n := g n\nby_measure n";

/// Texts the definition does not check with, and deleted texts the rest of the file needs.
struct Fake {
    broken: Vec<&'static str>,
    used_later: Vec<&'static str>,
}

fn range(text: &str) -> Range {
    let start = SOURCE.find(text).unwrap();
    Range {
        start,
        stop: start + text.len(),
    }
}

fn piece(kind: &str, text: &str, deleted: &str, replacements: &[&str]) -> Piece {
    Piece {
        kind: kind.to_string(),
        text: text.to_string(),
        range: range(deleted),
        line: 1 + SOURCE[..range(deleted).start].matches('\n').count(),
        replacements: replacements.iter().map(|r| r.to_string()).collect(),
    }
}

fn decl(kind: &str, name: &str, text: &str, pieces: Vec<Piece>) -> Decl {
    Decl {
        key: format!("T:{name}"),
        name: name.to_string(),
        kind: kind.to_string(),
        range: range(text),
        line: 1 + SOURCE[..range(text).start].matches('\n').count(),
        ok: true,
        steps: Vec::new(),
        simps: Vec::new(),
        pieces,
    }
}

impl Prover for Fake {
    fn hello(&mut self) -> Result<Hello> {
        Ok(Hello::default())
    }

    fn load(&mut self, _file: &str) -> Result<File> {
        let handlers = vec![
            piece("public deriving", "Show", "Show, ", &[""]),
            piece("deriving", "Eq", ", Eq", &[""]),
        ];
        let measure = vec![piece(
            "termination",
            "by_measure n",
            "by_measure n",
            &["structural m", "structural n"],
        )];
        Ok(File {
            decls: vec![
                decl("imports", "imports", SOURCE, Vec::new()),
                decl("definition", "T", "type T deriving Show, Eq", handlers),
                decl("definition", "f", "def f n := g n\nby_measure n", measure),
            ],
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
        let Ask::Run { edits } = &question.ask else {
            return answer;
        };
        let whole_file = question.decl == "T:imports";
        let fails = edits.iter().any(|e| {
            let deleted = &SOURCE[e.range.start..e.range.stop];
            self.broken.contains(&e.text.as_str())
                || (whole_file && self.used_later.iter().any(|used| deleted.contains(used)))
        });
        answer.verdict = if fails { "fails" } else { "closes" }.to_string();
        answer.ms = vec![if edits.is_empty() { 50 } else { 20 }; question.runs as usize];
        answer
    }
}

fn lint(mut prover: Fake) -> Vec<Finding> {
    let decls = prover.load("T").unwrap().decls;
    let options = Options::default();
    let answers = rounds::run(&mut prover, &Definitions, &decls, &options, None).unwrap();
    Definitions.report(&decls, &answers, &options)
}

fn fixed(findings: &[Finding]) -> String {
    let (edits, _) = fix::disjoint(findings);
    fix::apply(SOURCE, &edits).unwrap()
}

#[test]
fn a_public_handler_is_reported_and_a_private_one_removed() {
    let findings = lint(Fake {
        broken: vec!["structural m", "structural n"],
        used_later: vec![],
    });
    assert_eq!(findings.len(), 1);
    assert!(
        findings[0]
            .message
            .contains("public deriving `Show` (line 2) removed (not fixed")
    );
    assert!(
        findings[0]
            .message
            .ends_with("  deriving `Eq` (line 2) removed")
    );
    assert_eq!(
        fixed(&findings),
        "import A\ntype T deriving Show\ndef f n := g n\nby_measure n"
    );
}

#[test]
fn a_handler_the_file_uses_later_stays() {
    let findings = lint(Fake {
        broken: vec!["structural m", "structural n"],
        used_later: vec!["Eq"],
    });
    assert_eq!(findings.len(), 1);
    assert!(!findings[0].message.contains("`Eq`"));
    assert!(findings[0].edits.is_empty());
}

#[test]
fn the_first_replacement_that_checks_is_taken() {
    let findings = lint(Fake {
        broken: vec!["structural m"],
        used_later: vec!["Show", "Eq"],
    });
    assert_eq!(findings.len(), 1);
    assert!(
        findings[0]
            .message
            .starts_with("`f` takes 20 ms instead of 50 ms")
    );
    assert_eq!(
        fixed(&findings),
        "import A\ntype T deriving Show, Eq\ndef f n := g n\nstructural n"
    );
}
