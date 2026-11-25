//! `census` and `retime` against a prover that knows how long each command and step takes.

use xlint::census::{self, Row};
use xlint::protocol::{Answer, Ask, Command, Decl, File, Hello, Question, Range, Step};
use xlint::prover::{Prover, Result};
use xlint::retime;

const SOURCE: &str = "def d := 1\ntheorem t : goal := by slow\ntheorem u : goal := by quick";

/// Each step takes its `ms` in turn, one per run. `stuck` never closes.
struct Fake {
    ms: Vec<(&'static str, Vec<u64>)>,
}

fn range(text: &str) -> Range {
    let start = SOURCE.find(text).unwrap();
    Range {
        start,
        stop: start + text.len(),
    }
}

impl Prover for Fake {
    fn hello(&mut self) -> Result<Hello> {
        Ok(Hello::default())
    }

    fn load(&mut self, _file: &str) -> Result<File> {
        let command = |kind: &str, text: &str, ms| Command {
            kind: kind.to_string(),
            text: text.to_string(),
            range: range(text),
            ms,
        };
        let theorem = |name: &str, text: &str, tactic: &str| Decl {
            key: format!("T:{name}"),
            name: name.to_string(),
            kind: "theorem".to_string(),
            range: range(text),
            line: 1,
            ok: true,
            steps: vec![Step {
                text: tactic.to_string(),
                range: range(tactic),
                line: 1,
                candidates: Vec::new(),
            }],
            simps: Vec::new(),
            pieces: Vec::new(),
            probes: Vec::new(),
        };
        Ok(File {
            decls: vec![
                theorem("t", "theorem t : goal := by slow", "slow"),
                theorem("u", "theorem u : goal := by quick", "quick"),
            ],
            diagnostics: Vec::new(),
            commands: vec![
                command("def", "def d := 1", 40),
                command("theorem", "theorem t : goal := by slow", 5000),
                command("theorem", "theorem u : goal := by quick", 60),
            ],
        })
    }

    fn ask(&mut self, questions: &[Question]) -> Result<Vec<Answer>> {
        Ok(questions
            .iter()
            .map(|question| {
                let mut answer = Answer::unanswered(&question.key);
                let Ask::Step { text, .. } = &question.ask else {
                    return answer;
                };
                match self.ms.iter().find(|(step, _)| step == text) {
                    Some((_, ms)) => {
                        answer.verdict = "closes".to_string();
                        answer.ms = ms
                            .iter()
                            .copied()
                            .cycle()
                            .take(question.runs as usize)
                            .collect();
                    }
                    None => answer.verdict = "timeout".to_string(),
                }
                answer
            })
            .collect())
    }
}

fn fake() -> Fake {
    Fake {
        ms: vec![("slow", vec![4000, 3000, 3200]), ("quick", vec![20])],
    }
}

fn rows() -> Vec<Row> {
    census::file_rows(&mut fake(), "dir/T.lean", 30_000)
        .unwrap()
        .0
}

#[test]
fn a_step_row_follows_the_row_of_its_theorem() {
    let found: Vec<(String, f64)> = rows()
        .into_iter()
        .map(|row| (row.command, row.seconds))
        .collect();
    let expected = [
        ("def", 0.04),
        ("theorem", 5.0),
        ("step", 4.0),
        ("theorem", 0.06),
        ("step", 0.02),
    ];
    assert_eq!(
        found,
        expected.map(|(command, seconds)| (command.to_string(), seconds))
    );
}

#[test]
fn a_step_that_does_not_close_alone_gets_no_row() {
    let mut prover = Fake {
        ms: vec![("quick", vec![20])],
    };
    let (rows, lost) = census::file_rows(&mut prover, "T.lean", 30_000).unwrap();
    assert_eq!(lost, 1);
    assert_eq!(rows.iter().filter(|row| row.is_step()).count(), 1);
}

#[test]
fn the_rows_survive_the_tsv() {
    let rows = rows();
    assert_eq!(rows[0].session, "dir");
    assert_eq!(census::from_tsv(&census::to_tsv(&rows)).unwrap(), rows);
}

#[test]
fn the_summary_takes_shares_of_the_commands_time() {
    let summary = census::summary(&rows(), 1);
    assert!(
        summary.starts_with(
            "1 files, 3 commands, 5.1 s; 2 steps, 4.0 s (78.8% of the commands' time)"
        )
    );
    assert!(summary.contains("  theorem            5.1 s   99.2%      2 commands"));
    assert!(summary.contains("  slow               4.0 s   99.5%      1 steps"));
    assert!(summary.ends_with("slowest:\n     4.00 s  dir/T.lean:34  slow\n"));
}

#[test]
fn retime_takes_the_median_of_the_slowest_steps() {
    let slowest = retime::slowest(&rows(), 1);
    assert_eq!(slowest.len(), 1);
    let retimed = retime::file_steps(&mut fake(), "dir/T.lean", &slowest, 3, 30_000).unwrap();
    assert_eq!(retimed[0].median_ms(), Some(3200));
    let line = retime::to_tsv(&retimed).lines().nth(1).unwrap().to_string();
    assert_eq!(
        line,
        "dir\tdir/T.lean\t34\t4\tcloses\t3200\t3\t4000,3000,3200\tslow"
    );
}

#[test]
fn retime_reports_a_row_that_is_no_step() {
    let mut row = retime::slowest(&rows(), 1).remove(0);
    row.offset += 1;
    let retimed = retime::file_steps(&mut fake(), "dir/T.lean", &[row], 3, 30_000).unwrap();
    assert_eq!(retimed[0].verdict, "not_found");
    assert_eq!(retimed[0].median_ms(), None);
}
