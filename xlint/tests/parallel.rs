//! Files linted at once still report, and log, in the order they were given.

use std::time::Duration;
use xlint::lint::Options;
use xlint::protocol::{Answer, Decl, File, Hello, Piece, Question, Range};
use xlint::prover::{Prover, Result};
use xlint::session::Session;

/// One theorem with one unneeded piece. A file named `slow...` takes longer to load.
struct Fake;

impl Prover for Fake {
    fn hello(&mut self) -> Result<Hello> {
        Ok(Hello::default())
    }

    fn load(&mut self, file: &str) -> Result<File> {
        if file.starts_with("slow") {
            std::thread::sleep(Duration::from_millis(300));
        }
        if file.starts_with("broken") {
            return Err("does not load".to_string());
        }
        let range = Range { start: 0, stop: 4 };
        let piece = Piece {
            kind: "fact".to_string(),
            text: "h".to_string(),
            range,
            line: 1,
            replacements: Vec::new(),
            whole: None,
        };
        Ok(File {
            decls: vec![Decl {
                key: file.to_string(),
                name: "t".to_string(),
                kind: "theorem".to_string(),
                range,
                line: 1,
                ok: true,
                steps: Vec::new(),
                simps: Vec::new(),
                pieces: vec![piece],
            }],
            diagnostics: Vec::new(),
            commands: Vec::new(),
        })
    }

    fn ask(&mut self, questions: &[Question]) -> Result<Vec<Answer>> {
        Ok(questions
            .iter()
            .map(|q| Answer {
                verdict: "closes".to_string(),
                ms: vec![5; q.runs as usize],
                ..Answer::unanswered(&q.key)
            })
            .collect())
    }
}

fn lint(files: &[&str], jobs: usize, log: &std::path::Path) -> (String, (usize, usize)) {
    let _ = std::fs::remove_file(log);
    let files: Vec<String> = files.iter().map(|f| f.to_string()).collect();
    let lints = ["unused".to_string()];
    let options = Options::default();
    let session = Session {
        lints: Some(&lints),
        options: &options,
        log: Some(log),
        fix: false,
        jobs,
    };
    let mut out = Vec::new();
    let counts = session
        .lint_files(&files, || Ok(Box::new(Fake) as Box<dyn Prover>), &mut out)
        .unwrap();
    (String::from_utf8(out).unwrap(), counts)
}

fn keys(log: &std::path::Path) -> Vec<String> {
    let text = std::fs::read_to_string(log).unwrap();
    text.lines()
        .map(|line| line.split('\t').nth(1).unwrap().to_string())
        .collect()
}

#[test]
fn reports_and_log_keep_the_file_order() {
    let dir = std::env::temp_dir().join(format!("xlint-parallel-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let files = ["slow.a", "b", "c"];
    let (alone, _) = lint(&files, 1, &dir.join("alone.tsv"));
    let (together, counts) = lint(&files, 3, &dir.join("together.tsv"));
    assert_eq!(alone, together);
    assert_eq!(counts, (3, 0));
    let headers: Vec<&str> = together
        .lines()
        .filter(|l| l.contains("[unused]"))
        .collect();
    assert_eq!(
        headers,
        [
            "slow.a:1: [unused] not needed:",
            "b:1: [unused] not needed:",
            "c:1: [unused] not needed:"
        ]
    );
    // the same rows after the one that says the times were taken under load
    let rows = keys(&dir.join("together.tsv"));
    assert_eq!(rows[0], "jobs");
    assert_eq!(rows[1..], keys(&dir.join("alone.tsv")));
    assert!(rows[1].starts_with("slow.a"));
    assert!(!dir.join("together.tsv.part0").exists());
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn a_file_that_fails_does_not_stop_the_others() {
    let dir = std::env::temp_dir().join(format!("xlint-parallel-fail-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let (report, counts) = lint(&["a", "broken", "c"], 2, &dir.join("log.tsv"));
    assert_eq!(counts, (2, 1));
    assert!(report.contains("a:1:") && report.contains("c:1:"));
    std::fs::remove_dir_all(dir).unwrap();
}
