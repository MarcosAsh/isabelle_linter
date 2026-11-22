//! Time the census's slowest steps again, each alone and several times.

use crate::census::Row;
use crate::protocol::{Ask, Question};
use crate::prover::{Prover, Result};
use std::fmt::Write as _;

pub const HEADER: &str = "session\tfile\toffset\tcensus_s\tverdict\tmedian_ms\truns\truns_ms\ttext";

#[derive(Clone, Debug, PartialEq)]
pub struct Retimed {
    pub row: Row,
    pub verdict: String,
    pub runs_ms: Vec<u64>,
}

impl Retimed {
    pub fn median_ms(&self) -> Option<u64> {
        let mut ms = self.runs_ms.clone();
        ms.sort();
        ms.get(ms.len() / 2).copied()
    }
}

pub fn slowest(rows: &[Row], n: usize) -> Vec<Row> {
    let mut steps: Vec<Row> = rows.iter().filter(|row| row.is_step()).cloned().collect();
    steps.sort_by(|a, b| b.seconds.total_cmp(&a.seconds));
    steps.truncate(n);
    steps
}

/// `rows` are steps of `file`. A row whose offset is no step of the loaded file is `not_found`.
pub fn file_steps(
    prover: &mut dyn Prover,
    file: &str,
    rows: &[Row],
    runs: u32,
    timeout_ms: u64,
) -> Result<Vec<Retimed>> {
    let loaded = prover.load(file)?;
    let mut retimed = Vec::new();
    for row in rows {
        let found = loaded.decls.iter().filter(|decl| decl.ok).find_map(|decl| {
            let step = decl
                .steps
                .iter()
                .position(|step| step.range.start == row.offset)?;
            Some((decl, step))
        });
        let (verdict, runs_ms) = match found {
            None => ("not_found".to_string(), Vec::new()),
            Some((decl, step)) => {
                let question = Question {
                    key: format!("{}:{}:retime", decl.key, row.offset),
                    decl: decl.key.clone(),
                    ask: Ask::Step {
                        step,
                        text: decl.steps[step].text.clone(),
                    },
                    timeout_ms,
                    runs,
                    serial: true,
                };
                match prover.ask(std::slice::from_ref(&question))?.pop() {
                    Some(answer) if answer.closes() => (answer.verdict, answer.ms),
                    Some(answer) => (answer.verdict, Vec::new()),
                    None => ("unanswered".to_string(), Vec::new()),
                }
            }
        };
        retimed.push(Retimed {
            row: row.clone(),
            verdict,
            runs_ms,
        });
    }
    Ok(retimed)
}

pub fn to_tsv(retimed: &[Retimed]) -> String {
    let mut out = format!("{HEADER}\n");
    for step in retimed {
        let runs: Vec<String> = step.runs_ms.iter().map(u64::to_string).collect();
        let _ = writeln!(
            out,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            step.row.session,
            step.row.file,
            step.row.offset,
            step.row.seconds,
            step.verdict,
            step.median_ms()
                .map(|ms| ms.to_string())
                .unwrap_or_default(),
            runs.len(),
            runs.join(","),
            step.row.text
        );
    }
    out
}
