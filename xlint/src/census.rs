//! Where a file's checking time goes: each command as the prover loaded it, and each closing
//! step run once more on its own goal. The TSV has the columns of `isabelle linter_census -O`.

use crate::protocol::{Ask, Question};
use crate::prover::{Prover, Result};
use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::Path;

pub const HEADER: &str = "session\tfile\toffset\tcommand\tseconds\ttext";
pub const STEP: &str = "step";

/// A step row has the command `step` and lies inside the row of its declaration.
#[derive(Clone, Debug, PartialEq)]
pub struct Row {
    pub session: String,
    pub file: String,
    pub offset: usize,
    pub command: String,
    pub seconds: f64,
    pub text: String,
}

impl Row {
    pub fn is_step(&self) -> bool {
        self.command == STEP
    }
}

/// A file's directory stands in for the session.
fn session(file: &str) -> String {
    Path::new(file)
        .parent()
        .map(|dir| dir.display().to_string())
        .unwrap_or_default()
}

fn first_line(text: &str) -> String {
    text.lines().next().unwrap_or("").replace('\t', " ")
}

/// Steps that do not close alone within the limit get no row; the count is returned.
pub fn file_rows(
    prover: &mut dyn Prover,
    file: &str,
    timeout_ms: u64,
) -> Result<(Vec<Row>, usize)> {
    let loaded = prover.load(file)?;
    let row = |offset, command: &str, ms: u64, text: &str| Row {
        session: session(file),
        file: file.to_string(),
        offset,
        command: command.to_string(),
        seconds: ms as f64 / 1000.0,
        text: first_line(text),
    };
    let mut rows: Vec<Row> = loaded
        .commands
        .iter()
        .map(|c| row(c.range.start, &c.kind, c.ms, &c.text))
        .collect();
    let steps: Vec<_> = loaded
        .decls
        .iter()
        .filter(|decl| decl.ok)
        .flat_map(|decl| {
            decl.steps
                .iter()
                .enumerate()
                .map(move |(i, step)| (decl, i, step))
        })
        .collect();
    let questions: Vec<Question> = steps
        .iter()
        .map(|(decl, i, step)| Question {
            key: format!("{}:{}:census", decl.key, step.range.start),
            decl: decl.key.clone(),
            ask: Ask::Step {
                step: *i,
                text: step.text.clone(),
            },
            timeout_ms,
            runs: 1,
            serial: true,
        })
        .collect();
    let answers: HashMap<String, _> = prover
        .ask(&questions)?
        .into_iter()
        .map(|answer| (answer.key.clone(), answer))
        .collect();
    let mut lost = 0;
    for ((_, _, step), question) in steps.iter().zip(&questions) {
        match answers.get(&question.key) {
            Some(answer) if answer.closes() => {
                rows.push(row(step.range.start, STEP, answer.median_ms(), &step.text))
            }
            _ => lost += 1,
        }
    }
    rows.sort_by_key(|row| (row.offset, row.is_step()));
    Ok((rows, lost))
}

pub fn to_tsv(rows: &[Row]) -> String {
    let mut out = format!("{HEADER}\n");
    for row in rows {
        let _ = writeln!(
            out,
            "{}\t{}\t{}\t{}\t{}\t{}",
            row.session, row.file, row.offset, row.command, row.seconds, row.text
        );
    }
    out
}

pub fn from_tsv(text: &str) -> std::result::Result<Vec<Row>, String> {
    text.lines()
        .skip(1)
        .filter(|line| !line.is_empty())
        .map(|line| {
            let fields: Vec<&str> = line.splitn(6, '\t').collect();
            let bad = || format!("bad census row: {line}");
            let [session, file, offset, command, seconds, text] = fields[..] else {
                return Err(bad());
            };
            Ok(Row {
                session: session.to_string(),
                file: file.to_string(),
                offset: offset.parse().map_err(|_| bad())?,
                command: command.to_string(),
                seconds: seconds.parse().map_err(|_| bad())?,
                text: text.to_string(),
            })
        })
        .collect()
}

fn share(part: f64, all: f64) -> String {
    if all == 0.0 {
        "-".to_string()
    } else {
        format!("{:.1}%", 100.0 * part / all)
    }
}

/// Seconds and count per group, largest first.
fn groups<'a>(rows: &[&'a Row], name: impl Fn(&'a Row) -> &'a str) -> Vec<(&'a str, f64, usize)> {
    let mut sums: HashMap<&str, (f64, usize)> = HashMap::new();
    for row in rows {
        let sum = sums.entry(name(row)).or_default();
        sum.0 += row.seconds;
        sum.1 += 1;
    }
    let mut sorted: Vec<_> = sums
        .into_iter()
        .map(|(name, (s, n))| (name, s, n))
        .collect();
    sorted.sort_by(|a, b| b.1.total_cmp(&a.1).then(a.0.cmp(b.0)));
    sorted
}

fn tactic(row: &Row) -> &str {
    row.text.split([' ', '[', '(']).next().unwrap_or("")
}

/// Shares are of the commands' time, which already holds the steps' time.
pub fn summary(rows: &[Row], top: usize) -> String {
    let commands: Vec<&Row> = rows.iter().filter(|row| !row.is_step()).collect();
    let mut steps: Vec<&Row> = rows.iter().filter(|row| row.is_step()).collect();
    steps.sort_by(|a, b| b.seconds.total_cmp(&a.seconds));
    let total: f64 = commands.iter().map(|row| row.seconds).sum();
    let in_steps: f64 = steps.iter().map(|row| row.seconds).sum();
    let files = rows
        .iter()
        .map(|row| &row.file)
        .collect::<std::collections::HashSet<_>>()
        .len();
    let mut out = format!(
        "{files} files, {} commands, {total:.1} s; {} steps, {in_steps:.1} s ({} of the commands' time)\n",
        commands.len(),
        steps.len(),
        share(in_steps, total)
    );
    out.push_str("\nby command:\n");
    for (name, seconds, count) in groups(&commands, |row| &row.command).into_iter().take(12) {
        let _ = writeln!(
            out,
            "  {name:<14} {seconds:>7.1} s  {:>6}  {count:>5} commands",
            share(seconds, total)
        );
    }
    out.push_str("\nby tactic:\n");
    for (name, seconds, count) in groups(&steps, tactic).into_iter().take(12) {
        let _ = writeln!(
            out,
            "  {name:<14} {seconds:>7.1} s  {:>6}  {count:>5} steps",
            share(seconds, in_steps)
        );
    }
    out.push_str("\nconcentration:\n");
    for k in [10, 100, 1000] {
        if k < steps.len() {
            let part: f64 = steps[..k].iter().map(|row| row.seconds).sum();
            let _ = writeln!(out, "  top {k}: {} of step time", share(part, in_steps));
        }
    }
    out.push_str("\nslowest:\n");
    for row in steps.iter().take(top) {
        let _ = writeln!(
            out,
            "  {:>7.2} s  {}:{}  {}",
            row.seconds, row.file, row.offset, row.text
        );
    }
    out
}
