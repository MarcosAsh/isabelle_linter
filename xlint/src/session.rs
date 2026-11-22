//! Lint files, each with its own server, and report them in the order they were given.

use crate::lint::Options;
use crate::prover::{Prover, Result};
use crate::{fix, jobs, lints, rounds};
use std::fmt::Write as _;
use std::io::Write;
use std::path::{Path, PathBuf};

pub struct Session<'a> {
    /// Lints to run, all of them if none is named.
    pub lints: Option<&'a [String]>,
    pub options: &'a Options,
    pub log: Option<&'a Path>,
    pub fix: bool,
    pub jobs: usize,
}

struct Linted {
    report: String,
    findings: usize,
}

fn part(log: &Path, index: usize) -> PathBuf {
    PathBuf::from(format!("{}.part{index}", log.display()))
}

impl Session<'_> {
    fn lint_file(&self, prover: &mut dyn Prover, file: &str, log: Option<&Path>) -> Result<Linted> {
        let loaded = prover.load(file)?;
        let decls = &loaded.decls;
        let theorems = decls.iter().filter(|d| d.ok && d.kind == "theorem");
        eprintln!(
            "{file}: {} theorems, {} steps",
            theorems.clone().count(),
            theorems.map(|d| d.steps.len()).sum::<usize>()
        );
        let mut findings = Vec::new();
        for lint in lints::all() {
            if self
                .lints
                .is_some_and(|names| !names.iter().any(|n| n == lint.name()))
            {
                continue;
            }
            let answers = rounds::run(prover, lint.as_ref(), decls, self.options, log)?;
            findings.extend(lint.read(&loaded));
            findings.extend(lint.report(decls, &answers, self.options));
        }
        let mut report = String::new();
        for finding in &findings {
            let _ = writeln!(
                report,
                "\n{file}:{}: [{}] {}",
                finding.line, finding.lint, finding.message
            );
        }
        if self.fix {
            let (edits, fixed) = fix::disjoint(&findings);
            if !edits.is_empty() {
                let text = std::fs::read_to_string(file).map_err(|e| format!("{file}: {e}"))?;
                std::fs::write(file, fix::apply(&text, &edits)?)
                    .map_err(|e| format!("{file}: {e}"))?;
                let _ = writeln!(report, "Fixed {fixed} findings in {file}");
            }
        }
        Ok(Linted {
            report,
            findings: findings.len(),
        })
    }

    /// Reports and the question log come out in file order. A file that fails is named on
    /// stderr and the others go on; returns the findings and the failed files.
    pub fn lint_files(
        &self,
        files: &[String],
        start: impl Fn() -> Result<Box<dyn Prover>> + Sync,
        out: &mut dyn Write,
    ) -> Result<(usize, usize)> {
        let jobs = self.jobs.clamp(1, files.len().max(1));
        if let (Some(log), true) = (self.log, jobs > 1) {
            // one row, so that the times in this log are not read as taken alone
            let row =
                format!("xlint\tjobs\t{jobs} files at once: times were taken under load\t\t\t\n");
            append(log, row.as_bytes())?;
        }
        let (mut findings, mut failed) = (0, 0);
        let mut error = None;
        jobs::in_order(
            files,
            jobs,
            |index, file| {
                let log = self.log.map(|log| part(log, index));
                start().and_then(|mut prover| self.lint_file(prover.as_mut(), file, log.as_deref()))
            },
            |index, linted| {
                if let Some(log) = self.log {
                    let part = part(log, index);
                    if let Ok(rows) = std::fs::read(&part) {
                        error = error.take().or(append(log, &rows).err());
                        let _ = std::fs::remove_file(part);
                    }
                }
                match linted {
                    Ok(linted) => {
                        findings += linted.findings;
                        let _ = out.write_all(linted.report.as_bytes());
                    }
                    Err(message) => {
                        failed += 1;
                        eprintln!("*** {}: {message}", files[index]);
                    }
                }
            },
        );
        error.map_or(Ok((findings, failed)), Err)
    }
}

fn append(path: &Path, bytes: &[u8]) -> Result<()> {
    std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .and_then(|mut file| file.write_all(bytes))
        .map_err(|e| format!("cannot write {}: {e}", path.display()))
}
