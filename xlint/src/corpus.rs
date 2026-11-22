//! Lint a list of files on a copy of their project, check each fixed file, and add up what was
//! found. A file is done once it has a `.build` file, so a run that stopped goes on from there.

use crate::jobs;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

pub struct Corpus {
    pub out: PathBuf,
    /// The files are relative to this; it is copied to `out/copy` and linted there.
    pub project: Option<PathBuf>,
    /// The linter, run in the copy with the file as last argument.
    pub linter: Vec<String>,
    /// Flag before the question log's path, for a linter that writes one.
    pub log_flag: Option<String>,
    /// The check of a fixed file, run in the copy with the file as last argument.
    pub build: Vec<String>,
    /// Seconds a file's lint and its check get each.
    pub limit: Option<u64>,
    pub jobs: usize,
}

fn logs_name(file: &str) -> String {
    file.replace(['/', '\\'], "_")
}

/// The exit code, or none if the time ran out. The whole process group is killed, since a
/// linter's prover is its grandchild.
fn run(
    command: &[String],
    file: &str,
    dir: &Path,
    stdout: &Path,
    stderr: &Path,
    limit: Option<u64>,
) -> Result<Option<i32>, String> {
    use std::os::unix::process::CommandExt;
    let open =
        |path: &Path| std::fs::File::create(path).map_err(|e| format!("{}: {e}", path.display()));
    let (program, args) = command.split_first().ok_or("empty command")?;
    let mut child = Command::new(program)
        .args(args)
        .arg(file)
        .current_dir(dir)
        .stdin(Stdio::null())
        .stdout(open(stdout)?)
        .stderr(open(stderr)?)
        .process_group(0)
        .spawn()
        .map_err(|e| format!("cannot start {program}: {e}"))?;
    let start = Instant::now();
    loop {
        if let Some(status) = child.try_wait().map_err(|e| e.to_string())? {
            return Ok(Some(status.code().unwrap_or(-1)));
        }
        if limit.is_some_and(|limit| start.elapsed() > Duration::from_secs(limit)) {
            let _ = Command::new("kill")
                .args(["-KILL", &format!("-{}", child.id())])
                .status();
            let _ = child.wait();
            return Ok(None);
        }
        std::thread::sleep(Duration::from_millis(50));
    }
}

impl Corpus {
    fn logs(&self) -> PathBuf {
        self.out.join("logs")
    }

    fn dir(&self) -> PathBuf {
        match &self.project {
            Some(_) => self.out.join("copy"),
            None => std::env::current_dir().unwrap_or_default(),
        }
    }

    fn restore(&self, file: &str) -> Result<(), String> {
        match &self.project {
            Some(project) => std::fs::copy(project.join(file), self.dir().join(file))
                .map(|_| ())
                .map_err(|e| format!("{file}: {e}")),
            None => Ok(()),
        }
    }

    /// Lint, then check. A file whose lint or check fails goes back to its original, so the
    /// files that import it still see one that checks.
    fn file(&self, file: &str) -> Result<String, String> {
        let name = logs_name(file);
        let path = |suffix: &str| self.logs().join(format!("{name}.{suffix}"));
        let _ = std::fs::remove_file(path("tsv"));
        self.restore(file)?;
        let mut linter = self.linter.clone();
        if let Some(flag) = &self.log_flag {
            let log = std::path::absolute(path("tsv")).map_err(|e| e.to_string())?;
            linter.extend([flag.clone(), log.display().to_string()]);
        }
        let dir = self.dir();
        let linted = run(&linter, file, &dir, &path("log"), &path("err"), self.limit)?;
        let status = match linted {
            None => "lint timeout".to_string(),
            Some(code) if code != 0 => format!("lint failed ({code})"),
            Some(_) if self.build.is_empty() => "ok".to_string(),
            Some(_) => match run(
                &self.build,
                file,
                &dir,
                &path("check"),
                &path("check.err"),
                self.limit,
            )? {
                Some(0) => "ok".to_string(),
                Some(_) => "FAILED".to_string(),
                None => "check timeout".to_string(),
            },
        };
        if status != "ok" {
            self.restore(file)?;
        }
        // a fix is not to blame if the file as written fails the check too
        let status = match status.as_str() {
            "FAILED"
                if run(
                    &self.build,
                    file,
                    &dir,
                    &path("control"),
                    &path("control.err"),
                    self.limit,
                )? != Some(0) =>
            {
                "baseline-fails".to_string()
            }
            _ => status,
        };
        std::fs::write(path("build"), format!("{status}\n")).map_err(|e| e.to_string())?;
        Ok(status)
    }

    pub fn run(&self, files: &[String]) -> Result<Summary, String> {
        std::fs::create_dir_all(self.logs()).map_err(|e| format!("{}: {e}", self.out.display()))?;
        if let Some(project) = &self.project {
            let copy = self.out.join("copy");
            if !copy.exists() {
                let done = Command::new("cp")
                    .args(["-a", "--reflink=auto"])
                    .args([project, &copy])
                    .status()
                    .map_err(|e| e.to_string())?;
                if !done.success() {
                    return Err(format!("cannot copy {}", project.display()));
                }
            }
        }
        let todo: Vec<&String> = files
            .iter()
            .filter(|file| {
                !self
                    .logs()
                    .join(format!("{}.build", logs_name(file)))
                    .exists()
            })
            .collect();
        eprintln!(
            "{} files, {} already done",
            files.len(),
            files.len() - todo.len()
        );
        let mut error = None;
        jobs::in_order(
            &todo,
            self.jobs,
            |_, file| self.file(file),
            |index, status| match status {
                Ok(status) => eprintln!("{} {status}", todo[index]),
                Err(message) => error = error.take().or(Some(message)),
            },
        );
        error.map_or_else(|| Ok(summary(&self.logs(), files)), Err)
    }
}

/// What one file's logs say. Pieces are what `unused` found unneeded, by kind.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Row {
    pub entry: String,
    pub lemmas: usize,
    pub steps: usize,
    pub findings: usize,
    pub kinds: BTreeMap<String, usize>,
    /// Unneeded pieces that are reported only, like an assumption.
    pub kept: usize,
    pub fixed: usize,
    pub timed: usize,
    pub before_ms: u64,
    pub after_ms: u64,
    /// Findings of the other lints.
    pub other: usize,
    pub questions: usize,
    pub unanswered: usize,
    pub build: String,
}

impl Row {
    pub fn removed(&self) -> usize {
        self.kinds.values().sum()
    }

    fn add(&mut self, row: &Row) {
        self.lemmas += row.lemmas;
        self.steps += row.steps;
        self.findings += row.findings;
        for (kind, count) in &row.kinds {
            *self.kinds.entry(kind.clone()).or_default() += count;
        }
        self.kept += row.kept;
        self.fixed += row.fixed;
        self.timed += row.timed;
        self.before_ms += row.before_ms;
        self.after_ms += row.after_ms;
        self.other += row.other;
        self.questions += row.questions;
        self.unanswered += row.unanswered;
    }

    fn tsv(&self) -> String {
        let per = |n: usize, of: usize| {
            if of == 0 {
                String::new()
            } else {
                format!("{:.1}", 100.0 * n as f64 / of as f64)
            }
        };
        let kinds: Vec<String> = self
            .kinds
            .iter()
            .map(|(kind, count)| format!("{kind} {count}"))
            .collect();
        [
            self.entry.clone(),
            self.lemmas.to_string(),
            self.steps.to_string(),
            self.findings.to_string(),
            kinds.join(", "),
            self.removed().to_string(),
            self.kept.to_string(),
            self.fixed.to_string(),
            per(self.removed(), self.lemmas),
            per(self.removed(), self.steps),
            self.timed.to_string(),
            self.before_ms.to_string(),
            self.after_ms.to_string(),
            self.other.to_string(),
            self.questions.to_string(),
            self.unanswered.to_string(),
            self.build.clone(),
        ]
        .join("\t")
    }
}

const HEADER: &str = "entry\tlemmas\tsteps\tfindings\tpieces\tremoved\treported only\tfixed\tremoved /100 lemmas\tremoved /100 steps\ttimed fixes\tms before\tms after\tother findings\tquestions\tunanswered\tbuild";

fn number(text: &str) -> u64 {
    text.trim().parse().unwrap_or(0)
}

/// `FILE: N theorems, M steps`, as the linters say on stderr.
fn sizes(err: &str) -> (usize, usize) {
    err.lines()
        .filter_map(|line| {
            let (theorems, steps) = line.rsplit_once(": ")?.1.split_once(" theorems, ")?;
            Some((
                number(theorems) as usize,
                number(steps.strip_suffix(" steps")?) as usize,
            ))
        })
        .fold((0, 0), |(l, s), (lemmas, steps)| (l + lemmas, s + steps))
}

/// xlint lists a finding's pieces on the lines after it, under a heading that says whether
/// they are removed. A tool with one hit per finding starts the message with its name.
pub fn read(entry: &str, log: &str, err: &str, questions: &str, build: &str) -> Row {
    let mut row = Row {
        entry: entry.to_string(),
        build: build.trim().to_string(),
        ..Row::default()
    };
    (row.lemmas, row.steps) = sizes(err);
    let (mut unused, mut removing) = (false, false);
    for line in log.lines() {
        if let Some(piece) = line.strip_prefix("  ") {
            match piece.split_once(" `") {
                Some((kind, _)) if unused && removing => {
                    *row.kinds.entry(kind.to_string()).or_default() += 1
                }
                Some(_) if unused => row.kept += 1,
                _ => {}
            }
        } else if let Some((_, rest)) = line.split_once(": [") {
            let (lint, message) = rest.split_once("] ").unwrap_or((rest, ""));
            unused = lint == "unused";
            removing = message == "not needed:";
            if !unused {
                row.other += 1;
                continue;
            }
            row.findings += 1;
            match message.split_once(": ") {
                Some((tool, _)) if !message.starts_with("not needed") => {
                    *row.kinds.entry(tool.to_string()).or_default() += 1
                }
                _ => {}
            }
        } else if let Some(count) = line.strip_prefix("Fixed ") {
            row.fixed += number(count.split(' ').next().unwrap_or("")) as usize;
        } else if !unused {
        } else if let Some(times) = line.strip_prefix("time: ") {
            if let Some((before, after)) = times.split_once(" ms as written, ") {
                row.timed += 1;
                row.before_ms += number(before);
                row.after_ms += number(after.split(' ').next().unwrap_or(""));
            }
        } else if line.starts_with("not needed") {
            removing = line == "not needed:";
        }
    }
    for question in questions
        .lines()
        .filter(|line| !line.starts_with("xlint\tjobs\t"))
    {
        row.questions += 1;
        row.unanswered += (question.split('\t').nth(3) == Some("unanswered")) as usize;
    }
    row
}

pub struct Summary {
    pub rows: Vec<Row>,
    pub total: Row,
}

impl Summary {
    pub fn to_tsv(&self) -> String {
        let rows: Vec<String> = self
            .rows
            .iter()
            .chain([&self.total])
            .map(Row::tsv)
            .collect();
        format!("{HEADER}\n{}\n", rows.join("\n"))
    }

    /// The total in a sentence. Only files whose check passed are counted.
    pub fn sentence(&self) -> String {
        let total = &self.total;
        format!(
            "{} of {} files ok: {} lemmas, {} steps; {} lemmas with a finding ({:.1}%), {} pieces not needed ({:.1} per 100 steps), {} fixed; {} timed fixes {} -> {} ms; {} questions, {} unanswered",
            self.rows.iter().filter(|row| row.build == "ok").count(),
            self.rows.len(),
            total.lemmas,
            total.steps,
            total.findings,
            100.0 * total.findings as f64 / total.lemmas.max(1) as f64,
            total.removed(),
            100.0 * total.removed() as f64 / total.steps.max(1) as f64,
            total.fixed,
            total.timed,
            total.before_ms,
            total.after_ms,
            total.questions,
            total.unanswered
        )
    }
}

/// One row per file that has logs, and their total over the files whose check passed.
pub fn summary(logs: &Path, files: &[String]) -> Summary {
    let text = |name: &str, suffix: &str| {
        std::fs::read_to_string(logs.join(format!("{name}.{suffix}"))).unwrap_or_default()
    };
    let rows: Vec<Row> = files
        .iter()
        .map(|file| (file, logs_name(file)))
        .filter(|(_, name)| logs.join(format!("{name}.build")).exists())
        .map(|(file, name)| {
            read(
                file,
                &text(&name, "log"),
                &text(&name, "err"),
                &text(&name, "tsv"),
                &text(&name, "build"),
            )
        })
        .collect();
    let mut total = Row {
        entry: "total".to_string(),
        ..Row::default()
    };
    rows.iter()
        .filter(|row| row.build == "ok")
        .for_each(|row| total.add(row));
    Summary { rows, total }
}
