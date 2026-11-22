//! xlint: lint proof files with the prover checking every suggestion.

use std::path::PathBuf;
use std::process::ExitCode;
use xlint::corpus::Corpus;
use xlint::lint::Options;
use xlint::prover::{Prover, Server};
use xlint::session::Session;
use xlint::{census, jobs, retime};

const USAGE: &str = "Usage: xlint -s SERVER [-F] [-j N] [-l LINTS] [-L LOG] [-o NAME=VALUE] FILE...
       xlint run -d OUT (-s SERVER | -x TOOL) [-p PROJECT] [-b CHECK] [-t SECONDS] [-j N]
                 [-l LINTS] [-o NAME=VALUE] [-f LIST] FILE...
       xlint census -s SERVER [-O TSV] [-n N] [-o timeout_ms=MS] FILE...
       xlint retime -s SERVER -I TSV [-O TSV] [-n N] [-o runs=N] [-o timeout_ms=MS]

  -s SERVER    the prover's server command, in one argument (\"lake exe xlint-lean\")
  -F           apply the fixes to the files
  -j N         files linted at once (default: the cores but two); with more than
               one, times are taken under load and the log says so
  -l LINTS     comma-separated lints to run (default: all)
  -L LOG       append every question and answer to LOG, as TSV
  -o NAME=VAL  set an option (timeout_ms, factor, batch, runs, unused_ahead,
               faster_step_slow_ms, faster_step_speedup, simp_hygiene_min,
               simp_scope_slow_ms, simp_scope_speedup)

  run lints the files with -F on a copy of PROJECT, checks each fixed file,
  and adds the files up in OUT/summary.tsv; files that are done are skipped.
  -d OUT       logs, the copy and the summary go here
  -p PROJECT   the files are relative to this directory; without it they are
               linted where they are
  -x TOOL      a linter of its own that prints findings like xlint, in place of -s
  -b CHECK     run in the copy on each fixed file; a file that fails goes back
  -t SECONDS   time limit of a file's lint, and of its check
  -f LIST      a file with one file name per line

  census times each command and each closing step of the files and shows where
  the time goes. retime runs the N slowest steps of a census TSV again, alone.
  -O TSV       write the rows to TSV
  -I TSV       the census rows to re-time
  -n N         slowest steps shown (census, default 30) or re-timed (retime, default 100)";

struct Args {
    mode: String,
    server: Vec<String>,
    fix: bool,
    lints: Option<Vec<String>>,
    log: Option<PathBuf>,
    output: Option<PathBuf>,
    input: Option<PathBuf>,
    top: Option<usize>,
    options: Options,
    /// The -o assignments as given, for the linter that `run` starts.
    assignments: Vec<String>,
    jobs: usize,
    out: Option<PathBuf>,
    project: Option<PathBuf>,
    tool: Vec<String>,
    check: Vec<String>,
    limit: Option<u64>,
    files: Vec<String>,
}

fn parse() -> Result<Args, String> {
    let mut args = Args {
        mode: "lint".to_string(),
        server: Vec::new(),
        fix: false,
        lints: None,
        log: None,
        output: None,
        input: None,
        top: None,
        options: Options::default(),
        assignments: Vec::new(),
        jobs: jobs::default_jobs(),
        out: None,
        project: None,
        tool: Vec::new(),
        check: Vec::new(),
        limit: None,
        files: Vec::new(),
    };
    let mut argv = std::env::args().skip(1).peekable();
    if let Some(mode) = argv.next_if(|arg| ["census", "retime", "run"].contains(&arg.as_str())) {
        args.mode = mode;
    }
    while let Some(arg) = argv.next() {
        let mut value = || argv.next().ok_or(format!("{arg} needs a value"));
        let words = |text: String| text.split_whitespace().map(str::to_string).collect();
        match arg.as_str() {
            "-s" => args.server = words(value()?),
            "-x" => args.tool = words(value()?),
            "-b" => args.check = words(value()?),
            "-d" => args.out = Some(PathBuf::from(value()?)),
            "-p" => args.project = Some(PathBuf::from(value()?)),
            "-j" => args.jobs = value()?.parse().map_err(|_| "-j needs a number")?,
            "-t" => args.limit = Some(value()?.parse().map_err(|_| "-t needs a number")?),
            "-f" => {
                let list = value()?;
                let text = std::fs::read_to_string(&list).map_err(|e| format!("{list}: {e}"))?;
                args.files
                    .extend(text.split_whitespace().map(str::to_string));
            }
            "-F" => args.fix = true,
            "-l" => args.lints = Some(value()?.split(',').map(str::to_string).collect()),
            "-L" => args.log = Some(PathBuf::from(value()?)),
            "-O" => args.output = Some(PathBuf::from(value()?)),
            "-I" => args.input = Some(PathBuf::from(value()?)),
            "-n" => args.top = Some(value()?.parse().map_err(|_| "-n needs a number")?),
            "-o" => {
                let assignment = value()?;
                args.options.set(&assignment)?;
                args.assignments.push(assignment);
            }
            _ if arg.starts_with('-') => return Err(format!("unknown option {arg}")),
            _ => args.files.push(arg),
        }
    }
    let nothing_to_read = if args.mode == "retime" {
        args.input.is_none()
    } else {
        args.files.is_empty()
    };
    if (args.server.is_empty() && args.tool.is_empty()) || nothing_to_read {
        return Err("a server and a file are needed".to_string());
    }
    if args.mode == "run" && args.out.is_none() {
        return Err("run needs -d OUT".to_string());
    }
    Ok(args)
}

/// A server loads one file, so each file gets its own.
fn start(args: &Args) -> Result<Server, String> {
    let mut server = Server::start(&args.server)?;
    let hello = server.hello()?;
    eprintln!("{} {}", hello.prover, hello.version);
    Ok(server)
}

fn write(path: &Option<PathBuf>, text: String) -> Result<(), String> {
    match path {
        Some(path) => std::fs::write(path, text).map_err(|e| format!("{}: {e}", path.display())),
        None => Ok(()),
    }
}

fn run_census(args: &Args) -> Result<(), String> {
    let mut rows = Vec::new();
    for file in &args.files {
        let (found, lost) = census::file_rows(&mut start(args)?, file, args.options.timeout_ms)?;
        let steps = found.iter().filter(|row| row.is_step()).count();
        eprintln!(
            "{file}: {} commands, {steps} steps, {lost} steps did not close alone",
            found.len() - steps
        );
        rows.extend(found);
        write(&args.output, census::to_tsv(&rows))?;
    }
    print!("{}", census::summary(&rows, args.top.unwrap_or(30)));
    Ok(())
}

fn run_retime(args: &Args) -> Result<(), String> {
    let input = args.input.as_ref().unwrap();
    let text = std::fs::read_to_string(input).map_err(|e| format!("{}: {e}", input.display()))?;
    let rows = retime::slowest(&census::from_tsv(&text)?, args.top.unwrap_or(100));
    let mut files: Vec<&str> = rows.iter().map(|row| row.file.as_str()).collect();
    files.sort();
    files.dedup();
    let mut retimed = Vec::new();
    for file in files {
        let of_file: Vec<_> = rows
            .iter()
            .filter(|row| row.file == file)
            .cloned()
            .collect();
        let found = retime::file_steps(
            &mut start(args)?,
            file,
            &of_file,
            args.options.runs,
            args.options.timeout_ms,
        )?;
        for step in &found {
            let after = step
                .median_ms()
                .map(|ms| format!("{:.2} s", ms as f64 / 1000.0))
                .unwrap_or(step.verdict.clone());
            println!(
                "retime: {:>8.2} s -> {after}  {}",
                step.row.seconds, step.row.text
            );
        }
        retimed.extend(found);
        write(&args.output, retime::to_tsv(&retimed))?;
    }
    let timed: Vec<_> = retimed
        .iter()
        .filter_map(|step| Some((step.row.seconds, step.median_ms()?)))
        .collect();
    println!(
        "\n{} of {} steps re-timed: {:.1} s in the census, {:.1} s alone",
        timed.len(),
        retimed.len(),
        timed.iter().map(|(census, _)| census).sum::<f64>(),
        timed.iter().map(|(_, ms)| *ms as f64 / 1000.0).sum::<f64>()
    );
    Ok(())
}

fn run_lint(args: &Args) -> Result<Option<usize>, String> {
    let session = Session {
        lints: args.lints.as_deref(),
        options: &args.options,
        log: args.log.as_deref(),
        fix: args.fix,
        jobs: args.jobs,
    };
    let start = || start(args).map(|server| Box::new(server) as Box<dyn Prover>);
    let (findings, failed) = session.lint_files(&args.files, start, &mut std::io::stdout())?;
    if failed > 0 {
        return Err(format!("{failed} files failed"));
    }
    Ok(Some(findings))
}

/// Each file gets a linter process of its own, so that one that hangs can be killed.
fn run_corpus(args: &Args) -> Result<(), String> {
    let (linter, log_flag) = if args.tool.is_empty() {
        let exe = std::env::current_exe().map_err(|e| e.to_string())?;
        let mut linter = vec![
            exe.display().to_string(),
            "-F".into(),
            "-j".into(),
            "1".into(),
        ];
        linter.extend(["-s".to_string(), args.server.join(" ")]);
        if let Some(lints) = &args.lints {
            linter.extend(["-l".to_string(), lints.join(",")]);
        }
        for assignment in &args.assignments {
            linter.extend(["-o".to_string(), assignment.clone()]);
        }
        (linter, Some("-L".to_string()))
    } else {
        (args.tool.clone(), None)
    };
    let out = args.out.clone().unwrap();
    let corpus = Corpus {
        out: out.clone(),
        project: args.project.clone(),
        linter,
        log_flag,
        build: args.check.clone(),
        limit: args.limit,
        jobs: args.jobs,
    };
    let summary = corpus.run(&args.files)?;
    write(&Some(out.join("summary.tsv")), summary.to_tsv())?;
    println!("{}", summary.sentence());
    Ok(())
}

fn main() -> ExitCode {
    let args = match parse() {
        Ok(args) => args,
        Err(message) => {
            eprintln!("{message}\n\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    let result = match args.mode.as_str() {
        "census" => run_census(&args).map(|_| None),
        "retime" => run_retime(&args).map(|_| None),
        "run" => run_corpus(&args).map(|_| None),
        _ => run_lint(&args),
    };
    match result {
        Ok(count) => {
            if let Some(count) = count {
                println!("\n{count} findings");
            }
            ExitCode::SUCCESS
        }
        Err(message) => {
            eprintln!("*** {message}");
            ExitCode::FAILURE
        }
    }
}
