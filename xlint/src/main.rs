//! xlint: lint proof files with the prover checking every suggestion.

use std::path::PathBuf;
use std::process::ExitCode;
use xlint::lint::{Finding, Options};
use xlint::prover::{Prover, Server};
use xlint::{census, fix, lints, retime, rounds};

const USAGE: &str = "Usage: xlint -s SERVER [-F] [-l LINTS] [-L LOG] [-o NAME=VALUE] FILE...
       xlint census -s SERVER [-O TSV] [-n N] [-o timeout_ms=MS] FILE...
       xlint retime -s SERVER -I TSV [-O TSV] [-n N] [-o runs=N] [-o timeout_ms=MS]

  -s SERVER    the prover's server command, in one argument (\"lake exe xlint-lean\")
  -F           apply the fixes to the files
  -l LINTS     comma-separated lints to run (default: all)
  -L LOG       append every question and answer to LOG, as TSV
  -o NAME=VAL  set an option (timeout_ms, factor, batch, runs, unused_ahead,
               faster_step_slow_ms, faster_step_speedup, simp_hygiene_min,
               simp_scope_slow_ms, simp_scope_speedup)

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
        files: Vec::new(),
    };
    let mut argv = std::env::args().skip(1).peekable();
    if let Some(mode) = argv.next_if(|arg| arg == "census" || arg == "retime") {
        args.mode = mode;
    }
    while let Some(arg) = argv.next() {
        let mut value = || argv.next().ok_or(format!("{arg} needs a value"));
        match arg.as_str() {
            "-s" => args.server = value()?.split_whitespace().map(str::to_string).collect(),
            "-F" => args.fix = true,
            "-l" => args.lints = Some(value()?.split(',').map(str::to_string).collect()),
            "-L" => args.log = Some(PathBuf::from(value()?)),
            "-O" => args.output = Some(PathBuf::from(value()?)),
            "-I" => args.input = Some(PathBuf::from(value()?)),
            "-n" => args.top = Some(value()?.parse().map_err(|_| "-n needs a number")?),
            "-o" => args.options.set(&value()?)?,
            _ if arg.starts_with('-') => return Err(format!("unknown option {arg}")),
            _ => args.files.push(arg),
        }
    }
    let nothing_to_read = if args.mode == "retime" {
        args.input.is_none()
    } else {
        args.files.is_empty()
    };
    if args.server.is_empty() || nothing_to_read {
        return Err("a server and a file are needed".to_string());
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

fn lint_file(prover: &mut dyn Prover, file: &str, args: &Args) -> Result<Vec<Finding>, String> {
    let loaded = prover.load(file)?;
    let decls = &loaded.decls;
    eprintln!(
        "{file}: {} of {} declarations check",
        decls.iter().filter(|d| d.ok && d.kind != "imports").count(),
        decls.iter().filter(|d| d.kind != "imports").count()
    );
    let mut findings = Vec::new();
    for lint in lints::all() {
        if args
            .lints
            .as_ref()
            .is_some_and(|names| !names.iter().any(|n| n == lint.name()))
        {
            continue;
        }
        let answers = rounds::run(
            prover,
            lint.as_ref(),
            decls,
            &args.options,
            args.log.as_deref(),
        )?;
        findings.extend(lint.read(&loaded));
        findings.extend(lint.report(decls, &answers, &args.options));
    }
    for finding in &findings {
        println!(
            "\n{file}:{}: [{}] {}",
            finding.line, finding.lint, finding.message
        );
    }
    if args.fix {
        let (edits, fixed) = fix::disjoint(&findings);
        if !edits.is_empty() {
            let text = std::fs::read_to_string(file).map_err(|e| format!("{file}: {e}"))?;
            std::fs::write(file, fix::apply(&text, &edits)?).map_err(|e| format!("{file}: {e}"))?;
            println!("Fixed {fixed} findings in {file}");
        }
    }
    Ok(findings)
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
        _ => args
            .files
            .iter()
            .try_fold(0, |count, file| {
                Ok::<usize, String>(count + lint_file(&mut start(&args)?, file, &args)?.len())
            })
            .map(Some),
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
