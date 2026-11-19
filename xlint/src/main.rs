//! xlint: lint proof files with the prover checking every suggestion.

use std::path::PathBuf;
use std::process::ExitCode;
use xlint::lint::{Finding, Options};
use xlint::prover::{Prover, Server};
use xlint::{fix, lints, rounds};

const USAGE: &str = "Usage: xlint -s SERVER [-F] [-l LINTS] [-L LOG] [-o NAME=VALUE] FILE...

  -s SERVER    the prover's server command, in one argument (\"lake exe xlint-lean\")
  -F           apply the fixes to the files
  -l LINTS     comma-separated lints to run (default: all)
  -L LOG       append every question and answer to LOG, as TSV
  -o NAME=VAL  set an option (timeout_ms, factor, batch, runs, unused_ahead,
               faster_step_slow_ms, faster_step_speedup)";

struct Args {
    server: Vec<String>,
    fix: bool,
    lints: Option<Vec<String>>,
    log: Option<PathBuf>,
    options: Options,
    files: Vec<String>,
}

fn parse() -> Result<Args, String> {
    let mut args = Args {
        server: Vec::new(),
        fix: false,
        lints: None,
        log: None,
        options: Options::default(),
        files: Vec::new(),
    };
    let mut argv = std::env::args().skip(1);
    while let Some(arg) = argv.next() {
        let mut value = || argv.next().ok_or(format!("{arg} needs a value"));
        match arg.as_str() {
            "-s" => args.server = value()?.split_whitespace().map(str::to_string).collect(),
            "-F" => args.fix = true,
            "-l" => args.lints = Some(value()?.split(',').map(str::to_string).collect()),
            "-L" => args.log = Some(PathBuf::from(value()?)),
            "-o" => args.options.set(&value()?)?,
            _ if arg.starts_with('-') => return Err(format!("unknown option {arg}")),
            _ => args.files.push(arg),
        }
    }
    if args.server.is_empty() || args.files.is_empty() {
        return Err("a server and a file are needed".to_string());
    }
    Ok(args)
}

fn lint_file(prover: &mut dyn Prover, file: &str, args: &Args) -> Result<Vec<Finding>, String> {
    let loaded = prover.load(file)?;
    let decls = &loaded.decls;
    eprintln!(
        "{file}: {} of {} declarations check",
        decls.iter().filter(|d| d.ok).count(),
        decls.len()
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
    // a server loads one file, so each file gets its own
    let result = args.files.iter().try_fold(0, |count, file| {
        let mut server = Server::start(&args.server)?;
        let hello = server.hello()?;
        eprintln!("{} {}", hello.prover, hello.version);
        Ok::<usize, String>(count + lint_file(&mut server, file, &args)?.len())
    });
    match result {
        Ok(count) => {
            println!("\n{count} findings");
            ExitCode::SUCCESS
        }
        Err(message) => {
            eprintln!("*** {message}");
            ExitCode::FAILURE
        }
    }
}
