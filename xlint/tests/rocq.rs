//! The lints, `census` and `retime` against the real Rocq server. Skipped where there is no opam
//! switch named `rocq`.

use std::path::Path;
use std::process::Command;
use std::sync::Once;
use xlint::lint::{Finding, Lint, Options};
use xlint::lints::diagnostic_commands::DiagnosticCommands;
use xlint::lints::faster_step::FasterStep;
use xlint::lints::unused::{Unused, UnusedImports};
use xlint::prover::{Prover, Server};
use xlint::{census, fix, retime, rounds};

const IN_SWITCH: [&str; 5] = ["opam", "exec", "--switch", "rocq", "--"];

fn server() -> Option<Server> {
    let project = Path::new(env!("CARGO_MANIFEST_DIR")).join("../provers/rocq");
    let in_switch = |args: &[&str]| {
        Command::new(IN_SWITCH[0])
            .args(&IN_SWITCH[1..])
            .args(args)
            .current_dir(&project)
            .output()
    };
    if !in_switch(&["rocq", "-v"]).is_ok_and(|output| output.status.success()) {
        return None;
    }
    // dune takes a lock on the build directory, and the tests run at once
    static BUILD: Once = Once::new();
    BUILD.call_once(|| {
        let built = in_switch(&["dune", "build"]).unwrap();
        assert!(
            built.status.success(),
            "{}",
            String::from_utf8_lossy(&built.stderr)
        );
    });
    let binary = project
        .join("_build/default/main.exe")
        .display()
        .to_string();
    let command: Vec<String> = IN_SWITCH
        .iter()
        .map(|s| s.to_string())
        .chain([binary])
        .collect();
    Some(Server::start(&command).unwrap())
}

#[test]
fn rocq_finds_the_tactics_a_proof_does_not_need() {
    let Some(mut prover) = server() else {
        eprintln!("skipped: no opam switch rocq");
        return;
    };
    let file = Path::new(env!("CARGO_MANIFEST_DIR")).join("../provers/rocq/test/Example.v");
    let source = std::fs::read_to_string(&file).unwrap();
    let loaded = prover.load(&file.display().to_string()).unwrap();
    let names: Vec<&str> = loaded.decls.iter().map(|decl| decl.name.as_str()).collect();
    assert_eq!(names, ["imports", "needed", "bullets", "keeps"]);
    assert!(loaded.decls.iter().all(|decl| decl.ok));

    let options = Options::default();
    let answers = rounds::run(&mut prover, &Unused, &loaded.decls, &options, None).unwrap();
    let findings = Unused.report(&loaded.decls, &answers, &options);
    let found: Vec<&str> = findings
        .iter()
        .map(|finding| finding.decl.as_str())
        .collect();
    assert_eq!(found.len(), 2, "{findings:?}");
    let (edits, _) = fix::disjoint(&findings);
    let fixed = fix::apply(&source, &edits).unwrap();
    assert!(!fixed.contains("h1") && !fixed.contains("unused") && !fixed.contains("simpl."));
    assert!(fixed.contains("assert (h' : n <> 0) by lia."));
}

fn lints_file() -> String {
    let file = Path::new(env!("CARGO_MANIFEST_DIR")).join("../provers/rocq/test/Lints.v");
    file.display().to_string()
}

#[test]
fn rocq_answers_the_other_lints() {
    let Some(mut prover) = server() else {
        eprintln!("skipped: no opam switch rocq");
        return;
    };
    let loaded = prover.load(&lints_file()).unwrap();
    let options = Options {
        faster_step_slow_ms: 100,
        ..Options::default()
    };
    let mut found = |lint: &dyn Lint| -> Vec<Finding> {
        let answers = rounds::run(&mut prover, lint, &loaded.decls, &options, None).unwrap();
        lint.report(&loaded.decls, &answers, &options)
    };

    let unused = found(&Unused);
    assert_eq!(unused.len(), 1, "{unused:?}");
    assert!(unused[0].message.contains("fact `Nat.add_comm`"));
    assert!(unused[0].message.contains("hint database `arith`"));

    let imports = found(&UnusedImports);
    assert_eq!(imports.len(), 1, "{imports:?}");
    assert!(imports[0].message.contains("import `Lia`"));
    assert!(imports[0].message.contains("import `List Bool`"));
    assert!(!imports[0].message.contains("`Arith`"));

    let faster = found(&FasterStep);
    assert_eq!(faster.len(), 1, "{faster:?}");
    assert!(
        faster[0]
            .message
            .contains("for `do 3000000 idtac; reflexivity`")
    );

    let commands: Vec<String> = DiagnosticCommands
        .read(&loaded)
        .iter()
        .map(|finding| finding.message.clone())
        .collect();
    assert_eq!(commands.len(), 2, "{commands:?}");
    assert!(commands[0].contains("Check Nat.add_comm.") && commands[0].contains("while writing"));
    assert!(commands[1].contains("Compute 2 + 2.") && commands[1].contains("test file"));
}

#[test]
fn rocq_times_the_commands_and_steps() {
    let Some(mut prover) = server() else {
        eprintln!("skipped: no opam switch rocq");
        return;
    };
    let file = lints_file();
    let (rows, lost) = census::file_rows(&mut prover, &file, 30_000).unwrap();
    assert_eq!(lost, 0);
    let steps: Vec<&str> = rows
        .iter()
        .filter(|row| row.is_step())
        .map(|row| row.text.as_str())
        .collect();
    assert_eq!(
        steps,
        [
            "do 3000000 idtac; reflexivity",
            "auto using Nat.add_comm, Nat.le_refl with arith",
            "apply Nat.add_0_r"
        ]
    );

    let slowest = retime::slowest(&rows, 1);
    assert_eq!(slowest[0].text, steps[0]);
    let retimed = retime::file_steps(&mut server().unwrap(), &file, &slowest, 3, 30_000).unwrap();
    assert!(retimed[0].verdict == "closes" && retimed[0].runs_ms.len() == 3);
}
