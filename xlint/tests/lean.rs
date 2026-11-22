//! `census` and `retime` against the real Lean server. Skipped where `lake` is not installed.

use std::path::Path;
use std::process::Command;
use xlint::lint::{Lint, Options};
use xlint::lints::unused::Unused;
use xlint::prover::{Prover, Server};
use xlint::{census, fix, retime, rounds};

fn server() -> Option<Server> {
    let project = Path::new(env!("CARGO_MANIFEST_DIR")).join("../provers/lean");
    let built = Command::new("lake")
        .arg("build")
        .current_dir(&project)
        .output()
        .ok()?;
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stdout)
    );
    let binary = project.join(".lake/build/bin/xlint-lean");
    Some(Server::start(&[binary.display().to_string()]).unwrap())
}

#[test]
fn lean_times_the_commands_and_steps_of_the_example() {
    let Some(mut prover) = server() else {
        eprintln!("skipped: no lake");
        return;
    };
    let file = Path::new(env!("CARGO_MANIFEST_DIR")).join("../provers/lean/test/Example.lean");
    let file = file.display().to_string();
    let (rows, lost) = census::file_rows(&mut prover, &file, 30_000).unwrap();
    assert_eq!(lost, 0);
    let commands: Vec<&str> = rows
        .iter()
        .filter(|row| !row.is_step())
        .map(|row| row.command.as_str())
        .collect();
    assert_eq!(
        commands,
        [
            "theorem", "theorem", "theorem", "theorem", "check", "eval", "theorem"
        ]
    );
    let steps: Vec<&str> = rows
        .iter()
        .filter(|row| row.is_step())
        .map(|row| row.text.as_str())
        .collect();
    assert_eq!(steps.len(), 6);
    assert_eq!(steps[5], "simp_all");

    let slowest = retime::slowest(&rows, 2);
    let retimed = retime::file_steps(&mut server().unwrap(), &file, &slowest, 3, 30_000).unwrap();
    assert!(
        retimed
            .iter()
            .all(|step| step.verdict == "closes" && step.runs_ms.len() == 3)
    );
}

#[test]
fn lean_checks_a_lemma_like_a_theorem() {
    let Some(mut prover) = server() else {
        eprintln!("skipped: no lake");
        return;
    };
    let file = Path::new(env!("CARGO_MANIFEST_DIR")).join("../provers/lean/test/Lemma.lean");
    let loaded = prover.load(&file.display().to_string()).unwrap();
    let lemma = loaded.decls.iter().find(|decl| decl.name == "as_lemma");
    let lemma = lemma.expect("the lemma is a declaration");
    assert!(lemma.ok && lemma.kind == "theorem");
    assert_eq!(lemma.pieces.len(), 1);
}

#[test]
fn lean_drops_the_brackets_of_an_emptied_simp_list() {
    let Some(mut prover) = server() else {
        eprintln!("skipped: no lake");
        return;
    };
    let file = Path::new(env!("CARGO_MANIFEST_DIR")).join("../provers/lean/test/Lemma.lean");
    let loaded = prover.load(&file.display().to_string()).unwrap();
    let options = Options::default();
    let answers = rounds::run(&mut prover, &Unused, &loaded.decls, &options, None).unwrap();
    let findings = Unused.report(&loaded.decls, &answers, &options);
    let (edits, _) = fix::disjoint(&findings);
    let fixed = fix::apply(&std::fs::read_to_string(&file).unwrap(), &edits).unwrap();
    assert!(fixed.ends_with("n + 0 = n := by\n  simp\n"), "{fixed}");
}
