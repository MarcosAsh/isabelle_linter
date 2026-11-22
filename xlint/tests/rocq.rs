//! `unused` against the real Rocq server. Skipped where there is no opam switch named `rocq`.

use std::path::Path;
use std::process::Command;
use xlint::lint::{Lint, Options};
use xlint::lints::unused::Unused;
use xlint::prover::{Prover, Server};
use xlint::{fix, rounds};

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
    let built = in_switch(&["dune", "build"]).unwrap();
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
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
    assert_eq!(names, ["needed", "bullets", "keeps"]);
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
