//! `census` and `retime` against the real Lean server. Skipped where `lake` is not installed.

use std::path::Path;
use std::process::Command;
use xlint::prover::Server;
use xlint::{census, retime};

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
