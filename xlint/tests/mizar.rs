//! The Mizar wrapper on an article with known unneeded pieces. Skipped where Mizar is not in
//! `~/opt/mizar`.

use std::path::Path;
use std::process::Command;

#[test]
fn mizar_tools_report_as_findings() {
    let home = std::env::var("HOME").unwrap_or_default();
    let mizar = Path::new(&home).join("opt/mizar");
    if !mizar.join("bin/verifier").exists() {
        eprintln!("skipped: no ~/opt/mizar");
        return;
    }
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../provers/mizar");
    let path = format!(
        "{}:{}",
        mizar.join("bin").display(),
        std::env::var("PATH").unwrap_or_default()
    );
    let output = Command::new(dir.join("xlint-mizar"))
        .arg("test/example.miz")
        .current_dir(&dir)
        .env("MIZFILES", mizar.join("share"))
        .env("PATH", path)
        .output()
        .unwrap();
    let found = String::from_utf8_lossy(&output.stdout);
    let lines: Vec<&str> = found.lines().filter(|line| !line.is_empty()).collect();
    assert_eq!(
        lines,
        [
            "test/example.miz:16: [unused] relprem: Irrelevant reference (column 51)",
            "test/example.miz:16: [unused] relinfer: Irrelevant inference (column 39)",
            "test/example.miz:20: [unused] trivdemo: Justification can be straightforward (column 5)",
            "test/example.miz:6: [unused_imports] irrths: Unnecessary item in the \"theorems\" directive (column 28)",
            "test/example.miz:3: [unused_imports] irrvoc: Irrelevant item in the \"vocabularies\" directive (column 22)",
            "5 findings"
        ]
    );
    let counted = String::from_utf8_lossy(&output.stderr);
    assert_eq!(counted.trim(), "test/example.miz: 3 theorems, 3 steps");
}
