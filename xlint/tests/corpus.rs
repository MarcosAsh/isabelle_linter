//! The corpus runner with a shell script as linter: summary, check, time limit and resuming.

use std::path::{Path, PathBuf};
use xlint::corpus::{Corpus, read};

const LOG: &str = "
A.lean:3: [unused] not needed:
  fact `h1` (line 4)
  have `have h2 : x = x := rfl` (line 5)
time: 40 ms as written, 30 ms with the fix (medians, alone)
not needed, but removing them changes the statement:
  assumption `(h : 0 < n)` (line 3)

A.lean:9: [unused] not needed, but removing them changes the statement:
  assumption `(k : Nat)` (line 9)

A.lean:20: [faster_step] `omega` takes 3 ms in place of 90 ms for `simp [foo]: [x]`
Fixed 2 findings in A.lean
";

#[test]
fn a_log_is_read_into_a_row() {
    let questions = "xlint\tjobs\t2 files at once\t\t\t\nunused\tk:original\trun \tcloses\t40\t\nunused\tk:drop:0\trun 1-2:\tunanswered\t\t\n";
    let row = read(
        "A.lean",
        LOG,
        "A.lean: 12 theorems, 40 steps\n",
        questions,
        "ok\n",
    );
    assert_eq!(
        (row.lemmas, row.steps, row.findings, row.other),
        (12, 40, 2, 1)
    );
    assert_eq!(row.kinds.get("fact"), Some(&1));
    assert_eq!(row.kinds.get("have"), Some(&1));
    assert_eq!((row.removed(), row.kept, row.fixed), (2, 2, 2));
    assert_eq!((row.timed, row.before_ms, row.after_ms), (1, 40, 30));
    assert_eq!((row.questions, row.unanswered), (2, 1));
    assert_eq!(row.build, "ok");
}

#[test]
fn a_tool_with_one_hit_per_finding_counts_by_tool() {
    let log = "\na.miz:16: [unused] relprem: Irrelevant reference (column 51)\n\na.miz:16: [unused] relinfer: Irrelevant inference (column 39)\n\na.miz:3: [unused_imports] irrvoc: Irrelevant item (column 22)\n";
    let row = read("a.miz", log, "a.miz: 3 theorems, 3 steps\n", "", "ok\n");
    assert_eq!((row.findings, row.removed(), row.other), (2, 2, 1));
    assert_eq!(row.kinds.get("relprem"), Some(&1));
}

/// A linter that deletes the word `unneeded` from the file and reports it; `hang.txt` never ends.
fn linter(dir: &Path) -> String {
    let script = dir.join("linter.sh");
    std::fs::write(
        &script,
        "#!/bin/sh\ncase \"$1\" in hang*) sleep 60 ;; esac\necho ran >> ../ran\necho \"$1: 1 theorems, 2 steps\" >&2\nif grep -q unneeded \"$1\"; then\n  printf '\\n%s:1: [unused] not needed:\\n  fact `unneeded` (line 1)\\nFixed 1 findings in %s\\n' \"$1\" \"$1\"\n  sed -i 's/unneeded//' \"$1\"\nfi\n",
    )
    .unwrap();
    script.display().to_string()
}

fn corpus(dir: &Path) -> Corpus {
    Corpus {
        out: dir.join("out"),
        project: Some(dir.join("project")),
        linter: vec!["sh".to_string(), linter(dir)],
        log_flag: None,
        // bad.txt fails once fixed, and base.txt fails as written too
        build: [
            "sh",
            "-c",
            "case $0 in base*) exit 1 ;; bad*) grep -q unneeded $0 ;; esac",
        ]
        .map(str::to_string)
        .to_vec(),
        limit: Some(2),
        jobs: 2,
    }
}

fn project(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("xlint-corpus-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("project")).unwrap();
    for file in ["a.txt", "bad.txt", "base.txt", "clean.txt", "hang.txt"] {
        let text = if file == "clean.txt" {
            "needed\n"
        } else {
            "needed unneeded\n"
        };
        std::fs::write(dir.join("project").join(file), text).unwrap();
    }
    dir
}

#[test]
fn files_are_fixed_checked_and_added_up() {
    let dir = project("run");
    let files = ["a.txt", "bad.txt", "base.txt", "clean.txt", "hang.txt"].map(str::to_string);
    let summary = corpus(&dir).run(&files).unwrap();
    let builds: Vec<&str> = summary.rows.iter().map(|row| row.build.as_str()).collect();
    assert_eq!(
        builds,
        ["ok", "FAILED", "baseline-fails", "ok", "lint timeout"]
    );
    // the files whose check passed: a.txt with its piece, clean.txt with none
    let total = &summary.total;
    assert_eq!(
        (
            total.lemmas,
            total.steps,
            total.findings,
            total.removed(),
            total.fixed
        ),
        (2, 4, 1, 1, 1)
    );
    let copy = |file: &str| std::fs::read_to_string(dir.join("out/copy").join(file)).unwrap();
    assert_eq!(copy("a.txt"), "needed \n");
    assert_eq!(copy("bad.txt"), "needed unneeded\n");
    assert_eq!(
        std::fs::read_to_string(dir.join("project/a.txt")).unwrap(),
        "needed unneeded\n"
    );
    assert!(summary.to_tsv().lines().count() == 7);

    // a second run finds every file done and lints nothing
    let ran = std::fs::read_to_string(dir.join("out/ran")).unwrap();
    let again = corpus(&dir).run(&files).unwrap();
    assert_eq!(std::fs::read_to_string(dir.join("out/ran")).unwrap(), ran);
    assert_eq!(again.total, summary.total);
    std::fs::remove_dir_all(dir).unwrap();
}
