#!/usr/bin/env python3
"""Measure the unused lint: on copies of N sampled AFP entries, apply its fixes, then rebuild.

Usage: scripts/unused_pilot.py [N] [--out DIR]    (default: 20, census/unused)

Each entry is copied with its sessions renamed (as apply_findings.py does), each of its census
sessions is linted with -F, one log per session in DIR/logs, then the copies are built; the build's
log goes to DIR/logs/ENTRY.build. Entries with a build log are skipped, so a run can resume.
"""

import csv
import random
import re
import subprocess
import sys
from pathlib import Path

from apply_findings import AFP, SUFFIX, copy_entry

HERE = Path(__file__).parent


def census_sessions(sample="census/sample.tsv"):
    with open(sample) as f:
        return {r["session"] for r in csv.DictReader(f, delimiter="\t")}


def entries(n):
    """N entries of the census sample, fixed seed, that hold at least one census session."""
    known = census_sessions()
    chosen = [e for e in (HERE / "entries.txt").read_text().split() if sessions_of(AFP / e) & known]
    return sorted(random.Random(1).sample(chosen, min(n, len(chosen))))


def sessions_of(entry_dir):
    return set(re.findall(r'^\s*session\s+"?([\w+.-]+)"?', (entry_dir / "ROOT").read_text(), re.M))


def run(command, log):
    with open(log, "w") as out:
        return subprocess.run(command, stdout=out, stderr=subprocess.STDOUT).returncode


def pilot(entry, out, logs):
    known = census_sessions()
    target = copy_entry(entry, out)
    (out / "ROOTS").write_text("\n".join(sorted(p.parent.name for p in out.glob("*/ROOT"))) + "\n")
    linted = []
    for session in sorted(s for s in sessions_of(AFP / entry) if s in known):
        name = session + SUFFIX
        run(["isabelle", "linter", "-l", "unused", "-F", "-d", str(AFP), "-d", str(out), name],
            logs / (name + ".log"))
        linted.append(name)
    rc = run(["isabelle", "build", "-d", str(AFP), "-d", str(out), "-o", "document=false", *linted],
             logs / (entry + ".build"))
    print(f"{entry}: {len(linted)} sessions, build {'ok' if rc == 0 else 'FAILED'}", flush=True)


if __name__ == "__main__":
    args = sys.argv[1:]
    out = Path(args[args.index("--out") + 1]) if "--out" in args else Path("census/unused")
    n = int(args[0]) if args and args[0].isdigit() else 20
    logs = out / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    for entry in entries(n):
        if not (logs / (entry + ".build")).exists():
            pilot(entry, out, logs)
