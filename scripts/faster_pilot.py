#!/usr/bin/env python3
"""Run faster_step on the sessions that hold re-timed steps of at least 5 s, one log per session.

Usage: scripts/faster_pilot.py [RETIME.tsv] [OUT_DIR]    (default: census/retime.tsv census/faster)

Sessions whose log already ends with the findings line are skipped, so a run can resume.
"""

import csv
import os
import subprocess
import sys
from collections import Counter
from pathlib import Path

AFP = Path(os.environ.get("AFP", "~/dev/etc/afp/afp-2026-10-01/thys")).expanduser()
SLOW_MS = 5000


def sessions(retime):
    """Sessions with the most confirmed-slow steps first."""
    with open(retime) as f:
        rows = csv.DictReader(f, delimiter="\t")
        counts = Counter(r["session"] for r in rows
                         if r["verdict"] == "closes" and int(r["median_ms"]) >= SLOW_MS)
    return [s for s, _ in counts.most_common()]


def finished(log):
    return log.is_file() and log.read_text().rstrip().endswith("findings")


def lint(session, log):
    # 300 s per question, so the slowest steps are not skipped; 3 s as faster_step's own times are noisy
    command = ["isabelle", "linter", "-l", "faster_step", "-d", str(AFP),
               "-o", "faster_step_slow=3", "-o", "linter_timeout=300", session]
    with open(log, "w") as out:
        subprocess.run(command, stdout=out, stderr=subprocess.STDOUT)


if __name__ == "__main__":
    retime = Path(sys.argv[1] if len(sys.argv) > 1 else "census/retime.tsv")
    out = Path(sys.argv[2] if len(sys.argv) > 2 else "census/faster")
    out.mkdir(parents=True, exist_ok=True)
    for session in sessions(retime):
        log = out / (session + ".log")
        if not finished(log):
            lint(session, log)
