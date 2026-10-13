#!/usr/bin/env python3
"""Build the AFP keeping command timings in the build logs, for isabelle linter_census.

Usage: scripts/census_build.py [-j JOBS] [-t THREADS] [ENTRY...]    (default: every entry)
Sessions marked slow, very_slow or large are left out; built sessions are skipped, so it resumes.
Log: census/build.log
"""

import os
import subprocess
import sys
from pathlib import Path

AFP = Path(os.environ.get("AFP", "~/dev/etc/afp/afp-2026-10-01/thys")).expanduser()
LOG = Path("census/build.log")


def command(entries, jobs, threads):
    dirs = [arg for entry in entries for arg in ("-D", str(AFP / entry))]
    return ["isabelle", "build", "-d", str(AFP), *dirs, "-X", "slow", "-X", "very_slow", "-X", "large",
            "-j", jobs, "-o", f"threads={threads}", "-o", "build_timing_threshold=0.01",
            "-o", "document=false", "-v"]


if __name__ == "__main__":
    args, jobs, threads = sys.argv[1:], "2", "8"
    while args[:1] in (["-j"], ["-t"]):
        jobs, threads = (args[1], threads) if args[0] == "-j" else (jobs, args[1])
        args = args[2:]
    entries = args or sorted(root.parent.name for root in AFP.glob("*/ROOT"))
    LOG.parent.mkdir(exist_ok=True)
    with open(LOG, "w") as log:
        sys.exit(subprocess.run(command(entries, jobs, threads), stdout=log, stderr=subprocess.STDOUT).returncode)
