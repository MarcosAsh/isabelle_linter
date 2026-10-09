#!/usr/bin/env python3
"""Build a fixed random sample of AFP entries, keeping command timings in the build logs.

Usage: scripts/build_afp.py [N]    then: isabelle linter_census -O timings.tsv
"""

import os
import random
import subprocess
import sys
from pathlib import Path

AFP = Path(os.environ.get("AFP", "~/dev/etc/afp/afp-2026-10-01/thys")).expanduser()
HERE = Path(__file__).parent
ENTRIES = HERE / "entries.txt"


def sample(n):
    if not ENTRIES.exists():
        entries = sorted(root.parent.name for root in AFP.glob("*/ROOT"))
        chosen = sorted(random.Random(0).sample(entries, n))
        ENTRIES.write_text("\n".join(chosen) + "\n")
    return ENTRIES.read_text().split()


def build(entries):
    dirs = [arg for entry in entries for arg in ("-D", str(AFP / entry))]
    command = ["isabelle", "build", "-d", str(AFP), *dirs,
               "-X", "slow", "-X", "very_slow", "-X", "large",
               "-j", "3", "-o", "threads=6", "-o", "build_timing_threshold=0.01", "-v"]
    with open(HERE / "build.log", "w") as log:
        return subprocess.run(command, stdout=log, stderr=subprocess.STDOUT).returncode


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    sys.exit(build(sample(n)))
