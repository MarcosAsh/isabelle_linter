#!/usr/bin/env python3
"""Run a lint with -F on copies of AFP entries, then rebuild the copies to check the fixes.

Usage: scripts/lint_afp.py LINT ENTRY...  |  scripts/lint_afp.py LINT -n N  |  scripts/lint_afp.py -s DIR
Copies go to census/LINT, logs to census/LINT/logs; built entries and finished sessions are skipped.
"""

import os
import random
import re
import shutil
import subprocess
import sys
from collections import Counter
from pathlib import Path

AFP = Path(os.environ.get("AFP", "~/dev/etc/afp/afp-2026-10-01/thys")).expanduser()
SAMPLE = Path(__file__).parent / "entries.txt"
SUFFIX = "_Patched"
SESSION = re.compile(r'^\s*session\s+"?([\w+.-]+)"?', re.M)


def run(command, log):
    with open(log, "w") as out:
        return subprocess.run(command, stdout=out, stderr=subprocess.STDOUT).returncode


# the copy's sessions get SUFFIX, and so do session-qualified theory names in its theories
def copy(entry, out):
    target = out / entry
    shutil.rmtree(target, ignore_errors=True)
    shutil.copytree(AFP / entry, target)
    root = (target / "ROOT").read_text()
    names = SESSION.findall(root)
    for name in names:
        q = re.escape(name)
        root = re.sub(r'(session\s+)"?' + q + r'"?', rf'\1"{name}{SUFFIX}"', root)
        root = re.sub(r'(=\s*)"?' + q + r'"?(\s*\+)', rf'\1"{name}{SUFFIX}"\2', root)
    (target / "ROOT").write_text(root)
    for thy in target.rglob("*.thy"):
        text = thy.read_text()
        for name in names:
            text = re.sub(r"(?<![\w.])" + re.escape(name) + r"\.(?=\w)", name + SUFFIX + ".", text)
        thy.write_text(text)
    (out / "ROOTS").write_text("\n".join(sorted(p.parent.name for p in out.glob("*/ROOT"))) + "\n")
    return [n + SUFFIX for n in names]


# its fixes are in the copy: the run ended and applied any it found
def finished(log):
    text = log.read_text() if log.exists() else ""
    found = re.search(r"^(\d+) findings$", text, re.M)
    return bool(found) and (found.group(1) == "0" or "Fixed " in text)


# a copy with finished sessions is resumed, not copied again
def lint(name, entry, out):
    logs = out / "logs"
    sessions = [n + SUFFIX for n in SESSION.findall((AFP / entry / "ROOT").read_text())]
    if not any(finished(logs / f"{s}.log") for s in sessions):
        copy(entry, out)
    for s in sessions:
        if not finished(logs / f"{s}.log"):
            run(["isabelle", "linter", "-l", name, "-F", "-d", AFP, "-d", out, s], logs / f"{s}.log")
    rc = run(["isabelle", "build", "-d", AFP, "-d", out, "-o", "document=false", *sessions],
             logs / f"{entry}.build")
    print(entry, "ok" if rc == 0 else "FAILED", flush=True)


def summary(out):
    text = "".join(p.read_text() for p in (out / "logs").glob("*.log"))
    pieces = Counter(re.findall(r"^  (fact|assumption|`have|`apply)", text, re.M))
    times = [(int(a), int(b)) for a, b in re.findall(r"^time: (\d+) ms as written, (\d+) ms", text, re.M)]
    swaps = [(int(b), int(a)) for a, b in re.findall(r"takes (\d+) ms instead of (\d+) ms", text)]
    builds = {p.stem: p.read_text() for p in (out / "logs").glob("*.build")}
    failed = [e for e, t in builds.items() if "Unfinished session" in t]
    running = [e for e, t in builds.items() if not re.search(r"^[\d:]+ elapsed time", t, re.M)]
    print("findings:", sum(map(int, re.findall(r"^(\d+) findings$", text, re.M))))
    if pieces:
        print("pieces:", dict(pieces))
    for label, pairs in (("unused fixes", times), ("faster_step swaps", swaps)):
        if pairs:
            print(f"{label}: {len(pairs)}, {sum(a for a, _ in pairs)} ms -> {sum(b for _, b in pairs)} ms")
    print(f"builds: {len(builds) - len(failed) - len(running)} ok, {len(failed)} failed {failed}, "
          f"{len(running)} running")


if __name__ == "__main__":
    args = sys.argv[1:]
    if args[0] == "-s":
        summary(Path(args[1]))
    else:
        name, rest = args[0], args[1:]
        entries = rest if rest[:1] != ["-n"] else \
            sorted(random.Random(1).sample(SAMPLE.read_text().split(), int(rest[1])))
        out = Path("census") / name
        (out / "logs").mkdir(parents=True, exist_ok=True)
        for entry in entries:
            if not (out / "logs" / f"{entry}.build").exists():
                lint(name, entry, out)
