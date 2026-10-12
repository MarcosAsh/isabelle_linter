#!/usr/bin/env python3
"""Apply faster_step findings to a copy of each AFP entry, whose sessions get the suffix _Patched.

Usage: scripts/apply_findings.py [--build] LOG... [--out DIR]    (default: census/patched)

The original entries stay as they are, so both can be built side by side:
  isabelle build -d $AFP -d census/patched -o document=false MiniSail_Patched
--build runs that build for every patched session.
"""

import os
import re
import shutil
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

AFP = Path(os.environ.get("AFP", "~/dev/etc/afp/afp-2026-10-01/thys")).expanduser()
SUFFIX = "_Patched"

# methods may span lines, so the whole log is matched at once
FINDING = re.compile(
    r"^(/\S+?\.thy):(\d+): \[faster_step\] `by (.*?)` takes \d+ ms instead of \d+ ms for `by (.*?)`$",
    re.M | re.S)


def findings(logs):
    """(file, line, new, old) for every faster_step finding."""
    return [(Path(f), int(line), new, old)
            for log in logs for f, line, new, old in FINDING.findall(Path(log).read_text())]


def entry_of(path):
    return path.relative_to(AFP).parts[0]


def copy_entry(entry, out):
    target = out / entry
    if target.exists():
        shutil.rmtree(target)
    shutil.copytree(AFP / entry, target)
    names = rename_sessions(target / "ROOT")
    for thy in target.rglob("*.thy"):
        rename_imports(thy, [n[:-len(SUFFIX)] for n in names])
    return target


def rename_imports(thy, names):
    """Theory names qualified by session, such as Polynomials.MPoly_Type in imports and
    antiquotations, follow the renamed session (constants are qualified by theory, not session)."""
    text = thy.read_text()
    for name in names:
        text = re.sub(r"(?<![\w.])" + re.escape(name) + r"\.(?=\w)", name + SUFFIX + ".", text)
    thy.write_text(text)


def rename_sessions(root):
    """Rename each session and the parents that name a sibling; theory names stay."""
    text = root.read_text()
    names = re.findall(r'^\s*session\s+"?([\w+.-]+)"?', text, re.M)
    for name in names:
        quoted = re.escape(name)
        text = re.sub(r'(session\s+)"?' + quoted + r'"?', r'\g<1>"' + name + SUFFIX + '"', text)
        text = re.sub(r'(=\s*)"?' + quoted + r'"?(\s*\+)', r'\g<1>"' + name + SUFFIX + r'"\2', text)
    root.write_text(text)
    return [n + SUFFIX for n in names]


def apply(text, line, new, old):
    """Replace the first `by OLD` that starts on line; None if it is not there."""
    start = 0
    for _ in range(line - 1):
        start = text.index("\n", start) + 1
    m = re.compile(r"by\s*" + re.escape(old)).search(text, start)
    if m is None or text.count("\n", start, m.start()) > 0:
        return None
    return text[:m.start()] + "by " + new + text[m.end():]


def patch(found, out):
    by_entry = defaultdict(list)
    for f in found:
        by_entry[entry_of(f[0])].append(f)

    sessions, missed = [], []
    for entry, fs in sorted(by_entry.items()):
        target = copy_entry(entry, out)
        sessions += re.findall(r'^\s*session\s+"([\w+.-]+)"', (target / "ROOT").read_text(), re.M)
        # bottom-up, so earlier line numbers stay right
        for path, line, new, old in sorted(fs, key=lambda f: (f[0], -f[1])):
            copy = target / path.relative_to(AFP / entry)
            patched = apply(copy.read_text(), line, new, old)
            if patched is None:
                missed.append(f"{path}:{line}: by {old}")
            else:
                copy.write_text(patched)
        print(f"{entry}: {len(fs)} findings")
    for m in missed:
        print("not applied:", m)
    return sessions


def build(sessions, out):
    command = ["isabelle", "build", "-d", str(AFP), "-d", str(out), "-o", "document=false", *sessions]
    return subprocess.run(command).returncode


if __name__ == "__main__":
    args = sys.argv[1:]
    run_build = "--build" in args
    out = Path(args[args.index("--out") + 1]) if "--out" in args else Path("census/patched")
    logs = [a for i, a in enumerate(args) if a.endswith(".log") and (i == 0 or args[i - 1] != "--out")]
    out.mkdir(parents=True, exist_ok=True)
    (out / "ROOTS").write_text("")
    sessions = patch(findings(logs), out)
    (out / "ROOTS").write_text("\n".join(sorted({p.parent.name for p in out.glob("*/ROOT")})) + "\n")
    if run_build:
        sys.exit(build(sessions, out))
