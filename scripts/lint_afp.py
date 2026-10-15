#!/usr/bin/env python3
"""Run a lint with -F on copies of AFP entries, then rebuild the copies to check the fixes.

Usage: scripts/lint_afp.py LINT [-o OPTION]... ENTRY...  |  ... LINT [-o OPTION]... -n N  |  ... -s DIR
Copies go to census/LINT, logs and question logs (SESSION.tsv) to census/LINT/logs; built entries
and finished sessions are skipped. -o options go to the linter.
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
def copy(entry, out, afp=AFP, suffix=SUFFIX):
    target = out / entry
    shutil.rmtree(target, ignore_errors=True)
    shutil.copytree(afp / entry, target)
    root = (target / "ROOT").read_text()
    names = SESSION.findall(root)
    (target / "ROOT").write_text(rename_root(root, names, suffix))
    for thy in target.rglob("*.thy"):
        thy.write_text(qualify(thy.read_text(), names, suffix))
    return [n + suffix for n in names]


# theory names qualified by one of the sessions get the suffix on the session; file names
# like PAC_Checker.thy are left alone
def qualify(text, names, suffix):
    for name in names:
        text = re.sub(r"(?<![\w.])" + re.escape(name) + r"\.(?=\w)(?!thy\b)", name + suffix + ".", text)
    return text


ROOT_KEYWORDS = {"chapter", "session", "sessions", "theories", "options", "description", "directories",
                 "document_files", "document_theories", "export_files", "export_classpath", "global_theories"}


# session names, parents, `sessions` lists and qualified theory names of the entry's own sessions;
# no PDF document
def rename_root(root, names, suffix):
    def whole(name):
        return r'(?<![\w+.-])"?' + re.escape(name) + r'"?(?![\w+.-])'

    lines, section = [], None
    for line in root.splitlines(keepends=True):
        keyword = re.match(r"\s*([a-z_]+)\b", line)
        if keyword and keyword.group(1) in ROOT_KEYWORDS:
            section = keyword.group(1)
        for name in names:
            if section == "session":
                line = re.sub(r'(session\s+)' + whole(name), rf'\1"{name}{suffix}"', line)
                line = re.sub(r'(=\s*)' + whole(name) + r'(\s*\+)', rf'\1"{name}{suffix}"\2', line)
            elif section == "sessions":
                line = re.sub(whole(name), f'"{name}{suffix}"', line)
        lines.append(line)
    root = re.sub(r'\bdocument\s*=\s*"?pdf"?', "document = false", "".join(lines))
    return qualify(root, names, suffix)


# its fixes are in the copy: the run ended and applied any it found
def finished(log):
    text = log.read_text() if log.exists() else ""
    found = re.search(r"^(\d+) findings$", text, re.M)
    return bool(found) and (found.group(1) == "0" or "Fixed " in text)


# a copy with finished sessions is resumed, not copied again
def lint(name, entry, out, options):
    logs = out / "logs"
    sessions = [n + SUFFIX for n in SESSION.findall((AFP / entry / "ROOT").read_text())]
    if not any(finished(logs / f"{s}.log") for s in sessions):
        copy(entry, out)
    for s in sessions:
        if not finished(logs / f"{s}.log"):
            (logs / f"{s}.tsv").unlink(missing_ok=True)
            question_log = ["-o", f"linter_log={(logs / f'{s}.tsv').resolve()}"]
            run(["isabelle", "linter", "-l", name, "-F", *options, *question_log, "-d", AFP, "-d", out / entry, s],
                logs / f"{s}.log")
    rc = run(["isabelle", "build", "-d", AFP, "-d", out / entry, "-o", "document=false", *sessions],
             logs / f"{entry}.build")
    # a session whose lint stopped (e.g. the prover died) keeps its copy unpatched
    unfinished = [s for s in sessions if not finished(logs / f"{s}.log")]
    print(entry, "ok" if rc == 0 else "FAILED", *(["lint unfinished:", *unfinished] if unfinished else []), flush=True)


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
        name, rest, options = args[0], args[1:], []
        while rest[:1] == ["-o"]:
            options, rest = options + rest[:2], rest[2:]
        entries = rest if rest[:1] != ["-n"] else \
            sorted(random.Random(1).sample(SAMPLE.read_text().split(), int(rest[1])))
        out = Path("census") / name
        (out / "logs").mkdir(parents=True, exist_ok=True)
        for entry in entries:
            if not (out / "logs" / f"{entry}.build").exists():
                lint(name, entry, out, options)
