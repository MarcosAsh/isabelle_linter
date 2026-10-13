#!/usr/bin/env python3
"""Replay the edits in patched AFP copies on another AFP release, and see which still check.

Usage: scripts/replay.py [-i ISABELLE] [-n] PATCHED NEW_AFP OUT
PATCHED holds copies with edits, as lint_afp.py makes them (census/faster_step); the edits are
their differences from the originals in $AFP. Each edit whose old text occurs exactly once in the
new release's file is applied to a copy of the new entry in OUT. The copy is built; the edits at
its errors are undone and it is built again, until it builds. -n applies the edits but builds
nothing. Writes OUT/replay.tsv: entry, file, line, status, old text, new text, where status is
survives, broken, gone (old text not in the new release), ambiguous or unbuilt.
"""

import csv
import difflib
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from lint_afp import AFP, SUFFIX, copy

REPLAY = "_Replay"
ERROR = re.compile(r'\(line (\d+) of "([^"]+)"\)')


class Edit:
    def __init__(self, entry, file, old, new):
        self.entry, self.file, self.old, self.new = entry, file, old, new
        self.status, self.line, self.lines = "unbuilt", 0, (0, 0)


# changed lines with enough context on each side that the old text occurs once in the original;
# edits whose context overlaps become one
def edits(entry, patched):
    found = []
    for thy in sorted((patched / entry).rglob("*.thy")):
        file = thy.relative_to(patched / entry)
        before = (AFP / entry / file).read_text().splitlines(keepends=True)
        after = thy.read_text().replace(SUFFIX + ".", ".").splitlines(keepends=True)
        ops = difflib.SequenceMatcher(None, before, after, autojunk=False).get_opcodes()
        windows = [context(before, i1, i2) for op, i1, i2, _, _ in ops if op != "equal"]
        for lo, hi in merge(windows):
            old = "".join(before[lo:hi])
            new = "".join(after[position(ops, lo):position(ops, hi)])
            found.append(Edit(entry, file, old, new))
    return found


def context(before, i1, i2):
    original = "".join(before)
    for k in range(1, 20):
        lo, hi = max(i1 - k, 0), min(i2 + k, len(before))
        if original.count("".join(before[lo:hi])) == 1:
            break
    return lo, hi


def merge(windows):
    merged = []
    for lo, hi in sorted(windows):
        if merged and lo < merged[-1][1]:
            merged[-1] = (merged[-1][0], max(hi, merged[-1][1]))
        else:
            merged.append((lo, hi))
    return merged


# a line of the original that is unchanged, as a line of the patched file
def position(ops, i):
    for op, i1, i2, j1, _ in ops:
        if op == "equal" and i1 <= i <= i2:
            return j1 + i - i1
    raise ValueError(f"line {i} is not unchanged")


# the new release's file with the live edits applied; each applied edit learns its lines there
def write(target, file, pristine, live):
    placed = sorted((pristine.index(e.old), e) for e in live)
    out, at = [], 0
    for pos, e in placed:
        out.append(pristine[at:pos])
        start = "".join(out).count("\n") + 1
        out.append(e.new)
        e.lines = (start, start + e.new.count("\n"))
        at = pos + len(e.old)
    out.append(pristine[at:])
    (target / file).write_text("".join(out))


# the live edit an error is at: the error's command starts at or a few lines before the edit
def culprit(live, file, line):
    near = [e for e in live if e.file == file and line - 1 <= e.lines[1] and e.lines[0] <= line + 20]
    return min(near, key=lambda e: abs(e.lines[0] - line)) if near else None


def replay(entry, patched, new_afp, out, isabelle, build):
    found = edits(entry, patched)
    if not (new_afp / entry).exists():
        for e in found:
            e.status = "gone"
        return found
    sessions = copy(entry, out, afp=new_afp, suffix=REPLAY)
    target = out / entry
    pristine = {e.file: (target / e.file).read_text() for e in found if (target / e.file).exists()}
    for e in found:
        n = pristine.get(e.file, "").count(e.old)
        e.status = "unbuilt" if n == 1 else ("gone" if n == 0 else "ambiguous")

    live = [e for e in found if e.status == "unbuilt"]
    for _ in range(50):
        for file in pristine:
            write(target, file, pristine[file], [e for e in live if e.file == file])
        if not build:
            return found
        log = out / "logs" / f"{entry}.build"
        with open(log, "w") as f:
            rc = subprocess.run([isabelle, "build", "-d", new_afp, "-d", out, "-o", "document=false", *sessions],
                                stdout=f, stderr=subprocess.STDOUT).returncode
        if rc == 0:
            for e in live:
                e.status = "survives"
            return found
        guilty = set()
        for line, path in ERROR.findall(log.read_text()):
            path = Path(path).expanduser().resolve()
            if path.is_relative_to(target.resolve()):
                e = culprit(live, path.relative_to(target.resolve()), int(line))
                if e:
                    guilty.add(e)
        if not guilty:
            print(entry, "fails at errors no edit explains; see", log, flush=True)
            return found
        for e in guilty:
            e.status = "broken"
        live = [e for e in live if e not in guilty]
    return found


if __name__ == "__main__":
    args, isabelle, build = sys.argv[1:], "isabelle", True
    while args[0] in ("-i", "-n"):
        if args[0] == "-i":
            isabelle, args = args[1], args[2:]
        else:
            build, args = False, args[1:]
    patched, new_afp, out = (Path(a).expanduser() for a in args)
    (out / "logs").mkdir(parents=True, exist_ok=True)
    rows = []
    for entry in sorted(p.parent.name for p in patched.glob("*/ROOT")):
        found = replay(entry, patched, new_afp, out, isabelle, build)
        rows += [[e.entry, e.file, e.lines[0], e.status, e.old, e.new] for e in found]
        print(entry, {s: sum(e.status == s for e in found) for s in {e.status for e in found}}, flush=True)
    with open(out / "replay.tsv", "w", newline="") as f:
        w = csv.writer(f, delimiter="\t")
        w.writerow(["entry", "file", "line", "status", "old", "new"])
        w.writerows(rows)
