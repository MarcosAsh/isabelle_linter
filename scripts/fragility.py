#!/usr/bin/env python3
"""Are slow steps the ones that change between AFP releases?

Usage: scripts/fragility.py CENSUS.tsv OLD_THYS NEW_THYS [-O STEPS.tsv]
CENSUS is linter_census output for theories in OLD_THYS (offsets are Isabelle symbol offsets).
A step changed if any of its lines differ in the same file of NEW_THYS, ignoring the 2026
`smt` -> `smt (z3)` rewrite; gone if the file is.
Prints the share of `by`/`apply` steps that changed, by census time band and by method.
"""

import csv
import difflib
import re
import sys
from collections import defaultdict
from pathlib import Path

SYMBOL = re.compile(r"\\<\^?[A-Za-z0-9_']+>|.", re.S)
BANDS = [(0, 0.1), (0.1, 1), (1, 5), (5, float("inf"))]
STEPS = {"by", "apply"}

# a release-wide rewrite that breaks nothing: Isabelle2026 spells plain smt as `smt (z3)`
MECHANICAL = re.compile(r"\bsmt \(z3\)")


# 1-based symbol offset -> 0-based line, for each offset asked
def lines_at(text, offsets):
    wanted, found, line, pos = sorted(set(offsets)), {}, 0, 1
    i = 0
    for m in SYMBOL.finditer(text):
        while i < len(wanted) and wanted[i] == pos:
            found[wanted[i]] = line
            i += 1
        if m.group() == "\n":
            line += 1
        pos += 1
    while i < len(wanted):
        found[wanted[i]] = line
        i += 1
    return found


def changed_lines(old, new):
    norm = lambda s: [MECHANICAL.sub("smt", l.rstrip()) for l in s.splitlines()]
    ops = difflib.SequenceMatcher(None, norm(old), norm(new), autojunk=False).get_opcodes()
    return {i for op, i1, i2, _, _ in ops if op != "equal" for i in range(i1, max(i2, i1 + 1))}


def method(text):
    m = re.match(r"(?:by|apply)\s*\(?\s*([a-z_]+)", text)
    return m.group(1) if m else "?"


def classify(rows, old_thys, new_thys):
    by_file = defaultdict(list)
    for r in rows:
        by_file[r["file"]].append(r)
    out = []
    for file, commands in by_file.items():
        rel = Path(file.split("/thys/", 1)[1]) if "/thys/" in file else None
        if rel is None or not (old_thys / rel).exists():
            continue
        old = (old_thys / rel).read_text(errors="replace")
        commands.sort(key=lambda r: int(r["offset"]))
        at = lines_at(old, [int(r["offset"]) for r in commands])
        new_file = new_thys / rel
        diff = changed_lines(old, new_file.read_text(errors="replace")) if new_file.exists() else None
        for k, r in enumerate(commands):
            if r["command"] not in STEPS:
                continue
            first = at[int(r["offset"])]
            last = at[int(commands[k + 1]["offset"])] - 1 if k + 1 < len(commands) else first
            span = range(first, max(last, first) + 1)
            status = "gone" if diff is None else ("changed" if any(i in diff for i in span) else "same")
            out.append({"file": str(rel), "offset": r["offset"], "seconds": float(r["seconds"]),
                        "method": method(r["text"]), "status": status})
    return out


def table(title, groups):
    print(f"\n{title}: steps, changed, gone")
    for name, steps in groups:
        kept = [s for s in steps if s["status"] != "gone"]
        if kept:
            changed = sum(s["status"] == "changed" for s in kept)
            print(f"  {name:>12}  {len(steps):>7}  {changed / len(kept):6.2%}  "
                  f"{sum(s['status'] == 'gone' for s in steps) / len(steps):6.2%}")


if __name__ == "__main__":
    args = sys.argv[1:]
    output = None
    if "-O" in args:
        i = args.index("-O")
        output, args = args[i + 1], args[:i] + args[i + 2:]
    census, old_thys, new_thys = args[0], Path(args[1]).expanduser(), Path(args[2]).expanduser()
    with open(census) as f:
        rows = list(csv.DictReader(f, delimiter="\t"))
    steps = classify(rows, old_thys, new_thys)
    table("by census time", [(f"{lo}-{hi} s", [s for s in steps if lo <= s["seconds"] < hi]) for lo, hi in BANDS])
    common = [m for m, _ in sorted(((m, sum(s["method"] == m for s in steps)) for m in {s["method"] for s in steps}),
                                   key=lambda x: -x[1])[:6]]
    for m in common:
        table(f"method {m}", [(f"{lo}-{hi} s", [s for s in steps if s["method"] == m and lo <= s["seconds"] < hi])
                              for lo, hi in BANDS])
    if output:
        with open(output, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(steps[0]), delimiter="\t")
            w.writeheader()
            w.writerows(steps)
