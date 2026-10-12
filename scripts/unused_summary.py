#!/usr/bin/env python3
"""Summarise an unused_pilot.py run: what the lint found, how the fixes change time, and
whether the fixed entries still build.

Usage: scripts/unused_summary.py [DIR]    (default: census/unused)
"""

import re
import sys
from collections import Counter
from pathlib import Path

PIECE = re.compile(r"^  (fact|assumption|`have|`apply)", re.M)
TIME = re.compile(r"^time: (\d+) ms as written, (\d+) ms with the fix", re.M)
CHECKED = re.compile(r"^(\d+) of (\d+) lemmas check", re.M)
FINDINGS = re.compile(r"^(\d+) findings$", re.M)


def kind(word):
    return word.strip("`")


def session(log):
    text = log.read_text()
    checked = CHECKED.search(text)
    found = FINDINGS.search(text)
    return {
        "lemmas": int(checked.group(1)) if checked else 0,
        "findings": int(found.group(1)) if found else None,
        "pieces": Counter(kind(k) for k in PIECE.findall(text)),
        "times": [(int(a), int(b)) for a, b in TIME.findall(text)],
    }


def built(log):
    text = log.read_text()
    return "Unfinished session" not in text and "FAILED" not in text


def main():
    out = Path(sys.argv[1] if len(sys.argv) > 1 else "census/unused")
    logs = out / "logs"
    sessions = {p.stem: session(p) for p in sorted(logs.glob("*.log"))}
    builds = {p.stem: built(p) for p in sorted(logs.glob("*.build"))}

    pieces = sum((s["pieces"] for s in sessions.values()), Counter())
    times = [t for s in sessions.values() for t in s["times"]]
    finished = [s for s in sessions.values() if s["findings"] is not None]
    print(f"sessions: {len(finished)} finished of {len(sessions)}")
    print(f"lemmas checked: {sum(s['lemmas'] for s in finished)}")
    print(f"lemmas with findings: {sum(s['findings'] for s in finished)}")
    print("pieces:", ", ".join(f"{k} {n}" for k, n in pieces.most_common()))
    if times:
        before, after = sum(a for a, _ in times), sum(b for _, b in times)
        slower = sum(b > 1.2 * a and b - a >= 10 for a, b in times)
        faster = sum(b < a / 1.2 and a - b >= 10 for a, b in times)
        print(f"fixed lemmas timed: {len(times)}; {before} ms -> {after} ms in total; "
              f"{faster} faster, {slower} slower (> 1.2x and >= 10 ms)")
    ok = sum(builds.values())
    print(f"entries rebuilt with all fixes: {ok} of {len(builds)}"
          + ("" if ok == len(builds) else "; failed: " + ", ".join(e for e, b in builds.items() if not b)))


if __name__ == "__main__":
    main()
