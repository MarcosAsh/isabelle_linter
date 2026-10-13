#!/usr/bin/env python3
"""Summarise faster_step question logs (-o linter_log, or lint_afp.py's logs/SESSION.tsv).

Usage: scripts/edit_summary.py LOG.tsv...
Per log: steps checked, slow steps searched, hits (winners confirmed alone), time saved, search
time, and which kind of edit won. Times are wall-clock ms of the questions.
"""

import csv
import re
import statistics as st
import sys
from collections import Counter, defaultdict

SPEEDUP = 2


def props(row):
    return dict(p.split("=", 1) for p in row[5:] if "=" in p)


def ms(row, name="ms"):
    return int(props(row).get(name, 0))


# theory:start:offset identifies a step; the rest of the key is the question
def step_of(key):
    return ":".join(key.split(":", 3)[:3])


# which candidate list of faster_step an edit comes from, from its text alone
def kind(original, edit):
    if re.search(r"\bsimp(_all)? only:", edit):
        return "simp_only"
    if edit.count(", ") > original.count(", "):
        return "per_subgoal"
    words = lambda s: set(re.findall(r"[^\s()\[\],]+", s))
    if len(edit) < len(original) and words(edit) <= words(original):
        return "drop_fact"
    return "swap"


def read(path):
    with open(path) as f:
        rows = [r for r in csv.reader(f, delimiter="\t") if len(r) >= 5 and r[0] == "faster_step"]
    steps = defaultdict(list)
    for r in rows:
        steps[step_of(r[2])].append(r)
    return steps


def summarise(steps):
    out = {"steps": len(steps), "searched": 0, "hits": 0, "slow_ms": 0, "saved_ms": 0,
           "search_ms": [], "kinds": Counter(), "closing_kinds": Counter()}
    for questions in steps.values():
        original, rest = questions[0], questions[1:]
        if not rest or original[4] != "closes":
            continue
        out["searched"] += 1
        out["slow_ms"] += ms(original)
        out["search_ms"].append(sum(ms(q) for q in rest if q[1] != "linter_time"))
        tries = [q for q in rest if q[1] == "linter_try" and q[4] == "closes"]
        if tries:
            fastest = min(tries, key=ms)
            out["closing_kinds"][kind(original[3], fastest[3])] += 1
        for t in (q for q in rest if q[1] == "linter_time" and q[4] == "closes"):
            if ms(t, "ms2") * SPEEDUP < ms(t):
                out["hits"] += 1
                out["saved_ms"] += ms(t) - ms(t, "ms2")
                out["kinds"][kind(original[3], t[3].split(" | ")[2])] += 1
    return out


def show(name, s):
    searched = s["searched"] or 1
    print(f"{name}: {s['steps']} steps, {s['searched']} searched, {s['hits']} hits "
          f"({s['hits'] / searched:.0%}), saved {s['saved_ms'] / 1000:.1f} of {s['slow_ms'] / 1000:.1f} s")
    if s["search_ms"]:
        print(f"  search per step: median {st.median(s['search_ms']) / 1000:.1f} s, "
              f"total {sum(s['search_ms']) / 1000:.0f} s")
    print(f"  winners: {dict(s['kinds'])}  fastest closing edit: {dict(s['closing_kinds'])}")


if __name__ == "__main__":
    total = None
    for path in sys.argv[1:]:
        s = summarise(read(path))
        show(path, s)
        if total is None:
            total = s
        else:
            for k, v in s.items():
                total[k] = total[k] + v
    if len(sys.argv) > 2:
        show("total", total)
