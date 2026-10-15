#!/usr/bin/env python3
"""Summarise faster_step question logs (-o linter_log, or lint_afp.py's logs/SESSION.tsv).

Usage: scripts/edit_summary.py LOG.tsv...
Per log: steps checked, slow steps searched, hits (winners confirmed alone), time saved, search
time, and which kind of edit won. Times are wall-clock ms of the questions.

With -o faster_step_try0=true in the run, also the try0 baseline (try0's fastest proof, confirmed
the same way) and the oracle (per step, the better of faster_step's and try0's confirmed edit).
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


# the key ends with what was asked: a method, "time:METHOD", "try0" ...
def asked(row):
    return row[2].split(":", 3)[3]


def timings(rest):
    return {asked(q).removeprefix("time:"): q for q in rest if q[1] == "linter_time"}


# time saved by a confirmed edit, else None
def saving(t):
    if t is not None and t[4] == "closes" and ms(t, "ms2") * SPEEDUP < ms(t):
        return ms(t) - ms(t, "ms2")
    return None


# faster_step re-times its fastest closing edit; when that is try0's proof too, they share the row
def own_timing(rest, times, try0_method):
    others = [m for m in times if m != try0_method]
    if others:
        return others[0], times[others[0]]
    if try0_method in times and any(q[1] == "linter_try" and q[4] == "closes" for q in rest):
        return try0_method, times[try0_method]
    return None, None


def summarise(steps):
    out = {"steps": len(steps), "searched": 0, "hits": 0, "slow_ms": 0, "saved_ms": 0,
           "search_ms": [], "kinds": Counter(), "closing_kinds": Counter(),
           "try0_steps": 0, "try0_found": 0, "try0_hits": 0, "try0_saved_ms": 0, "try0_ms": [],
           "try0_methods": Counter(), "oracle_hits": 0, "oracle_saved_ms": 0, "overlap": Counter()}
    for questions in steps.values():
        original, rest = questions[0], questions[1:]
        if not rest or original[4] != "closes":
            continue
        out["searched"] += 1
        out["slow_ms"] += ms(original)
        out["search_ms"].append(sum(ms(q) for q in rest if q[1] not in ("linter_time", "linter_try0")))
        tries = [q for q in rest if q[1] == "linter_try" and q[4] == "closes"]
        if tries:
            fastest = min(tries, key=ms)
            out["closing_kinds"][kind(original[3], fastest[3])] += 1

        try0 = next((q for q in rest if q[1] == "linter_try0"), None)
        try0_method = props(try0).get("method") if try0 and try0[4] == "closes" else None
        times = timings(rest)
        method, own = own_timing(rest, times, try0_method)
        ours = saving(own)
        if ours is not None:
            out["hits"] += 1
            out["saved_ms"] += ours
            out["kinds"][kind(original[3], method)] += 1

        if try0 is not None:
            add_try0(out, try0, try0_method, times, ours)
    return out


# try0's confirmed proof, and the oracle: per step the better of the two savings
def add_try0(out, try0, method, times, ours):
    out["try0_steps"] += 1
    out["try0_ms"].append(ms(try0))
    theirs = saving(times.get(method)) if method else None
    if method:
        out["try0_found"] += 1
        out["try0_methods"][method] += 1
    if theirs is not None:
        out["try0_hits"] += 1
        out["try0_saved_ms"] += theirs

    savings = [x for x in (ours, theirs) if x is not None]
    if savings:
        out["oracle_hits"] += 1
        out["oracle_saved_ms"] += max(savings)
    names = {(True, True): "both", (True, False): "faster_step only", (False, True): "try0 only",
             (False, False): "neither"}
    out["overlap"][names[ours is not None, theirs is not None]] += 1


def show(name, s):
    searched = s["searched"] or 1
    print(f"{name}: {s['steps']} steps, {s['searched']} searched, {s['hits']} hits "
          f"({s['hits'] / searched:.0%}), saved {s['saved_ms'] / 1000:.1f} of {s['slow_ms'] / 1000:.1f} s")
    if s["search_ms"]:
        print(f"  search per step: median {st.median(s['search_ms']) / 1000:.1f} s, "
              f"total {sum(s['search_ms']) / 1000:.0f} s")
    print(f"  winners: {dict(s['kinds'])}  fastest closing edit: {dict(s['closing_kinds'])}")
    if s["try0_steps"]:
        show_try0(s)


def show_try0(s):
    n = s["try0_steps"]
    print(f"  try0 on {n} steps: found {s['try0_found']}, {s['try0_hits']} hits ({s['try0_hits'] / n:.0%}), "
          f"saved {s['try0_saved_ms'] / 1000:.1f} s; run median {st.median(s['try0_ms']) / 1000:.1f} s, "
          f"total {sum(s['try0_ms']) / 1000:.0f} s")
    print(f"  oracle (faster_step or try0): {s['oracle_hits']} hits ({s['oracle_hits'] / n:.0%}), "
          f"saved {s['oracle_saved_ms'] / 1000:.1f} s; {dict(s['overlap'])}")
    print(f"  try0 methods: {dict(s['try0_methods'])}")


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
