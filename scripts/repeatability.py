#!/usr/bin/env python3
"""Spread of each step's runs in a linter_retime output, and its medians against other runs.

Usage: scripts/repeatability.py RETIME [OTHER...]
"""

import csv
import statistics as st
import sys


def read(path):
    with open(path) as f:
        return {(r["file"], r["offset"]): r for r in csv.DictReader(f, delimiter="\t")
                if r["verdict"] == "closes"}


def quantiles(xs):
    xs = sorted(xs)
    q = lambda p: xs[round(p * (len(xs) - 1))]
    return f"median {q(.5):.3f}  p10 {q(.1):.3f}  p90 {q(.9):.3f}  max {xs[-1]:.3f}"


def cvs(rows):
    runs = [[int(x) for x in r.get("runs_ms", "").split(",") if x] for r in rows.values()]
    return [st.stdev(r) / st.mean(r) for r in runs if len(r) >= 2 and st.mean(r) > 0]


if __name__ == "__main__":
    base = read(sys.argv[1])
    spread = cvs(base)
    print(f"{sys.argv[1]}: {len(base)} steps closed")
    if spread:
        print("  stdev / mean of runs:", quantiles(spread))
        print(f"  steps within 5%: {sum(c <= .05 for c in spread) / len(spread):.0%}")
    for other in sys.argv[2:]:
        rows = read(other)
        ratios = [int(rows[k]["median_ms"]) / int(base[k]["median_ms"])
                  for k in base.keys() & rows.keys() if int(base[k]["median_ms"]) > 0]
        print(f"{other} / {sys.argv[1]}: {len(ratios)} steps in both")
        if ratios:
            print("  ratio of medians:", quantiles(ratios))
