#!/usr/bin/env python3
"""How repeatable are the re-timed step times?

Usage: scripts/repeatability.py RETIME [OTHER...]

For RETIME (a linter_retime output with runs_ms), prints the spread of each step's runs.
For each OTHER (another run over the same steps, e.g. on another machine or day), prints
how the medians of the steps both closed compare.
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


def spread(rows):
    """per step: (max - min) / median of its runs, and stdev / mean"""
    ranges, cvs = [], []
    for r in rows.values():
        runs = [int(x) for x in r.get("runs_ms", "").split(",") if x]
        if len(runs) >= 2 and st.median(runs) > 0:
            ranges.append((max(runs) - min(runs)) / st.median(runs))
            cvs.append(st.stdev(runs) / st.mean(runs))
    return ranges, cvs


def compare(a, b):
    """ratio of b's median to a's for the steps both closed"""
    both = a.keys() & b.keys()
    return [int(b[k]["median_ms"]) / int(a[k]["median_ms"]) for k in both
            if int(a[k]["median_ms"]) > 0]


def main():
    base = read(sys.argv[1])
    ranges, cvs = spread(base)
    print(f"{sys.argv[1]}: {len(base)} steps closed, {len(cvs)} with several runs")
    if cvs:
        print("  range / median:", quantiles(ranges))
        print("  stdev / mean:  ", quantiles(cvs))
        print(f"  steps within 5%: {sum(c <= .05 for c in cvs) / len(cvs):.0%}")
    for other in sys.argv[2:]:
        ratios = compare(base, read(other))
        print(f"{other} / {sys.argv[1]}: {len(ratios)} steps in both")
        if ratios:
            print("  ratio of medians:", quantiles(ratios))


if __name__ == "__main__":
    main()
