#!/usr/bin/env python3
"""Build a lookup table of rewrites that usually win, from linter_collect output.

Usage: scripts/peephole.py collect.jsonl... [-o table.json]
"""

import argparse
import json
import re
from collections import Counter, defaultdict

# a method within this factor of the fastest also counts as a winner
TOLERANCE = 1.3


def template(method):
    """The method with its facts replaced by F, so steps can be compared."""
    t = re.sub(r"\b(metis|meson|argo|smt(\s*\([^)]*\))?)\s+[^()]+", r"\1 F", method)
    t = re.sub(r"(\w+!?:)\s*[^():]+", r"\1 F ", t)
    t = re.sub(r"\((induction|induct|cases)\s+[^()]*\)", r"(\1 _)", t)
    return re.sub(r"\s+", " ", t).replace(" )", ")").strip()


def key(record):
    return template(record["method"]) + " | " + str(record["goal"].get("head", "?"))


def winners(record):
    times = {t["method"]: t["median_ms"] for t in record["tries"] if "median_ms" in t}
    if not times:
        return []
    best = min(times.values())
    return [m for m, t in times.items() if t <= max(best * TOLERANCE, best + 1)]


def build(records):
    seen = Counter()
    wins = defaultdict(Counter)
    for r in records:
        k = key(r)
        seen[k] += 1
        for m in winners(r):
            wins[k][template(m)] += 1

    return {k: [(m, w / seen[k]) for m, w in wins[k].most_common(3)] for k in seen}


def read(paths):
    for path in paths:
        with open(path) as f:
            yield from (json.loads(line) for line in f if line.strip())


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="+")
    parser.add_argument("-o", "--output")
    args = parser.parse_args()

    table = build(list(read(args.files)))
    for k, rewrites in sorted(table.items()):
        print(k)
        for m, rate in rewrites:
            print(f"    {rate:4.0%}  {m}")

    if args.output:
        with open(args.output, "w") as f:
            json.dump(table, f, indent=1)
