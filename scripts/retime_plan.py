#!/usr/bin/env python3
"""Plan the full-AFP re-time on the timing PC: steps per band, estimated hours, and the input file.

Usage: scripts/retime_plan.py [-b HOURS] [-r RUNS] [-s SEED] [CENSUS] [OUT]
Defaults: 30 h budget, 1 run per step (retime_runs=1, no -P; -r 4 is retime_runs=3 with -P), seed 1,
census/pc/timings_afp.tsv, census/retime_full.tsv
Takes the `by` steps of 5 s or more session by session, most slow time per PC hour first, while the
plan fits the budget; the 1-5 s and 0.5-1 s bands are sampled at random, in two strata each: steps
in sessions already loaded for the slow steps (cheap) and steps elsewhere. OUT is a census TSV for
linter_retime -I OUT -n <rows> -o retime_runs=1; OUT with _strata before .tsv gives each row's band, stratum
and weight (stratum size over sample size), for estimates over the whole band.
"""

import csv
import random
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

from census_stats import afp_only, read_rows

BANDS = [("5 s and more", 5, float("inf")), ("1-5 s", 1, 5), ("0.5-1 s", 0.5, 1)]
BUILD_LOG = "census/pc/build.log"
BAND_RUN = "census/pc/retime_band.tsv"
BAND_RUN_MINUTES = 205  # 15 Oct 03:29 (pc_queue.log) to 06:54, when the next session hung
SLOW_RUN = "census/retime2.tsv"
SESSION_FIXED_S = 60  # JVM, heap and PIDE session start
BOOST_OFF = 1.32  # boost on was 1.32x faster (repeat_boost against repeat1)
FAIL_ALLOWANCE = 0.02  # share of steps that time out: 3 runs of max(10 s, 3x census)
IN_SAMPLE = 500  # per lower band, steps in sessions the >= 5 s steps load anyway
OUT_SAMPLE = 50  # per lower band, steps elsewhere: each one loads a session of its own


def timed_out_sessions(log_path):
    """Sessions that failed while checking (not only in the LaTeX document): their load may not end."""
    lines = Path(log_path).read_text(errors="replace").split("\n")
    failed = set()
    for i, line in enumerate(lines):
        m = re.match(r"(\S+) FAILED \(see", line)
        if m and any("*** Timeout" in l for l in lines[max(0, i - 3):i + 4]):
            failed.add(m[1])
    return failed


def session_loads(rows):
    """Serial time each session checks: every file it holds at least one row of."""
    file_time = Counter()
    sessions = defaultdict(set)
    for r in rows:
        file_time[r["file"]] += r["seconds"]
        sessions[r["file"]].add(r["session"])
    load = Counter()
    for file, names in sessions.items():
        for name in names:
            load[name] += file_time[file]
    return load, file_time


def read_retime(path):
    with open(path) as f:
        return list(csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE))


def alone_ratio(path, census, lo, hi):
    """Mean of re-timed over this census's time, for closing steps it puts in [lo, hi). Both runs
    were boost on: retime2 on the laptop, which runs at the PC's boost-on speed."""
    ratios = []
    for r in read_retime(path):
        seconds = census.get((r["file"], r["offset"]))
        if r["verdict"] == "closes" and seconds and lo <= seconds < hi:
            ratios.append(int(r["median_ms"]) / 1000 / seconds)
    return sum(ratios) / len(ratios), len(ratios)


def calibrate(load, file_time):
    """Seconds of PC wall time per second of serial census time loaded, from the band run."""
    rows = read_retime(BAND_RUN)
    steps = sum(sum(int(x) for x in r["runs_ms"].split(",")) / 1000 + int(r["median_ms"]) / 1000
                for r in rows if r["verdict"] == "closes")
    sessions = {r["session"] for r in rows}
    loaded = sum(load[s] for s in sessions) + sum(file_time[f] for f in {r["file"] for r in rows})
    return (BAND_RUN_MINUTES * 60 - steps - SESSION_FIXED_S * len(sessions)) / loaded


class Model:
    def __init__(self, load, file_time, ratios, per_loaded, runs):
        self.load, self.file_time, self.ratios, self.per_loaded = load, file_time, ratios, per_loaded
        self.runs = runs

    def step(self, row, band):
        alone = row["seconds"] * self.ratios[band]
        fail = FAIL_ALLOWANCE * 3 * max(10, 3 * row["seconds"])
        return self.runs * alone + fail

    def hours(self, chosen):
        """Boost-off PC hours to re-time chosen [(row, band)]: sessions, theories touched, steps."""
        sessions = {r["session"] for r, _ in chosen}
        files = {r["file"] for r, _ in chosen}
        loaded = sum(self.load[s] for s in sessions) + sum(self.file_time[f] for f in files)
        wall = SESSION_FIXED_S * len(sessions) + self.per_loaded * loaded
        wall += sum(self.step(r, band) for r, band in chosen)
        return BOOST_OFF * wall / 3600


def band_rows(rows, lo, hi, excluded):
    return [r for r in rows if r["command"] == "by" and lo <= r["seconds"] < hi
            and r["session"] not in excluded]


def by_value(model, slow):
    """Sessions holding >= 5 s steps, most census slow time per PC hour first."""
    steps = defaultdict(list)
    for r in slow:
        steps[r["session"]].append(r)
    value = lambda s: sum(r["seconds"] for r in steps[s]) / model.hours([(r, 0) for r in steps[s]])
    return [steps[s] for s in sorted(steps, key=lambda s: -value(s))]


def lower_samples(bands, loaded, rng_order):
    """Per lower band: IN_SAMPLE random steps in loaded sessions, OUT_SAMPLE elsewhere, with weights."""
    chosen = []
    for band in (1, 2):
        for stratum, n in (("in", IN_SAMPLE), ("out", OUT_SAMPLE)):
            pool = [r for r in rng_order[band] if (r["session"] in loaded) == (stratum == "in")]
            chosen += [(r, band, stratum, len(pool) / min(n, len(pool))) for r in pool[:n]]
    return chosen


def plan(model, groups, bands, rng_order, k):
    slow = [(r, 0, "all", 1.0) for g in groups[:k] for r in g]
    loaded = {g[0]["session"] for g in groups[:k]}
    return slow + lower_samples(bands, loaded, rng_order)


def fit(model, groups, bands, rng_order, budget):
    """The most >= 5 s sessions, in value order, whose plan stays within budget."""
    lo, hi = 0, len(groups)
    while lo < hi:
        k = (lo + hi + 1) // 2
        if model.hours([c[:2] for c in plan(model, groups, bands, rng_order, k)]) <= budget:
            lo = k
        else:
            hi = k - 1
    return lo


def write_tsv(path, rows):
    cols = ["session", "file", "offset", "command", "seconds", "text"]
    with open(path, "w") as f:
        f.write("\t".join(cols) + "\n")
        for r in sorted(rows, key=lambda r: (r["session"], r["file"], int(r["offset"]))):
            f.write("\t".join(str(r[c]) for c in cols) + "\n")


def write_strata(path, chosen):
    with open(path, "w") as f:
        f.write("session\tfile\toffset\tband\tstratum\tweight\n")
        for r, band, stratum, weight in chosen:
            f.write(f"{r['session']}\t{r['file']}\t{r['offset']}\t{BANDS[band][0]}\t{stratum}\t{weight:.2f}\n")


def describe(model, label, chosen, total_steps):
    sessions = {r["session"] for r, _ in chosen}
    print(f"  {label:<26} {len(chosen):>6,} of {total_steps:>6,} steps, {len(sessions):>4} sessions, "
          f"{model.hours(chosen):6.1f} h")


def main():
    args = sys.argv[1:]
    opts = {"-b": 30.0, "-r": 1, "-s": 1}
    while args[:1] and args[0] in opts:
        opts[args[0]] = type(opts[args[0]])(args[1])
        args = args[2:]
    budget, runs, seed = opts["-b"], opts["-r"], opts["-s"]
    census, out = args + ["census/pc/timings_afp.tsv", "census/retime_full.tsv"][len(args):]

    rows = afp_only(read_rows(census))
    excluded = timed_out_sessions(BUILD_LOG)
    load, file_time = session_loads(rows)

    census_times = {(r["file"], r["offset"]): r["seconds"] for r in rows}
    slow_ratio, n_slow = alone_ratio(SLOW_RUN, census_times, 5, float("inf"))
    band_ratio, n_band = alone_ratio(BAND_RUN, census_times, 0.1, 5)
    per_loaded = calibrate(load, file_time)
    model = Model(load, file_time, [slow_ratio, band_ratio, band_ratio], per_loaded, runs)
    print(f"excluded (timed out in the build): {', '.join(sorted(excluded))}")
    print(f"alone/census (boost on): {slow_ratio:.3f} for >= 5 s ({n_slow} steps), {band_ratio:.3f} "
          f"below 5 s ({n_band} steps); {runs} runs per step; PC wall per serial second loaded "
          f"{per_loaded:.3f} + {SESSION_FIXED_S} s per session; x{BOOST_OFF} for boost off")

    bands = [band_rows(rows, lo, hi, excluded) for _, lo, hi in BANDS]
    print("\nevery step, per band (boost-off PC hours if re-timed alone):")
    for (label, _, _), (i, chosen) in zip(BANDS, enumerate(bands)):
        describe(model, label, [(r, i) for r in chosen], len(chosen))
    describe(model, "all three bands", [(r, i) for i, b in enumerate(bands) for r in b], sum(map(len, bands)))

    rng = random.Random(seed)
    rng_order = [None] + [rng.sample(b, len(b)) for b in bands[1:]]
    groups = by_value(model, bands[0])
    k = fit(model, groups, bands, rng_order, budget)
    chosen = plan(model, groups, bands, rng_order, k)
    loaded = {g[0]["session"] for g in groups[:k]}
    slow_time = sum(r["seconds"] for r in bands[0])
    taken = sum(r["seconds"] for r, band, _, _ in chosen if band == 0)
    print(f"\nplan within {budget:.0f} h (seed {seed}): >= 5 s steps of {k} of {len(groups)} sessions, "
          f"{taken / slow_time:.1%} of their census time")
    so_far = []
    for band, stratum in ((0, "all"), (1, "in"), (2, "in"), (1, "out"), (2, "out")):
        part = [c for c in chosen if c[1] == band and c[2] == stratum]
        pool = sum(1 for r in bands[band] if stratum == "all" or (stratum == "in") == (r["session"] in loaded))
        before = model.hours([c[:2] for c in so_far])
        so_far += part
        print(f"  {BANDS[band][0] + ' ' + stratum:<16} {len(part):>5,} of {pool:>6,} steps, "
              f"{len({c[0]['session'] for c in part}):>3} sessions, +{model.hours([c[:2] for c in so_far]) - before:5.1f} h")
    describe(model, "plan", [c[:2] for c in chosen], sum(map(len, bands)))

    write_tsv(out, [c[0] for c in chosen])
    write_strata(out.replace(".tsv", "_strata.tsv"), chosen)
    print(f"\nwrote {out}: {len(chosen):,} rows; run with -n {len(chosen)}")


if __name__ == "__main__":
    main()
