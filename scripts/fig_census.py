#!/usr/bin/env python3
"""Paper figures for RQ1 (census) and the repeatability appendix.

Usage: uv run --with matplotlib --with numpy python3 scripts/fig_census.py
Writes census/figures/fig_{overstatement,methods,entries,repeat}.{pdf,png}.
"""

import csv
from collections import Counter

import numpy as np
from matplotlib.colors import to_rgb

from census_stats import afp_only, at_least, method_group, of_command, quantile, read_rows, total
from figstyle import *  # noqa: F403
from repeatability import cvs

CENSUS = "census/pc/timings_afp.tsv"
SLOW = 5
TOP_METHODS = 8
OUTLIER = "Correctness_Algebras"


def tint(color, amount=0.55):
    return tuple(c + (1 - c) * amount for c in to_rgb(color))


def read_retime(path):
    with open(path) as f:
        return {(r["file"], r["offset"]): r for r in csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE)
                if r["verdict"] == "closes"}


def alone_s(row):
    return int(row["median_ms"]) / 1000


def log_axes(ax, lo, hi):
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlim(lo, hi)
    ax.set_ylim(lo, hi)
    ax.set_aspect("equal")


def guide(ax, factor, label, lo, hi, at, above=True, style="-"):
    xs = np.array([lo, hi])
    ax.plot(xs, factor * xs, color=MUTED, linewidth=0.8, linestyle=style, zorder=1)
    ax.annotate(label, (at, factor * at), xytext=(-3, 3) if above else (3, -3), textcoords="offset points",
                ha="right" if above else "left", va="bottom" if above else "top", color=MUTED, fontsize=8,
                rotation=45, rotation_mode="anchor")


def dots(ax, x, y, color, label):
    ax.scatter(x, y, s=14, color=color, alpha=0.75, edgecolor="white", linewidth=0.4, label=label, zorder=3)


# PC boost-on re-times: the slow steps (repeat_boost) and the random 1-5 s band (retime_band)
def overstatement_pairs(pc):
    retimes = {**read_retime("census/repeat_boost.tsv"), **read_retime("census/pc/retime_band.tsv")}
    keys = [k for k in retimes if k in pc]
    alone = np.array([alone_s(retimes[k]) for k in keys])
    quiet = np.array([pc[k] for k in keys])
    laptop = np.array([float(retimes[k]["census_s"]) for k in keys])
    return alone, quiet, laptop


def fig_overstatement(rows):
    pc = {(r["file"], r["offset"]): r["seconds"] for r in rows}
    alone, quiet, laptop = overstatement_pairs(pc)
    lo, hi = 3e-3, 1e3
    fig, ax = plt.subplots(figsize=(4.8, 4.2))

    dots(ax, alone, laptop, ORANGE, "loaded laptop census")
    dots(ax, alone, quiet, BLUE, "quiet PC census")
    guide(ax, 1, "y = x", lo, hi, at=0.02, above=False)
    guide(ax, 2, "2x", lo, hi, at=0.02, style=":")

    q, l = np.median(quiet / alone), np.median(laptop / alone)
    note(ax, f"median build-log / alone\nquiet PC {q:.1f}x, laptop {l:.1f}x\nn = {len(alone)} steps",
         x=0.03, y=0.97, ha="left")
    log_axes(ax, lo, hi)
    ax.set_xlabel("time alone, re-timed on the PC (s)")
    ax.set_ylabel("build-log (census) time (s)")
    handles, labels = ax.get_legend_handles_labels()
    ax.legend(handles[::-1], labels[::-1], loc="lower right", fontsize=8, handletextpad=0.2)
    style(ax, grid="both")
    save(fig, "fig_overstatement")
    print(f"  overstatement n {len(alone)}: quiet {q:.2f}x (p90 {quantile(quiet / alone, .9):.1f}), "
          f"laptop {l:.2f}x (p90 {quantile(laptop / alone, .9):.1f})")


def method_shares(slow):
    time, outlier = Counter(), Counter()
    for r in slow:
        name = method_group(r)
        time[name] += r["seconds"]
        if r["entry"] == OUTLIER:
            outlier[name] += r["seconds"]
    whole = total(slow)
    top = time.most_common(TOP_METHODS)
    other = whole - sum(t for _, t in top)
    shares = [(n, t / whole, outlier[n] / whole) for n, t in top] + [("other", other / whole, 0)]
    return shares


def fig_methods(rows):
    slow = at_least(of_command(rows, {"by"}), SLOW)
    shares = method_shares(slow)
    names = [n for n, _, _ in shares][::-1]
    share = np.array([s for _, s, _ in shares][::-1]) * 100
    outlier = np.array([o for _, _, o in shares][::-1]) * 100
    y = np.arange(len(names))
    fig, ax = plt.subplots(figsize=(4.8, 3.1))

    ax.barh(y, share - outlier, color=BLUE, height=0.7)
    ax.barh(y, outlier, left=share - outlier, color=tint(BLUE), height=0.7, edgecolor="white", linewidth=1)
    for yi, s in zip(y, share):
        ax.text(s + 0.4, yi, f"{s:.1f}%", va="center", color=INK, fontsize=8)

    i = int(np.argmax(outlier))
    rest = share[i] - outlier[i]
    ax.text(rest + outlier[i] / 2, y[i], OUTLIER, ha="center", va="center", color=INK, fontsize=7)
    ax.set_yticks(y, names)
    ax.tick_params(axis="y", length=0)
    ax.set_xlim(0, share.max() * 1.15)
    ax.set_xlabel(f"share of time in by steps ≥ {SLOW} s (%)")
    style(ax, grid="x")
    note(ax, f"{len(slow):,} steps, {total(slow) / 3600:.1f} h\n{names[i]} without {OUTLIER}: {rest:.1f}%",
         y=0.3)
    save(fig, "fig_methods")
    print(f"  methods: {names[i]} {share[i]:.1f}%, of which {OUTLIER} {outlier[i]:.1f}%")


def cumulative_by_entry(rows):
    by_entry = Counter()
    for r in rows:
        by_entry[r["entry"]] += r["seconds"]
    ranked = np.array(sorted(by_entry.values(), reverse=True))
    share = np.cumsum(ranked) / ranked.sum()
    half = int(np.searchsorted(share, 0.5)) + 1
    return np.arange(1, len(share) + 1), share * 100, half


def fig_entries(rows):
    slow = at_least(of_command(rows, {"by"}), SLOW)
    fig, ax = plt.subplots(figsize=(4.8, 3.1))
    ax.axhline(50, color=MUTED, linewidth=0.8, linestyle=":")

    series = [(slow, BLUE, f"by steps ≥ {SLOW} s"), (rows, ORANGE, "all checking time")]
    for chosen, color, label in series:
        x, share, half = cumulative_by_entry(chosen)
        ax.plot(x, share, color=color, linewidth=2, label=f"{label} ({len(x):,} entries)")
        ax.plot(half, share[half - 1], "o", color=color, markersize=6, markeredgecolor="white", zorder=4)
        ax.annotate(f"{half} entries", (half, share[half - 1]), xytext=(6, -12), textcoords="offset points",
                    color=INK, fontsize=8)
        print(f"  entries: {label}: {half} of {len(x)} hold half")

    ax.set_xscale("log")
    ax.set_xlim(1, 1100)
    ax.set_xticks([1, 10, 100, 1000], ["1", "10", "100", "1,000"])
    ax.set_ylim(0, 100)
    ax.set_xlabel("entries, largest first (log)")
    ax.set_ylabel("cumulative share of time (%)")
    ax.legend(loc="lower right", fontsize=8)
    style(ax, grid="both")
    save(fig, "fig_entries")


def ecdf(ax, values, color, label):
    xs = np.sort(np.array(values) * 100)
    ax.step(xs, np.arange(1, len(xs) + 1) / len(xs) * 100, where="post", color=color, linewidth=2,
            label=f"{label}\nn = {len(xs)}, median {np.median(xs):.1f}%")


def fig_repeat():
    off, on = read_retime("census/repeat1.tsv"), read_retime("census/repeat_boost.tsv")
    laptop = read_retime("census/retime2.tsv")
    fig, (left, right) = plt.subplots(1, 2, figsize=(7, 3.3))

    ecdf(left, cvs(off), BLUE, "boost off")
    ecdf(left, cvs(on), ORANGE, "boost on")
    left.axvline(5, color=MUTED, linewidth=0.8, linestyle=":")
    left.set_xscale("log")
    left.set_xlim(0.01, 60)
    left.set_ylim(0, 100)
    left.set_xlabel("run-to-run stdev / mean (%, log)")
    left.set_ylabel("steps at or below (%)")
    left.text(5.4, 3, "5%", color=MUTED, fontsize=8)
    left.legend(loc="upper left", fontsize=7.5, handlelength=1.2, labelspacing=0.8)
    style(left, "Spread of 5 runs on the PC", grid="both")

    keys = [k for k in off.keys() & laptop.keys() if alone_s(off[k]) > 0]
    pc = np.array([alone_s(off[k]) for k in keys])
    lap = np.array([alone_s(laptop[k]) for k in keys])
    ratio = np.median(lap / pc)
    lo, hi = 3e-3, 300
    dots(right, pc, lap, BLUE, None)
    guide(right, 1, "y = x", lo, hi, at=0.03)
    guide(right, ratio, f"{ratio:.2f}x (median)", lo, hi, at=0.03, above=False, style="--")
    log_axes(right, lo, hi)
    right.set_xlabel("PC, boost off (s)")
    right.set_ylabel("laptop, boost on (s)")
    style(right, f"Same steps, two machines (n = {len(keys)})", grid="both")
    save(fig, "fig_repeat")
    print(f"  repeat: laptop / PC median {ratio:.3f}, n {len(keys)}")


def main():
    rows = afp_only(read_rows(CENSUS))
    fig_overstatement(rows)
    fig_methods(rows)
    fig_entries(rows)
    fig_repeat()


if __name__ == "__main__":
    main()
