#!/usr/bin/env python3
"""Step-time histograms from the census and the re-timed steps, and census against re-timed time.

Usage: uv run --with matplotlib scripts/plot_steps.py [CENSUS] [RETIME] [OUT.png]
"""

import csv
import sys

import matplotlib.pyplot as plt
import numpy as np

STEPS = {"by", "apply"}
BLUE = "#2a78d6"
INK = "#0b0b0b"
MUTED = "#52514e"
GRID = "#e4e3df"
SLOW = 5.0


def step_times(path):
    with open(path) as f:
        return np.array([float(r["seconds"]) for r in csv.DictReader(f, delimiter="\t")
                         if r["command"] in STEPS and float(r["seconds"]) > 0])


def retimed(path):
    with open(path) as f:
        return np.array([float(r["median_ms"]) / 1000 for r in csv.DictReader(f, delimiter="\t")
                         if r["verdict"] == "closes"])


def style(ax, title):
    ax.set_xscale("log")
    ax.set_title(title, loc="left", color=INK, fontsize=11)
    ax.grid(axis="y", color=GRID, linewidth=0.8)
    ax.set_axisbelow(True)
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    for side in ("left", "bottom"):
        ax.spines[side].set_color(MUTED)
    ax.tick_params(colors=MUTED, labelsize=9)


def mark_slow(ax, text):
    ax.axvline(SLOW, color=MUTED, linestyle="--", linewidth=1)
    ax.text(0.99, 0.95, f"dashed line: 5 s\n{text}", transform=ax.transAxes, ha="right",
            va="top", color=MUTED, fontsize=9, bbox=dict(facecolor="white", edgecolor="none"))


def bars(ax, values, bins, weights=None):
    ax.hist(values, bins=bins, weights=weights, color=BLUE, edgecolor="white", linewidth=1)


def pairs(path):
    with open(path) as f:
        rows = [r for r in csv.DictReader(f, delimiter="\t") if r["verdict"] == "closes"]
    return (np.array([float(r["census_s"]) for r in rows]),
            np.array([float(r["median_ms"]) / 1000 for r in rows]))


def overstatement(retime, out):
    census, alone = pairs(retime)
    fig, ax = plt.subplots(figsize=(6, 6), constrained_layout=True)
    ax.scatter(census, alone, s=14, color=BLUE, alpha=0.7, linewidths=0)
    lo, hi = 0.005, 400
    ax.plot([lo, hi], [lo, hi], color=MUTED, linewidth=1)
    ax.axhline(SLOW, color=MUTED, linestyle="--", linewidth=1)
    ax.set_xlim(10, hi)
    ax.set_ylim(lo, hi)
    ax.set_yscale("log")
    ax.set_xlabel("census time, parallel build (s, log)", color=MUTED)
    ax.set_ylabel("time alone, median of 3 (s, log)", color=MUTED)
    ratio = np.median(census / alone)
    style(ax, f"Build logs overstate slow steps {ratio:.1f}x at the median")
    ax.text(0.98, 0.04, "solid: same time  dashed: 5 s", transform=ax.transAxes, ha="right",
            color=MUTED, fontsize=9)
    fig.savefig(out, dpi=150, facecolor="white")
    print(out)


def main():
    defaults = ["census/sample.tsv", "census/retime2.tsv", "census/steps.png"]
    census, retime, out = sys.argv[1:4] + defaults[len(sys.argv[1:4]):]
    times = step_times(census)
    slow = times >= SLOW
    bins = np.logspace(np.log10(times.min()), np.log10(times.max()), 50)

    fig, axes = plt.subplots(3, 1, figsize=(8, 10), constrained_layout=True)

    bars(axes[0], times, bins)
    axes[0].set_yscale("log")
    axes[0].set_ylabel("steps (log)", color=MUTED)
    style(axes[0], f"Census: {len(times):,} by/apply steps, wall time per step")
    mark_slow(axes[0], f"{slow.sum():,} steps ≥ 5 s")

    bars(axes[1], times, bins, weights=times / 3600)
    axes[1].set_ylabel("total hours", color=MUTED)
    style(axes[1], "Census: total time in each bin")
    mark_slow(axes[1], f"{times[slow].sum() / times.sum():.0%} of step time ≥ 5 s")

    again = retimed(retime)
    bars(axes[2], again, np.logspace(np.log10(again.min()), np.log10(again.max()), 30))
    axes[2].set_ylabel("steps", color=MUTED)
    axes[2].set_xlabel("seconds (log)", color=MUTED)
    style(axes[2], f"Re-timed serially: {len(again)} of the 200 slowest census steps (median of 3)")
    mark_slow(axes[2], f"{(again >= SLOW).sum()} still ≥ 5 s")

    fig.savefig(out, dpi=150, facecolor="white")
    print(out)
    overstatement(retime, out.replace(".png", "-overstatement.png"))


if __name__ == "__main__":
    main()
