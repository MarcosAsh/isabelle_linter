#!/usr/bin/env python3
"""Histogram of proof step times from the census, and of the re-timed slow steps.

Usage: uv run --with matplotlib scripts/plot_steps.py [CENSUS] [RETIME] [OUT]
       (defaults: census/sample.tsv census/retime2.tsv census/steps.png)
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


if __name__ == "__main__":
    main()
