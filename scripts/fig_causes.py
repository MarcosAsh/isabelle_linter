#!/usr/bin/env python3
"""Figures for RQ2: what makes slow `by` steps slow, and where faster edits help.

Usage: scripts/fig_causes.py
Reads census/notes/rq2_root_causes.tsv (from scripts/root_causes.py -O) and writes
fig_causes, fig_cause_hits and fig_profile_flatness to census/figures/.
"""

import sys
from collections import defaultdict
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
from figstyle import *  # noqa: E402,F403
from root_causes import read_tsv  # noqa: E402

STEPS = "census/notes/rq2_root_causes.tsv"
TOP, BAND = "top 200 (laptop)", "1-5 s band (PC)"

LABELS = {
    "transfer": "transfer", "simp": "simp", "inst_lift": "inst/lift", "proof_state": "proof state",
    "metis": "metis", "unify": "unify", "code_eval": "code eval", "sorts": "sorts",
    "classical": "classical", "match": "match", "term_index": "term index",
    "elaboration": "elaboration", "external_wait": "smt (solver wait)", "no_profile": "no profile",
}

# causes under this share of re-timed time in both corpora fold into "other"
FOLD = 0.02

# real rewriting or search vs per-rule overhead set by the context
WORK = ["simp", "metis", "unify"]
OVERHEAD = ["transfer", "inst_lift", "code_eval", "proof_state"]


def load():
    rows = read_tsv(STEPS)
    for r in rows:
        r["ms"] = float(r["ms"])
    return rows


def corpus(rows, name):
    return [r for r in rows if r["corpus"] == name]


def time_shares(steps):
    total = sum(r["ms"] for r in steps)
    shares = defaultdict(float)
    for r in steps:
        shares[r["cause"]] += r["ms"] / total
    return shares


def fold_small(top, band):
    kept = [c for c in set(top) | set(band) if max(top.get(c, 0), band.get(c, 0)) >= FOLD]
    kept.sort(key=lambda c: -top.get(c, 0))
    folded = lambda s: sum(v for c, v in s.items() if c not in kept)
    return kept + ["other"], {**top, "other": folded(top)}, {**band, "other": folded(band)}


def legend_label(name, steps):
    return f"{name} ({len(steps)} steps, {sum(r['ms'] for r in steps) / 1000:,.0f} s)"


def bar_labels(ax, bars, values):
    for bar, v in zip(bars, values):
        y = bar.get_y() + bar.get_height() / 2
        ax.text(bar.get_width() + 0.4, y, f"{100 * v:.0f}%" if v >= 0.005 else "<1%",
                va="center", ha="left", color=INK, fontsize=7.5)


def fig_causes(rows):
    top_steps, band_steps = corpus(rows, TOP), corpus(rows, BAND)
    causes, top, band = fold_small(time_shares(top_steps), time_shares(band_steps))
    y = np.arange(len(causes))
    h = 0.38
    fig, ax = plt.subplots(figsize=(4.8, 3.4))
    a = ax.barh(y - h / 2, [100 * top[c] for c in causes], h, color=BLUE,
                label=legend_label("top 200 slowest", top_steps))
    b = ax.barh(y + h / 2, [100 * band[c] for c in causes], h, color=ORANGE,
                label=legend_label("random 1-5 s band", band_steps))
    bar_labels(ax, a, [top[c] for c in causes])
    bar_labels(ax, b, [band[c] for c in causes])
    ax.set_yticks(y, [LABELS.get(c, c) for c in causes], color=INK)
    ax.invert_yaxis()
    ax.set_xlim(0, 37)
    ax.set_xlabel("share of re-timed time (%), by step's dominant cause")
    ax.legend(loc="lower right", fontsize=7.5)
    style(ax, grid="x")
    ax.tick_params(axis="y", length=0)
    save(fig, "fig_causes")


# Wilson score interval, 95%
def wilson(k, n, z=1.96):
    p = k / n
    centre = (p + z * z / (2 * n)) / (1 + z * z / n)
    half = z * np.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / (1 + z * z / n)
    return max(0, centre - half), min(1, centre + half)


def hit_counts(steps):
    counts = defaultdict(lambda: [0, 0])
    for r in steps:
        if r["edit"] != "not_searched":
            counts[r["cause"]][0] += r["edit"] == "faster_edit"
            counts[r["cause"]][1] += 1
    return counts


def pooled(counts, causes):
    return [sum(counts[c][0] for c in causes), sum(counts[c][1] for c in causes)]


# rows top to bottom: (label, k, n, colour, pooled?), None for a gap
def hit_rows(counts):
    rows = [(LABELS[c], *counts[c], BLUE, False) for c in WORK]
    rows.append(("rewriting/search, all", *pooled(counts, WORK), BLUE, True))
    rows.append(None)
    rows += [(LABELS[c], *counts[c], ORANGE, False) for c in OVERHEAD]
    rows.append(("context overhead, all", *pooled(counts, OVERHEAD), ORANGE, True))
    return rows


def draw_hit(ax, y, label, k, n, colour, total):
    lo, hi = wilson(k, n)
    ax.barh(y, 100 * k / n, 0.62, color=colour, alpha=1 if total else 0.55)
    ax.plot([100 * lo, 100 * hi], [y, y], color=INK, linewidth=0.9)
    ax.text(100 * hi + 1.5, y, f"{k}/{n}", va="center", ha="left", color=INK, fontsize=7.5,
            fontweight="bold" if total else "normal")


def fig_cause_hits(rows):
    steps = corpus(rows, TOP)
    counts = hit_counts(steps)
    layout = hit_rows(counts)
    fig, ax = plt.subplots(figsize=(4.8, 3.0))
    ticks, names = [], []
    for y, row in enumerate(layout):
        if row is None:
            continue
        label, k, n, colour, total = row
        draw_hit(ax, y, label, k, n, colour, total)
        ticks.append(y)
        names.append(label)
    ax.set_yticks(ticks, names, color=INK)
    for tick, row in zip(ax.get_yticklabels(), [r for r in layout if r]):
        tick.set_fontweight("bold" if row[4] else "normal")
    ax.invert_yaxis()
    ax.set_xlim(0, 100)
    ax.set_xlabel("searched steps with a verified 2x faster edit (%)")
    searched = sum(n for _, n in counts.values())
    rest = [c for c in counts if c not in WORK + OVERHEAD]
    k, n = pooled(counts, rest)
    note(ax, f"top 200, {searched} searched steps\nline: 95% Wilson interval\n"
             f"not shown: classical, no profile {k}/{n}", y=0.5)
    style(ax, grid="x")
    ax.tick_params(axis="y", length=0)
    save(fig, "fig_cause_hits")


def dominant_share(r):
    return float(r[r["cause"]]) if r["cause"] in r else None


# causes with a share column and enough steps, sorted by median share
def flat_causes(rows, min_steps=5):
    groups = defaultdict(list)
    for r in rows:
        s = dominant_share(r)
        if s is not None:
            groups[r["cause"]].append(s)
    kept = [c for c, v in groups.items() if len(v) >= min_steps]
    return sorted(kept, key=lambda c: np.median(groups[c]))


def strip(ax, y, values, colour, offset, rng):
    jitter = rng.uniform(-0.12, 0.12, len(values))
    ax.scatter(100 * np.array(values), y + offset + jitter, s=9, color=colour, alpha=0.7,
               linewidths=0)


def fig_profile_flatness(rows):
    causes = flat_causes(rows)
    rng = np.random.default_rng(0)
    fig, ax = plt.subplots(figsize=(4.8, 3.2))
    for name, colour, offset in [(TOP, BLUE, -0.17), (BAND, ORANGE, 0.17)]:
        steps = corpus(rows, name)
        for y, c in enumerate(causes):
            values = [dominant_share(r) for r in steps if r["cause"] == c]
            if values:
                strip(ax, y, values, colour, offset, rng)
    for y, c in enumerate(causes):
        m = 100 * np.median([dominant_share(r) for r in rows if r["cause"] == c])
        ax.plot([m, m], [y - 0.38, y + 0.38], color=INK, linewidth=1.4)
        n = sum(r["cause"] == c for r in rows)
        ax.text(101, y, f"n={n}", va="center", ha="left", color=MUTED, fontsize=7)
    ax.set_yticks(range(len(causes)), [LABELS[c] for c in causes], color=INK)
    ax.invert_yaxis()
    ax.set_xlim(0, 100)
    ax.set_xlabel("dominant cause's share of the step's profile samples (%)")
    ax.scatter([], [], s=12, color=BLUE, label="top 200")
    ax.scatter([], [], s=12, color=ORANGE, label="1-5 s band")
    ax.plot([], [], color=INK, linewidth=1.4, label="median, both")
    ax.legend(loc="upper right", fontsize=7.5, handletextpad=0.3)
    style(ax, grid="x")
    ax.tick_params(axis="y", length=0)
    save(fig, "fig_profile_flatness")


def main():
    rows = load()
    fig_causes(rows)
    fig_cause_hits(rows)
    fig_profile_flatness(rows)


if __name__ == "__main__":
    main()
