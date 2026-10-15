#!/usr/bin/env python3
"""Figures for RQ2 edits: faster_step winners, seconds saved per entry, and unused pieces.

Usage: scripts/fig_edits.py
Reads census/winners_21.tsv, the question logs in census/pc/faster_step/logs, census/pc/unused and
census/pc/dsp/unused; writes fig_winners, fig_savings and fig_unused to census/figures/.
"""

import csv
import glob
import statistics as st
import sys
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
from edit_summary import SPEEDUP, ms, read, summarise  # noqa: E402
from figstyle import *  # noqa: E402,F403
from lint_afp import SUFFIX  # noqa: E402
from unused_summary import summarise_run  # noqa: E402
from winners import entry_sessions  # noqa: E402

ROOT = Path(__file__).parent.parent
WINNERS = ROOT / "census/winners_21.tsv"
RUN = ROOT / "census/pc/faster_step"
UNUSED = ROOT / "census/pc/unused"
DSP = ROOT / "census/pc/dsp/unused"

KINDS = [("swap", "method swap", BLUE), ("simp_only", "simp only", ORANGE),
         ("other", "drop fact, per subgoal", AQUA)]
LIGHT_BLUE = "#a9c9ef"
LIGHT_GREY = "#c9c8c3"

# times under 1 ms are drawn on this floor
FLOOR = 0.6e-3

# first-timing bins (s) for the hit rate of searched steps
BINS = [3, 5, 10, 20, 50, np.inf]

SHORT = {"Modular_arithmetic_LLL_and_HNF_algorithms": "Modular_arith._LLL_HNF",
         "ResiduatedTransitionSystem2": "ResiduatedTransSys2",
         "Relational_Disjoint_Set_Forests": "Relational_Disj._Set_Forests",
         "Abstract_Consistency_Property": "Abstract_Consistency_Prop.",
         "Comparison_Sort_Lower_Bound": "Comparison_Sort_Lower_Bnd",
         "Interval_Arithmetic_Word32": "Interval_Arith._Word32",
         "Ordered_Resolution_Prover": "Ordered_Resolution_Prover",
         "Diophantine_Universal_Pairs": "Diophantine_Univ._Pairs"}


def short(name):
    return SHORT.get(name, name)


def read_winners():
    with open(WINNERS) as f:
        rows = list(csv.DictReader(f, delimiter="\t"))
    for r in rows:
        r["old_s"], r["new_s"] = int(r["original_ms"]) / 1000, int(r["new_ms"]) / 1000
        r["group"] = r["kind"] if r["kind"] in ("swap", "simp_only") else "other"
    return rows


# every searched step: its first (parallel) timing and whether an edit was confirmed 2x faster
def searched_steps():
    out = []
    for log in sorted((RUN / "logs").glob("*.tsv")):
        for questions in read(log).values():
            original, rest = questions[0], questions[1:]
            if not rest or original[4] != "closes":
                continue
            hit = any(q[1] == "linter_time" and q[4] == "closes" and ms(q, "ms2") * SPEEDUP < ms(q) for q in rest)
            out.append(dict(s=ms(original) / 1000, hit=hit, session=log.stem))
    return out


def time_axis(axis, which):
    ticks = [1e-3, 1e-2, 1e-1, 1, 10]
    labels = ["1 ms", "10 ms", "0.1 s", "1 s", "10 s"]
    getattr(axis, f"set_{which}scale")("log")
    getattr(axis, f"set_{which}ticks")(ticks, labels)
    getattr(axis, f"set_{which}ticks")([], minor=True)


# y = x / k guides, labelled at their right end
def guides(ax, lo, hi):
    xs = np.array([lo, hi])
    ax.plot(xs, xs, color=MUTED, linewidth=0.8)
    ax.text(lo * 1.1, lo * 3, "same time", color=MUTED, fontsize=7, ha="left", va="bottom")
    for k in (2, 10, 100, 1000):
        ax.plot(xs, xs / k, color=MUTED, linewidth=0.6, linestyle=(0, (3, 3)))
        ax.text(hi * 0.9, hi * 0.9 / k * 1.25, f"{k}x", color=MUTED, fontsize=7, ha="right", va="bottom",
                bbox=dict(facecolor="white", edgecolor="none", pad=0.3))


def plot_scatter(ax, rows):
    for key, label, color in KINDS:
        pts = [r for r in rows if r["group"] == key]
        ax.scatter([r["old_s"] for r in pts], [max(r["new_s"], FLOOR) for r in pts], s=20, color=color,
                   edgecolor="white", linewidth=0.5, alpha=0.9, label=f"{label} ({len(pts)})", zorder=3)
    lo, hi = 0.1, 40
    guides(ax, lo, hi)
    time_axis(ax, "x")
    time_axis(ax, "y")
    ax.set_yticks([FLOOR] + [1e-2, 1e-1, 1, 10], ["<1 ms", "10 ms", "0.1 s", "1 s", "10 s"])
    ax.set_xlim(lo, hi)
    ax.set_ylim(0.4e-3, hi)
    ax.set_xlabel("original step, alone (median of 3)")
    ax.set_ylabel("edited step, alone")
    label_notable(ax, rows)
    ax.legend(loc="upper left", fontsize=7.5, handletextpad=0.2, borderaxespad=0.2)
    style(ax, "a. 164 confirmed edits", grid="both")


# the largest single saving, labelled in the empty corner above it
def label_notable(ax, rows):
    r = max(rows, key=lambda r: r["old_s"] - r["new_s"])
    ax.annotate(f"{r['original'][3:]} → {r['new'][3:]}\n({r['entry']})", (r["old_s"], max(r["new_s"], FLOOR)),
                xytext=(0, 18), textcoords="offset points", ha="center", va="bottom", fontsize=7, color=INK,
                arrowprops=dict(arrowstyle="-", color=MUTED, linewidth=0.6, shrinkB=4))


def hit_rates(steps):
    rates = []
    for lo, hi in zip(BINS, BINS[1:]):
        inside = [s for s in steps if lo <= s["s"] < hi]
        rates.append((sum(s["hit"] for s in inside), len(inside)))
    return rates


def bin_labels():
    return [f"{lo}-{hi}" for lo, hi in zip(BINS, BINS[1:-1])] + [f"≥{BINS[-2]}"]


def plot_hits(ax, steps):
    others = [s for s in steps if not s["session"].startswith("MiniSail")]
    x = np.arange(len(BINS) - 1)
    width = 0.38
    for shift, group, color, label in ((-width / 2, steps, MUTED, "all 21 entries"),
                                       (width / 2, others, LIGHT_GREY, "without MiniSail")):
        rates = hit_rates(group)
        ax.bar(x + shift, [100 * h / n if n else 0 for h, n in rates], width - 0.04, color=color, label=label)
    rates = hit_rates(steps)
    ax.set_xticks(x, [f"{b} s\n{h}/{n}" for b, (h, n) in zip(bin_labels(), rates)], fontsize=7.5)
    overall = 100 * sum(s["hit"] for s in steps) / len(steps)
    ax.axhline(overall, color=INK, linewidth=0.7, linestyle=(0, (3, 3)))
    ax.text(len(x) - 0.5, overall + 1, f"overall {overall:.0f}%", color=INK, fontsize=7, ha="right", va="bottom")
    ax.set_ylabel("searched steps with a confirmed edit (%)")
    ax.set_xlabel("original step, first parallel timing\n(hits / searched, all entries)")
    ax.set_ylim(0, 45)
    ax.legend(loc="upper right", fontsize=7.5, bbox_to_anchor=(1, 0.93))
    style(ax, f"b. hit rate of the {len(steps)} searched steps")


def fig_winners():
    rows, steps = read_winners(), searched_steps()
    fig, (left, right) = plt.subplots(1, 2, figsize=(7, 3.3), gridspec_kw=dict(width_ratios=[1.15, 1]))
    plot_scatter(left, rows)
    plot_hits(right, steps)
    save(fig, "fig_winners")
    return rows, steps


# searched slow seconds per entry, from the question logs
def searched_seconds():
    owner = entry_sessions(RUN)
    out = defaultdict(float)
    for log in glob.glob(str(RUN / "logs/*.tsv")):
        entry = owner[Path(log).stem.removesuffix(SUFFIX)]
        out[entry] += summarise(read(log))["slow_ms"] / 1000
    return out


def savings(rows):
    out = defaultdict(lambda: [0.0, 0.0])
    for r in rows:
        out[r["entry"]][r["applied"] != "yes"] += r["old_s"] - r["new_s"]
    return sorted(out.items(), key=lambda kv: sum(kv[1]))


def plot_savings(ax, saved, searched):
    y = np.arange(len(saved))
    applied = [a for _, (a, _) in saved]
    confirmed = [c for _, (_, c) in saved]
    ax.barh(y, applied, 0.7, color=BLUE, label=f"applied and rebuilt ({sum(applied):.0f} s)")
    ax.barh(y, confirmed, 0.7, left=applied, color=LIGHT_BLUE, edgecolor="white", linewidth=0.8,
            label=f"confirmed only ({sum(confirmed):.0f} s)")
    ax.set_yticks(y, [short(e) for e, _ in saved], fontsize=7.5, color=INK)
    for i, (entry, parts) in enumerate(saved[:-1]):
        ax.text(sum(parts) + 4, i, f"{sum(parts):.1f} of {searched[entry]:.0f}", va="center", fontsize=7, color=INK)
    top, parts = saved[-1]
    ax.text(sum(parts) - 4, len(saved) - 1, f"{sum(parts):.1f} of {searched[top]:.0f} s searched",
            va="center", ha="right", fontsize=7, color=INK)
    ax.set_xlim(0, 360)
    ax.set_ylim(-0.6, len(saved) - 0.4)
    ax.set_xlabel("seconds saved, sum of single-edit savings")
    ax.legend(loc="lower right", fontsize=7.5, bbox_to_anchor=(1, 0.06))
    style(ax, grid="x")


def fig_savings(rows):
    saved, searched = savings(rows), searched_seconds()
    fig, ax = plt.subplots(figsize=(4.8, 3.6))
    plot_savings(ax, saved, searched)
    save(fig, "fig_savings")
    return saved, searched


def removed(r):
    p = r["pieces"]
    return p["fact"] + p["have"] + p["apply"]


def per100(r, what=None):
    count = removed(r) if what is None else r["pieces"][what]
    return 100 * count / r["steps"]


# AFP entries with steps; Relational_Disjoint_Set_Forests lost 65% of its questions
def unused_rows():
    afp = [r for r in summarise_run(UNUSED) if r["steps"]]
    dsp = summarise_run(DSP)[0]
    return afp, dsp


def plot_rates(ax, afp, dsp):
    lost = "Relational_Disjoint_Set_Forests"
    rows = sorted(afp + [dict(dsp, name="DSP")], key=per100)
    y = np.arange(len(rows))
    for i, r in enumerate(rows):
        if r["name"] == "DSP":
            ax.scatter(per100(r), i, marker="D", s=34, color=ORANGE, zorder=3)
        else:
            hollow = r["name"] == lost
            ax.scatter(per100(r), i, s=26, zorder=3, color="white" if hollow else BLUE, edgecolor=BLUE, linewidth=1)
    names = ["DSP (199 proofs)" if r["name"] == "DSP" else short(r["name"]) + (" *" if r["name"] == lost else "")
             for r in rows]
    ax.set_yticks(y, names, fontsize=7.5, color=INK)
    median = st.median(per100(r) for r in afp if r["name"] != lost)
    ax.axvline(median, color=MUTED, linewidth=0.8, linestyle=(0, (3, 3)))
    ax.text(median + 1, len(rows) - 1, f"AFP median entry {median:.1f}", color=MUTED, fontsize=7, va="center")
    ax.set_xlim(0, 68)
    ax.set_ylim(-0.7, len(rows) - 0.3)
    ax.set_xlabel("removable pieces per 100 steps")
    note(ax, "* lost 65% of its questions", y=0.03, x=0.99)
    ax.texts[-1].set_va("bottom")
    style(ax, "a. per entry", grid="x")


def pooled(rows):
    return dict(steps=sum(r["steps"] for r in rows), pieces=sum((r["pieces"] for r in rows), Counter()))


def plot_mix(ax, afp, dsp):
    whole = pooled(afp)
    parts = [("fact", "facts"), ("have", "haves"), ("apply", "applys")]
    y = np.arange(len(parts))
    height = 0.36
    afp_v = [per100(whole, p) for p, _ in parts]
    dsp_v = [per100(dsp, p) for p, _ in parts]
    ax.barh(y - height / 2, afp_v, height - 0.04, color=BLUE, label=f"AFP, {len(afp)} entries pooled")
    ax.barh(y + height / 2, dsp_v, height - 0.04, color=ORANGE, label="DSP, 199 proofs")
    ax.set_yticks(y, [name for _, name in parts], color=INK)
    ax.invert_yaxis()
    ratio = dsp_v[1] / afp_v[1]
    ax.text(dsp_v[1] + 0.6, 1 + height / 2, f"{dsp_v[1]:.1f} vs {afp_v[1]:.1f}: {ratio:.0f}x", va="center",
            fontsize=7, color=INK)
    ax.text(afp_v[0] + 0.6, -height / 2, f"{afp_v[0]:.1f}", va="center", fontsize=7, color=INK)
    ax.text(dsp_v[0] + 0.6, height / 2, f"{dsp_v[0]:.1f}", va="center", fontsize=7, color=INK)
    ax.text(0.6, 2 + height / 2, "none", va="center", fontsize=7, color=INK)
    ax.set_xlim(0, 32)
    ax.set_xlabel("removable pieces per 100 steps")
    ax.legend(loc="lower right", fontsize=7.5)
    style(ax, "b. what is removable", grid="x")


def fig_unused():
    afp, dsp = unused_rows()
    fig, (left, right) = plt.subplots(1, 2, figsize=(7, 3.8), gridspec_kw=dict(width_ratios=[1.25, 1]))
    plot_rates(left, afp, dsp)
    plot_mix(right, afp, dsp)
    save(fig, "fig_unused")
    return afp, dsp


def report(rows, steps, saved, afp, dsp):
    slow_confirm = sum(r["old_s"] < 3 for r in rows)
    print(f"winners {len(rows)}, hits {sum(s['hit'] for s in steps)}/{len(steps)} searched; "
          f"{slow_confirm} winners under 3 s when timed alone")
    faster = {k: sum(r["old_s"] >= k * r["new_s"] for r in rows) for k in (10, 100)}
    print(f">=10x {faster[10]}, >=100x {faster[100]}")
    print("saved:", {e: [round(a, 1), round(c, 1)] for e, (a, c) in saved})
    print(f"DSP {per100(dsp):.1f} per 100 steps, AFP pooled {per100(pooled(afp)):.1f}")


if __name__ == "__main__":
    rows, steps = fig_winners()
    saved, _ = fig_savings(rows)
    afp, dsp = fig_unused()
    report(rows, steps, saved, afp, dsp)
