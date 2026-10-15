#!/usr/bin/env python3
"""RQ1 headline numbers from a linter_census TSV: where AFP checking time goes.

Usage: uv run --with matplotlib scripts/census_stats.py [CENSUS] [SAMPLE] [FIGURE.png]
Defaults: census/pc/timings_afp.tsv, census/sample.tsv, census/figures/steps_afp.png
Only commands in files under the AFP thys directory count; each row goes to the entry that owns
its file. The census already keeps each (file, offset) once, with its lowest time.
"""

import csv
import re
import sys
from collections import Counter
from pathlib import Path

STEPS = {"by", "apply"}
THRESHOLDS = [0.5, 1, 5, 10]
METHOD_GROUPS = {"simp_all": "simp", "induct": "induction", "induct_tac": "induction",
                 "fastforce": "fastforce", "force": "force", "auto": "auto", "metis": "metis",
                 "smt": "smt", "blast": "blast", "cases": "cases", "induction": "induction"}
SAMPLE_PUBLISHED = "25% of time in 1,293 `by` steps >= 5 s; 43% in steps >= 1 s"
RETIMES = [("census/retime2.tsv", "laptop, boost on, top 200 of the sample"),
           ("census/repeat1.tsv", "PC, boost off, same steps"),
           ("census/pc/retime_band.tsv", "PC, boost on, random 1-5 s of the sample")]


def read_rows(path):
    with open(path) as f:
        rows = list(csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE))
    for r in rows:
        r["seconds"] = float(r["seconds"])
    return rows


def entry_of(file):
    parts = file.split("/thys/", 1)
    return parts[1].split("/", 1)[0] if len(parts) == 2 else None


def afp_only(rows):
    kept = [r for r in rows if entry_of(r["file"])]
    for r in kept:
        r["entry"] = entry_of(r["file"])
    return kept


def first_method(text):
    """The first proof method of a `by`/`apply` command: `by (cases x; auto)` gives cases."""
    body = re.sub(r"\(\*.*?\*\)|\\<comment>\s*\\<open>.*?\\<close>", " ", text)
    body = re.sub(r"^\s*(by|apply)\b", "", body).lstrip(" (")
    if body.startswith("-"):
        return "-"
    m = re.match(r"[A-Za-z_][\w.']*", body)
    return m.group(0) if m else "?"


def source_text(file, offset, length=300):
    """The command text from the theory source; offset counts Isabelle symbols from 1."""
    path = Path(file).expanduser()
    if not path.is_file():
        return ""
    symbols = re.findall(r"\\<[^>]*>|.", path.read_text(errors="replace"), re.S)
    return " ".join("".join(symbols[offset - 1:offset - 1 + length]).split())


def method_group(row):
    name = first_method(row["text"])
    if name == "?":  # the method is on the next line, which the census does not keep
        name = first_method(source_text(row["file"], int(row["offset"])))
    return METHOD_GROUPS.get(name, name)


def pct(part, whole):
    return f"{100 * part / whole:.1f}%" if whole else "-"


def total(rows):
    return sum(r["seconds"] for r in rows)


def of_command(rows, commands):
    return [r for r in rows if r["command"] in commands]


def at_least(rows, seconds):
    return [r for r in rows if r["seconds"] >= seconds]


def overview(rows):
    all_time = total(rows)
    steps = of_command(rows, STEPS)
    by = of_command(rows, {"by"})
    print(f"entries {len({r['entry'] for r in rows})}, sessions {len({r['session'] for r in rows})}, "
          f"commands {len(rows):,}")
    print(f"serial checking time {all_time:,.0f} s = {all_time / 3600:.1f} h (sum of distinct command times)")
    print(f"by/apply steps {len(steps):,}: {pct(total(steps), all_time)} of time "
          f"(by {pct(total(by), all_time)}, apply {pct(total(steps) - total(by), all_time)})")


def thresholds(rows, commands, label):
    all_time = total(rows)
    chosen = of_command(rows, commands)
    print(f"\n{label} steps at or above a census time:")
    for t in THRESHOLDS:
        slow = at_least(chosen, t)
        print(f"  >= {t:>4} s: {len(slow):>7,} steps, {total(slow):>9,.0f} s = {pct(total(slow), all_time)} of time")


def concentration(rows):
    all_time = total(rows)
    ranked = sorted(rows, key=lambda r: -r["seconds"])
    by = sorted(of_command(rows, {"by"}), key=lambda r: -r["seconds"])
    print("\nconcentration:")
    for k in (100, 1000, 10000):
        print(f"  top {k:>6,} commands {pct(total(ranked[:k]), all_time)}, top {k:,} `by` steps "
              f"{pct(total(by[:k]), all_time)}")


def method_mix(rows, seconds):
    slow = at_least(of_command(rows, {"by"}), seconds)
    time = Counter()
    count = Counter()
    for r in slow:
        name = method_group(r)
        time[name] += r["seconds"]
        count[name] += 1
    print(f"\nfirst method of `by` steps >= {seconds} s ({len(slow):,} steps, {total(slow):,.0f} s):")
    for name, t in time.most_common(14):
        print(f"  {name:<16} {count[name]:>6,} steps  {pct(t, total(slow)):>6} of their time")
    return time, count


def entries_holding_half(rows):
    by_entry = Counter()
    for r in rows:
        by_entry[r["entry"]] += r["seconds"]
    ranked = by_entry.most_common()
    running = 0
    for k, (_, t) in enumerate(ranked, 1):
        running += t
        if running >= total(rows) / 2:
            return k, len(ranked), ranked[:8]
    return 0, len(ranked), ranked[:8]


def by_entry(rows):
    slow = at_least(of_command(rows, {"by"}), 5)
    k, n, top = entries_holding_half(slow)
    print(f"\nby entry: {k} of the {n} entries with a `by` step >= 5 s hold half of that time")
    print("  " + ", ".join(f"{e} {t / 3600:.1f} h" for e, t in top))
    k, n, _ = entries_holding_half(rows)
    print(f"  all checking time: {k} of {n} entries hold half")


def sample_comparison(sample_path):
    rows = read_rows(sample_path)
    print(f"\n151-session sample ({sample_path}), published: {SAMPLE_PUBLISHED}")
    for label, chosen in (("all files", rows), ("AFP files only", afp_only(rows))):
        by = of_command(chosen, {"by"})
        steps = of_command(chosen, STEPS)
        print(f"  {label:<14}: by >= 5 s {len(at_least(by, 5)):,} steps {pct(total(at_least(by, 5)), total(chosen))}; "
              f"by >= 1 s {pct(total(at_least(by, 1)), total(chosen))}; "
              f"by/apply >= 1 s {pct(total(at_least(steps, 1)), total(chosen))}")


def quantile(xs, q):
    xs = sorted(xs)
    return xs[round(q * (len(xs) - 1))]


def overstatement(rows, sample_path):
    """This census's time over the time alone, for steps re-timed earlier; and the laptop sample's
    census time over this one's, for the same steps."""
    census = {(r["file"], r["offset"]): r["seconds"] for r in rows}
    print("\noverstatement: census time / time alone (median, p90), joined on (file, offset):")
    for path, label in RETIMES:
        with open(path) as f:
            closes = [r for r in csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE)
                      if r["verdict"] == "closes" and (r["file"], r["offset"]) in census]
        ratio = [census[(r["file"], r["offset"])] / (int(r["median_ms"]) / 1000) for r in closes]
        own = [float(r["census_s"]) / (int(r["median_ms"]) / 1000) for r in closes]
        print(f"  {label:<42} n {len(closes):>3}: this census {quantile(ratio, 0.5):.1f}x, "
              f"{quantile(ratio, 0.9):.1f}x; the census it was drawn from {quantile(own, 0.5):.1f}x, "
              f"{quantile(own, 0.9):.1f}x")
    steps = {(r["file"], r["offset"]): r["seconds"] for r in of_command(rows, STEPS)}
    sample = [r for r in afp_only(read_rows(sample_path)) if r["command"] in STEPS and r["seconds"] >= 1]
    ratio = [r["seconds"] / steps[(r["file"], r["offset"])] for r in sample if (r["file"], r["offset"]) in steps]
    print(f"  laptop sample census / this census, same steps >= 1 s in the sample: n {len(ratio):,}, "
          f"median {quantile(ratio, 0.5):.1f}x, p10 {quantile(ratio, 0.1):.1f}x, p90 {quantile(ratio, 0.9):.1f}x")


def plot(rows, sample_rows, out):
    import matplotlib.pyplot as plt
    import numpy as np
    from plot_steps import MUTED, bars, mark_slow, style

    times = np.array([r["seconds"] for r in of_command(rows, STEPS)])
    bins = np.logspace(np.log10(times.min()), np.log10(times.max()), 50)
    slow = times >= 5
    fig, axes = plt.subplots(3, 1, figsize=(8, 10), constrained_layout=True)

    bars(axes[0], times, bins)
    axes[0].set_yscale("log")
    axes[0].set_ylabel("steps (log)", color=MUTED)
    style(axes[0], f"Full AFP census: {len(times):,} by/apply steps, build-log time per step")
    mark_slow(axes[0], f"{slow.sum():,} steps ≥ 5 s")

    bars(axes[1], times, bins, weights=times / 3600)
    axes[1].set_ylabel("total hours", color=MUTED)
    style(axes[1], "Total time in each bin")
    mark_slow(axes[1], f"{times[slow].sum() / total(rows):.0%} of all checking time ≥ 5 s")

    for data, label, color in ((rows, "full AFP", "#2a78d6"), (sample_rows, "151-session sample", "#d9822b")):
        xs, share = share_curve(data)
        axes[2].plot(xs, share, color=color, linewidth=2, label=label)
    axes[2].set_ylim(0, 1)
    axes[2].set_ylabel("share of all checking time", color=MUTED)
    axes[2].set_xlabel("census seconds per step (log)", color=MUTED)
    axes[2].legend(frameon=False, fontsize=9, loc="upper right")
    style(axes[2], "Share of checking time in by/apply steps at least this slow")
    axes[2].axvline(5, color=MUTED, linestyle="--", linewidth=1)

    Path(out).parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out, dpi=150, facecolor="white")
    print(f"\nfigure: {out}")


def share_curve(rows):
    import numpy as np
    times = np.sort(np.array([r["seconds"] for r in of_command(rows, STEPS)]))[::-1]
    return times, np.cumsum(times) / total(rows)


def main():
    defaults = ["census/pc/timings_afp.tsv", "census/sample.tsv", "census/figures/steps_afp.png"]
    census, sample, figure = sys.argv[1:4] + defaults[len(sys.argv[1:4]):]
    rows = afp_only(read_rows(census))

    overview(rows)
    thresholds(rows, {"by"}, "`by`")
    thresholds(rows, STEPS, "by/apply")
    concentration(rows)
    method_mix(rows, 5)
    method_mix(rows, 1)
    by_entry(rows)
    sample_comparison(sample)
    overstatement(rows, sample)

    plot(rows, afp_only(read_rows(sample)), figure)


if __name__ == "__main__":
    main()
