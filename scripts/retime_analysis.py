#!/usr/bin/env python3
"""RQ1 numbers from the full re-time run: build-log (census) time against time alone, per band.

Usage: uv run --with matplotlib scripts/retime_analysis.py [OUT] [-s STRATA] [-c CENSUS] [-n NOTE] [-f FIGURE] [-b BOOT]
Defaults: census/pc/retime_full_out.tsv, census/retime_full_strata.tsv, census/pc/timings_afp.tsv,
census/notes/rq1_retime.md, fig_retime_bands, 1000 bootstrap resamples. Works on partial output.

Estimator: the three bands (>= 5 s, 1-5 s, 0.5-1 s of census time) are design strata, and the census
time of every `by` step in them is known. So totals use a ratio estimator per stratum, T_h * sum(alone)
/ sum(census) over the answered steps, instead of Horvitz-Thompson (N_h * mean(alone)): it has far
less variance because alone time follows census time. Counts use N_h * mean(indicator). The >= 5 s
steps of the sessions that were re-timed are taken as they are; the rest of the band (other sessions)
and the unanswered rows get the ratio of those. Steps under 0.5 s census get the 0.5-1 s ratio.
"""

import argparse
import csv
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

import numpy as np

from census_stats import afp_only, entry_of, first_method, read_rows, total
from figstyle import *  # noqa: F403
from retime_plan import BANDS

CONFIDENCE = 95
ALONE_FLOOR_S = 0.001  # the re-time is in whole ms, so a 0 ms step reads as 1 ms
ARTEFACT_RATIO = 10
LISTED = 30

# per-step features whose totals are estimated: name, is_count, function of (census, alone)
FEATURES = [
    ("alone", False, lambda c, a: a),
    ("alone_ge5", False, lambda c, a: a * (a >= 5)),
    ("alone_ge1", False, lambda c, a: a * (a >= 1)),
    ("n_ge5", True, lambda c, a: (a >= 5) * 1.0),
    ("n_ge1", True, lambda c, a: (a >= 1) * 1.0),
]
FEATURE_NAMES = [f[0] for f in FEATURES]
IS_COUNT = np.array([f[1] for f in FEATURES])
BAND_LABELS = [b[0] for b in BANDS]


@dataclass
class Step:
    key: tuple
    session: str
    file: str
    offset: str
    census: float
    band: int
    stratum: str
    verdict: str = "pending"
    alone: float = None
    text: str = ""


@dataclass
class Stratum:
    label: str
    band: int
    group: str  # whose answered steps it is estimated from
    T: float  # census seconds of every step in it
    N: int
    exact: bool = False  # answered steps count as they are, only the rest is estimated


def read_tsv(path):
    with open(path) as f:
        return list(csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE))


def band_of(seconds):
    for i, (_, lo, hi) in enumerate(BANDS):
        if lo <= seconds < hi:
            return i
    return None


def read_plan(path):
    """(file, offset) -> (band, stratum) as retime_plan.py wrote them."""
    return {(r["file"], r["offset"]): (BAND_LABELS.index(r["band"]), r["stratum"])
            for r in read_tsv(path)} if Path(path).is_file() else {}


def read_steps(out_path, plan, census_times):
    """One Step per answered or planned (file, offset); a repeated row keeps the last answer."""
    answers = {}
    for r in read_tsv(out_path):
        answers[(r["file"], r["offset"])] = r
    steps = {}
    for key in plan:
        steps[key] = new_step(key, census_times[key], plan[key])
    for key, r in answers.items():
        census = census_times.get(key, float(r["census_s"]))
        band = band_of(census)
        if key not in steps and band is not None:
            steps[key] = new_step(key, census, (band, "all" if band == 0 else "in"), unplanned=True)
        fill_answer(steps.get(key), r)
    return [s for s in steps.values()]


def new_step(key, census, placed, unplanned=False):
    band, stratum = placed
    return Step(key, "", key[0], key[1], census, band, stratum + ("*" if unplanned else ""))


def fill_answer(step, r):
    if step is None:
        return
    step.session, step.text, step.verdict = r["session"], r["text"], r["verdict"]
    if r["verdict"] == "closes":
        step.alone = max(int(r["median_ms"]) / 1000, ALONE_FLOOR_S)


def fill_sessions(steps, census_rows):
    sessions = {(r["file"], r["offset"]): r["session"] for r in census_rows}
    for s in steps:
        s.session = s.session or sessions.get(s.key, "?")


def load_census(path):
    rows = afp_only(read_rows(path))
    times = {(r["file"], r["offset"]): r["seconds"] for r in rows}
    return rows, times


def design(rows, steps):
    """Strata of the population of `by` steps >= 0.5 s, and the data the estimators need."""
    placed = {s.key: s for s in steps}
    covered = {s.session for s in steps if s.band == 0}
    by = [r for r in rows if r["command"] == "by"]
    pop = {}
    for r in by:
        key = (r["file"], r["offset"])
        band = band_of(r["seconds"])
        if band is not None:
            pop[key] = (band, stratum_of(r, key, band, placed, covered), r["seconds"])
    strata = make_strata(pop)
    below = sum(r["seconds"] for r in by if band_of(r["seconds"]) is None)
    return strata, below, total(by), total(rows)


def stratum_of(r, key, band, placed, covered):
    if key in placed:
        return placed[key].stratum.rstrip("*")
    if band == 0:
        return "other"
    return "in" if r["session"] in covered else "out"


def make_strata(pop):
    sums = Counter()
    counts = Counter()
    for band, stratum, seconds in pop.values():
        sums[band, stratum] += seconds
        counts[band, stratum] += 1
    strata = []
    for (band, stratum), t in sorted(sums.items()):
        group = (band, "all") if stratum == "other" else (band, stratum)
        exact = stratum == "all"
        strata.append(Stratum(f"{BAND_LABELS[band]} {stratum}", band, f"{group[0]}:{group[1]}",
                              t, counts[band, stratum], exact))
    return strata


def groups_of(steps):
    """Answered steps per sampling group: arrays of census, alone and session."""
    out = {}
    for s in steps:
        if s.alone is not None:
            out.setdefault(f"{s.band}:{s.stratum.rstrip('*')}", []).append(s)
    return {g: (np.array([s.census for s in ss]), np.array([s.alone for s in ss]),
                np.array([s.session for s in ss])) for g, ss in out.items()}


def feature_matrix(c, a):
    return np.column_stack([f[2](c, a) for f in FEATURES])


def stratum_totals(s, sample, observed):
    """Estimated totals of FEATURES over the stratum; None if no step of it is answered."""
    c, a = sample
    if len(c) == 0:
        return None
    f = feature_matrix(c, a)
    per_unit = np.where(IS_COUNT, f.mean(0), f.sum(0) / c.sum())
    base, rem_t, rem_n = 0, s.T, s.N
    if s.exact:
        oc, oa = observed
        base, rem_t, rem_n = feature_matrix(oc, oa).sum(0), s.T - oc.sum(), s.N - len(oc)
    return base + np.where(IS_COUNT, rem_n, rem_t) * per_unit


def weighted_quantile(values, weights, q):
    order = np.argsort(values)
    cum = np.cumsum(weights[order])
    return values[order][np.searchsorted(cum, q * cum[-1])]


def group_weights(strata, observed):
    w = Counter()
    for s in strata:
        w[s.group] += s.N
    return {g: w[g] / len(observed[g][0]) for g in observed}


def ratio_stats(band, groups, weights):
    """Weighted median, p10, p90 of census/alone and the share with alone slower than the census."""
    sel = [g for g in groups if g.startswith(f"{band}:") and len(groups[g][0])]
    if not sel:
        return {}
    r = np.concatenate([groups[g][0] / groups[g][1] for g in sel])
    w = np.concatenate([np.full(len(groups[g][0]), weights[g]) for g in sel])
    return {f"{band}:p50": weighted_quantile(r, w, 0.5), f"{band}:p10": weighted_quantile(r, w, 0.1),
            f"{band}:p90": weighted_quantile(r, w, 0.9), f"{band}:slower": w[r < 1].sum() / w.sum()}


def estimate(d, samples, observed):
    """Every reported number, as one flat dict, from `samples` (resampled or not) and `observed`."""
    band_tot = {b: np.zeros(len(FEATURES)) for b in range(len(BANDS))}
    incomplete = set()
    for s in d["strata"]:
        t = stratum_totals(s, samples.get(s.group, ((), ())), observed.get(s.group))
        if t is None:
            incomplete.add(s.band)
        else:
            band_tot[s.band] += t
    for b in incomplete:  # a band with a stratum not started has no total yet
        band_tot[b][:] = np.nan
    flat = {f"{b}:{n}": band_tot[b][i] for b in band_tot for i, n in enumerate(FEATURE_NAMES)}
    for b in band_tot:
        flat.update(ratio_stats(b, samples, d["weights"]))
    flat.update(headline(d, band_tot, incomplete))
    return flat


def headline(d, band_tot, incomplete):
    out = {}
    for n in ("alone_ge5", "alone_ge1", "n_ge5", "n_ge1"):
        out[n] = sum(band_tot[b][FEATURE_NAMES.index(n)] for b in band_tot if b not in incomplete)
    alone = sum(band_tot[b][0] for b in band_tot if b not in incomplete)
    r_low = band_tot[2][0] / d["band_T"][2] if 2 not in incomplete and d["band_T"][2] else np.nan
    by_alone = alone + d["below_T"] * r_low if not incomplete else np.nan
    scaled_all = d["all_T"] * by_alone / d["by_T"]
    nonby = d["all_T"] - d["by_T"]
    for t in (5, 1):
        num = out[f"alone_ge{t}"]
        out[f"share_census_den_{t}"] = num / d["all_T"]
        out[f"share_by_scaled_{t}"] = num / (nonby + by_alone)
        out[f"share_all_scaled_{t}"] = num / scaled_all
    out["by_alone"] = by_alone
    return out


def resample(groups, rng, by_session):
    out = {}
    for g, (c, a, sess) in groups.items():
        idx = session_indices(sess, rng) if by_session else rng.integers(0, len(c), len(c))
        out[g] = (c[idx], a[idx], sess[idx])
    return out


def session_indices(sess, rng):
    names = np.unique(sess)
    picked = rng.choice(names, len(names))
    return np.concatenate([np.flatnonzero(sess == n) for n in picked])


def bootstrap(d, groups, n, by_session, seed=1):
    rng = np.random.default_rng(seed)
    observed = {g: v[:2] for g, v in groups.items()}
    runs = []
    for _ in range(n):
        res = resample(groups, rng, by_session)
        runs.append(estimate(d, {g: v[:2] for g, v in res.items()}, observed))
    keys = runs[0].keys() if runs else []
    return {k: np.array([r.get(k, np.nan) for r in runs]) for k in keys}


# ---- text output ----

def interval(boot, key):
    x = boot.get(key) if boot else None
    if x is None or len(x) == 0 or not np.isfinite(x).all():
        return None
    half = (100 - CONFIDENCE) / 2
    return np.percentile(x, [half, 100 - half])


def show(est, boot, key, fmt):
    if not np.isfinite(est.get(key, np.nan)):
        return "n/a"
    ci = interval(boot, key)
    span = f" [{fmt(ci[0])}, {fmt(ci[1])}]" if ci is not None else ""
    return fmt(est[key]) + span


def hours(x):
    return f"{x / 3600:.2f} h"


def num1(x):
    return f"{x:.1f}"


def ratio_fmt(x):
    return f"{x:.1f}x"


def percent(x):
    return f"{100 * x:.1f}%"


def count0(x):
    return f"{x:,.0f}"


def table(header, rows):
    lines = ["| " + " | ".join(header) + " |", "|" + "|".join("---" for _ in header) + "|"]
    return lines + ["| " + " | ".join(map(str, r)) + " |" for r in rows]


def coverage_section(steps, d, out_rows):
    planned = [s for s in steps if not s.stratum.endswith("*")]
    verdicts = Counter(s.verdict for s in planned)
    lines = ["## Coverage", ""]
    done = sum(v for k, v in verdicts.items() if k != "pending")
    lines.append(f"Planned rows done: {done:,} of {len(planned):,} ({100 * done / max(len(planned), 1):.1f}%); "
                 f"output rows read: {out_rows:,}. Unplanned rows in the output (not in the strata file): "
                 f"{sum(s.stratum.endswith('*') for s in steps):,}.")
    lines.append("")
    rows = []
    for key in sorted({(s.band, s.stratum.rstrip("*")) for s in steps}):
        part = [s for s in steps if (s.band, s.stratum.rstrip("*")) == key]
        c = Counter(s.verdict for s in part)
        other = sum(v for k, v in c.items() if k not in ("closes", "not_found", "pending"))
        rows.append([BAND_LABELS[key[0]], key[1], len(part), c["closes"], c["not_found"], other,
                     c["pending"]])
    lines += table(["band", "stratum", "planned", "closes", "not_found", "other verdict", "not yet"], rows)
    lines += ["", why_lines(steps), "", population_lines(d)]
    return lines


def why_lines(steps):
    nf = Counter(s.session for s in steps if s.verdict == "not_found")
    other = Counter(s.verdict for s in steps if s.verdict not in ("closes", "not_found", "pending"))
    text = ("`not_found`: the step at that offset was not found among the re-checked theory's ok lemmas "
            f"(so it cannot be timed): {sum(nf.values()):,} steps"
            + (", mostly in " + ", ".join(f"{k} {v}" for k, v in nf.most_common(5)) if nf else "") + ". ")
    text += ("Other verdicts (the step did not close alone, timed out or got no answer): "
             + ", ".join(f"{k} {v}" for k, v in other.most_common()) + "." if other
             else "No step failed, timed out or went unanswered.")
    done = {s.session for s in steps if s.verdict != "pending"}
    todo = {s.session for s in steps if s.verdict == "pending"}
    return text + f" Sessions with output: {len(done)}; sessions still to do: {len(todo - done)}."


def population_lines(d):
    rows = [[s.label, f"{s.N:,}", f"{s.T / 3600:.2f} h", "as measured + estimated rest" if s.exact else "ratio estimator"]
            for s in d["strata"]]
    return "\n".join(["Strata of the population (`by` steps >= 0.5 s census, AFP files):", ""]
                     + table(["stratum", "steps", "census time", "estimate"], rows))


def totals_section(d, est, b_step, b_sess, groups):
    lines = ["## Time alone against census time, per band", "",
             f"Totals over all `by` steps of the band ({CONFIDENCE}% bootstrap CI over steps, resampled "
             "within sampling groups; the session-resampled CI is in the last column).", ""]
    rows = []
    for b, label in enumerate(BAND_LABELS):
        n = sum(len(v[0]) for g, v in groups.items() if g.startswith(f"{b}:"))
        agg = est[f"{b}:alone"]
        rows.append([label, f"{d['band_N'][b]:,}", n, hours(d["band_T"][b]),
                     show(est, b_step, f"{b}:alone", hours),
                     show(est, b_sess, f"{b}:alone", hours),
                     ratio_fmt(d["band_T"][b] / agg) if agg > 0 else "n/a"])
    lines += table(["band", "steps", "answered", "census time", "alone (est.)", "alone, session CI",
                    "census/alone, aggregate"], rows)
    return lines


def ratios_section(est, b_step, groups):
    lines = ["## Overstatement per band: census time / time alone, per step", "",
             "Weighted by the sampling weights (stratum size / answered steps); CI on the median.", ""]
    rows = []
    for b, label in enumerate(BAND_LABELS):
        n = sum(len(v[0]) for g, v in groups.items() if g.startswith(f"{b}:"))
        rows.append([label, n, show(est, b_step, f"{b}:p50", ratio_fmt), show(est, {}, f"{b}:p10", ratio_fmt),
                     show(est, {}, f"{b}:p90", ratio_fmt), show(est, {}, f"{b}:slower", percent)])
    return lines + table(["band", "answered", "median", "p10", "p90", "share where alone is slower"], rows)


def headline_section(d, est, b_step, b_sess):
    lines = ["## Corrected RQ1 headline", ""]
    lines += [f"Share of AFP checking time in `by` steps that take >= t s alone, with three denominators "
              f"(census total {hours(d['all_T'])}, of which `by` steps {hours(d['by_T'])}):", ""]
    rows = []
    for label, key in (("A: census total (non-`by` and `by` below 0.5 s as in the census)", "share_census_den"),
                       ("B: non-`by` census + `by` steps' total time alone", "share_by_scaled"),
                       ("C: census total scaled by the `by` alone/census ratio", "share_all_scaled")):
        rows.append([label] + [show(est, b_step, f"{key}_{t}", percent) for t in (5, 1)])
    rows.append(["same steps, census time (the old headline, for reference)"]
                + [percent(d["census_share"][t]) for t in (5, 1)])
    lines += table(["denominator", ">= 5 s alone", ">= 1 s alone"], rows)
    used = [BAND_LABELS[b] for b in range(len(BANDS)) if np.isfinite(est[f"{b}:alone"])]
    if len(used) < len(BANDS):
        lines += ["", f"PARTIAL: numerators A use only the bands with every stratum started ({', '.join(used) or 'none'}); "
                  "B and C need all three."]
    lines += ["", f"Session-resampled CI, denominator B: >= 5 s {show(est, b_sess, 'share_by_scaled_5', percent)}, "
              f">= 1 s {show(est, b_sess, 'share_by_scaled_1', percent)}.", ""]
    lines += [f"Steps that stay >= 5 s alone: {show(est, b_step, 'n_ge5', count0)} "
              f"(of {d['band_N'][0]:,} at >= 5 s census); steps >= 1 s alone: {show(est, b_step, 'n_ge1', count0)}. "
              f"Time in them alone: {show(est, b_step, 'alone_ge5', hours)} and {show(est, b_step, 'alone_ge1', hours)}.",
              f"Estimated total time alone of all `by` steps: {show(est, b_step, 'by_alone', hours)}."]
    return lines


def artefact_section(steps, path):
    odd = sorted((s for s in steps if s.alone and s.census / s.alone > ARTEFACT_RATIO),
                 key=lambda s: -s.census / s.alone)
    answered = sum(s.alone is not None for s in steps)
    lines = ["## Steps far slower in the census than alone (ratio > 10)", "",
             f"{len(odd):,} of {answered:,} answered steps. Full list: `{path}`.", ""]
    if not odd:
        return lines
    by_session = Counter(s.session for s in odd).most_common(8)
    by_method = Counter(first_method(s.text) for s in odd).most_common(8)
    lines += ["By session: " + ", ".join(f"{k} {v}" for k, v in by_session) + ".",
              "By first method: " + ", ".join(f"{k} {v}" for k, v in by_method) + ".", ""]
    rows = [[entry_of(s.file), f"{Path(s.file).name}:{s.offset}", f"{s.census:.1f}", f"{s.alone:.3f}",
             f"{s.census / s.alone:.0f}x", s.text[:70].replace("|", "\\|")] for s in odd[:LISTED]]
    lines += table(["entry", "theory:offset", "census s", "alone s", "ratio", "text"], rows)
    write_artefacts(path, odd)
    return lines


def write_artefacts(path, odd):
    with open(path, "w") as f:
        f.write("entry\tsession\tfile\toffset\tcensus_s\talone_s\tratio\ttext\n")
        for s in odd:
            f.write(f"{entry_of(s.file)}\t{s.session}\t{s.file}\t{s.offset}\t{s.census:.3f}\t{s.alone:.3f}\t"
                    f"{s.census / s.alone:.1f}\t{s.text}\n")


METHOD_NOTES = """## Method and assumptions

- Population: the `by` steps of AFP files with census time >= 0.5 s (`census/pc/timings_afp.tsv`),
  in three bands. Steps are the census's own (file, offset) keys; "alone" is the median of the
  re-time's runs (one run each, boost off), the census was built with boost on at `-j 3 -t 5`, so
  the census/alone ratio also contains a boost factor of about 1.3.
- Estimator: ratio estimator per stratum (totals) because census time is known for all of the
  population and predicts alone time; Horvitz-Thompson would have the same expectation and a much
  wider interval. Quantiles are weighted by stratum size / answered steps.
- >= 5 s band: the re-timed sessions were chosen by most slow time per PC hour, not at random. Their
  steps count as measured; the steps of the other sessions get the ratio of the measured ones. This
  assumes those sessions are not different, which the plan does not guarantee.
- Steps without an answer (`not_found`, failed, not yet done) are imputed with their stratum's ratio,
  i.e. assumed to behave like the answered ones.
- Steps below 0.5 s census are not re-timed. For denominators B and C they get the 0.5-1 s ratio, and
  they add nothing to the >= 1 s alone numbers (a step under 0.5 s in the census is assumed to stay under 1 s).
- Denominators: the numerator is always time alone. A divides by the census total, which is inflated
  (under-states the share). B keeps the census time of non-`by` commands and replaces the `by` steps'
  by their time alone. C also scales the non-`by` commands by the `by` steps' alone/census ratio, which
  assumes they are overstated alike. The truth for the non-`by` commands is not measured.
- Bootstrap: resamples answered steps with replacement within each sampling group, the second one resamples
  whole sessions (steps of a session share its load and its anomalies). The part of the >= 5 s stratum
  that was measured is held fixed; only the extrapolated part varies.
- Partial data: the run goes by session in order of census time, so partial results are the biggest
  sessions and are not a random sample. Bands with a stratum that has no answered step yet show n/a.
"""


def figure(steps, d, groups, name):
    fig, ax = plt.subplots(figsize=(6.5, 3.8))  # noqa: F405
    w = group_weights(d["strata"], {g: v[:2] for g, v in groups.items()})
    for b, label in enumerate(BAND_LABELS):
        sel = [g for g in groups if g.startswith(f"{b}:")]
        if not sel:
            continue
        r = np.concatenate([groups[g][0] / groups[g][1] for g in sel])
        wt = np.concatenate([np.full(len(groups[g][0]), w[g]) for g in sel])
        order = np.argsort(r)
        ax.step(r[order], np.cumsum(wt[order]) / wt.sum(), where="post", color=SERIES[b],  # noqa: F405
                linewidth=1.8, label=f"{label} (n {len(r)})")
    ax.set_xscale("log")
    ax.axvline(1, color=MUTED, linewidth=0.8, linestyle=":")  # noqa: F405
    ax.set_xlabel("census time / time alone, per step")
    ax.set_ylabel("share of steps in the band")
    ax.set_ylim(0, 1)
    ax.legend(loc="lower right")
    style(ax, "How much the build log overstates a step", grid="both")  # noqa: F405
    save(fig, name)  # noqa: F405


def summary(steps):
    answered = sum(s.alone is not None for s in steps)
    pending = sum(s.verdict == "pending" for s in steps)
    return (f"**{'PARTIAL: ' if pending else ''}{answered:,} steps answered, {pending:,} planned rows "
            "not done yet.**" + (" The run is incomplete: totals are extrapolated from the sessions "
                                  "done so far, which are the biggest ones." if pending else ""))


def main():
    p = argparse.ArgumentParser()
    p.add_argument("out", nargs="?", default="census/pc/retime_full_out.tsv")
    p.add_argument("-s", default="census/retime_full_strata.tsv")
    p.add_argument("-c", default="census/pc/timings_afp.tsv")
    p.add_argument("-n", default="census/notes/rq1_retime.md")
    p.add_argument("-f", default="fig_retime_bands")
    p.add_argument("-b", type=int, default=1000)
    args = p.parse_args()

    rows, census_times = load_census(args.c)
    plan = read_plan(args.s)
    steps = read_steps(args.out, plan, census_times)
    fill_sessions(steps, rows)
    strata, below, by_t, all_t = design(rows, steps)
    groups = groups_of(steps)
    observed = {g: v[:2] for g, v in groups.items()}
    band_t = {b: sum(s.T for s in strata if s.band == b) for b in range(len(BANDS))}
    band_n = {b: sum(s.N for s in strata if s.band == b) for b in range(len(BANDS))}
    by = [r for r in rows if r["command"] == "by"]
    d = {"strata": strata, "below_T": below, "by_T": by_t, "all_T": all_t, "band_T": band_t, "band_N": band_n,
         "weights": group_weights(strata, observed),
         "census_share": {t: sum(r["seconds"] for r in by if r["seconds"] >= t) / all_t for t in (5, 1)}}
    if not groups:
        raise SystemExit("no answered steps in " + args.out)
    est = estimate(d, {g: v[:2] for g, v in groups.items()}, observed)
    b_step = bootstrap(d, groups, args.b, by_session=False)
    b_sess = bootstrap(d, groups, args.b, by_session=True)

    artefacts = str(Path(args.n).with_name("rq1_retime_ratio10.tsv"))
    lines = ["# RQ1: `by` steps timed alone (full AFP re-time)", "",
             f"Generated by `scripts/retime_analysis.py` from `{args.out}`. {summary(steps)}", ""]
    lines += coverage_section(steps, d, len(read_tsv(args.out))) + [""]
    lines += totals_section(d, est, b_step, b_sess, groups) + [""]
    lines += ratios_section(est, b_step, groups) + [""]
    lines += headline_section(d, est, b_step, b_sess) + [""]
    lines += artefact_section(steps, artefacts) + [""]
    lines += [f"Figure: `census/figures/{args.f}.png`.", ""] + METHOD_NOTES.split("\n")

    Path(args.n).parent.mkdir(parents=True, exist_ok=True)
    Path(args.n).write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    print("\nwrote", args.n)
    figure(steps, d, groups, args.f)


if __name__ == "__main__":
    main()
