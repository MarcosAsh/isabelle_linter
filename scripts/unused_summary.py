#!/usr/bin/env python3
"""Per-entry tables for an unused run: volume per lemma and per step, lost questions, timings, builds.

Usage: scripts/unused_summary.py RUN [RUN...]
A RUN is a lint_afp.py output dir (census/pc/unused, one row per entry) or a single-session dir
with lint.log, questions.tsv and build.log (census/pc/dsp/unused, one row, plus per-proof counts).
Steps are the `by` and `apply` commands of the lemmas the linter checked.
"""

import csv
import re
import statistics as st
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from lint_afp import SESSION, SUFFIX

csv.field_size_limit(1 << 30)
FINDING = re.compile(r"^(\S+?):(\d+): \[unused\] .*\n(?:.+\n)*", re.M)
TIME = re.compile(r"^time: (\d+) ms as written, (\d+) ms", re.M)
PIECE = re.compile(r"^  (fact|assumption|`have|`hence|`apply)", re.M)
HIDDEN = re.compile(r'\(\*.*?\*\)|"(?:[^"\\]|\\.)*"|\\<open>(?:(?!\\<open>).)*?\\<close>', re.S)


# by and apply commands, outside comments, strings and cartouches
def count_steps(lemma):
    while True:
        stripped = HIDDEN.sub(" ", lemma)
        if stripped == lemma:
            break
        lemma = stripped
    return len(re.findall(r"(?<![\w.'])(by|apply)(?![\w.'])", lemma))


# lemma texts of the first round, and how each question ended
def read_questions(path):
    lemmas, verdicts = {}, Counter()
    with open(path) as f:
        for r in csv.reader(f, delimiter="\t", quoting=csv.QUOTE_NONE):
            if len(r) < 5:
                continue
            verdicts[r[4]] += 1
            if r[2].endswith(":original"):
                lemmas[r[2]] = r[3]
    return lemmas, verdicts


# a finding runs to the next blank line: pieces, its time, then any assumptions
def read_findings(log_text):
    for m in FINDING.finditer(log_text):
        pieces = Counter(p.strip("`").replace("hence", "have") for p in PIECE.findall(m.group(0)))
        timed = TIME.search(m.group(0))
        yield dict(file=m.group(1), pieces=pieces, timed=(int(timed.group(1)), int(timed.group(2))) if timed else None)


def build_status(text):
    if re.search(r"^Unfinished session|FAILED|^\*\*\*", text, re.M):
        return "FAILED"
    return "ok" if re.search(r"^[\d:]+ elapsed time", text, re.M) else "none"


def machine(log_text):
    return "PC" if "/home/marcos/" in log_text else "laptop" if "/home/marcosash/" in log_text else "-"


# one group: the logs of its sessions, their question logs and its build log
def summarise(name, logs, tsvs, build):
    text = "".join(p.read_text() for p in logs)
    lemmas, verdicts = {}, Counter()
    for t in tsvs:
        l, v = read_questions(t)
        lemmas.update(l)
        verdicts.update(v)
    findings = list(read_findings(text))
    pieces = sum((f["pieces"] for f in findings), Counter())
    timed = [f["timed"] for f in findings if f["timed"]]
    return dict(name=name, machine=machine(text), lemmas=sum(map(int, re.findall(r"^(\d+) of \d+ lemmas check", text, re.M))),
                steps=sum(map(count_steps, lemmas.values())), findings=len(findings), pieces=pieces,
                fixed=sum(map(int, re.findall(r"^Fixed (\d+) lemmas", text, re.M))), timed=timed,
                questions=sum(verdicts.values()), unanswered=verdicts["unanswered"] + verdicts["interrupted"], timeouts=verdicts["timeout"],
                build=build_status(build.read_text()) if build.exists() else "none", per_file=Counter(f["file"] for f in findings),
                findings_list=findings)


# the entry of each logged session, from the copies' ROOT files
def entry_groups(run):
    owner = {}
    for root in run.glob("*/ROOT"):
        for s in SESSION.findall(root.read_text()):
            owner[s.removesuffix(SUFFIX)] = root.parent.name
    groups = {}
    for log in (run / "logs").glob("*.log"):
        entry = owner.get(log.stem.removesuffix(SUFFIX), log.stem.removesuffix(SUFFIX))
        groups.setdefault(entry, []).append(log)
    return groups


def summarise_run(run):
    if (run / "lint.log").exists():
        return [summarise(run.name, [run / "lint.log"], [run / "questions.tsv"], run / "build.log")]
    rows = []
    for entry, logs in sorted(entry_groups(run).items()):
        tsvs = [l.with_suffix(".tsv") for l in logs if l.with_suffix(".tsv").exists()]
        rows.append(summarise(entry, logs, tsvs, run / "logs" / f"{entry}.build"))
    return rows


def per100(part, whole):
    return f"{100 * part / whole:.1f}" if whole else "-"


def show_table(rows):
    print("| entry | machine | lemmas | steps | findings | facts | haves | applys | assms | fixed | "
          "removed /100 lemmas | removed /100 steps | timed ms before -> after | questions | unanswered | build |")
    print("|---" * 16 + "|")
    for r in rows + [total(rows)]:
        p, before, after = r["pieces"], sum(a for a, _ in r["timed"]), sum(b for _, b in r["timed"])
        removed = p["fact"] + p["have"] + p["apply"]
        print(f"| {r['name']} | {r['machine']} | {r['lemmas']} | {r['steps']} | {r['findings']} | {p['fact']} | "
              f"{p['have']} | {p['apply']} | {p['assumption']} | {r['fixed']} | {per100(removed, r['lemmas'])} | "
              f"{per100(removed, r['steps'])} | {before} -> {after} | "
              f"{r['questions']} | {r['unanswered']} | {r['build']} |")


def total(rows):
    t = dict(name="total", machine="", build="", timed=[], pieces=Counter())
    for k in ("lemmas", "steps", "findings", "fixed", "questions", "unanswered", "timeouts"):
        t[k] = sum(r[k] for r in rows)
    for r in rows:
        t["timed"] += r["timed"]
        t["pieces"] += r["pieces"]
    return t


# rates for comparing corpora: per 100 lemmas and per 100 steps; removed = facts + haves + applys
def show_rates(label, r):
    p = r["pieces"]
    removed = p["fact"] + p["have"] + p["apply"]
    before, after = sum(a for a, _ in r["timed"]), sum(b for _, b in r["timed"])
    ratios = [b / a for a, b in r["timed"] if a > 0]
    slower = sum(b > 1.1 * a and b - a >= 50 for a, b in r["timed"])
    faster = sum(a > 1.1 * b and a - b >= 50 for a, b in r["timed"])
    print(f"{label}: {r['lemmas']} lemmas, {r['steps']} steps; lemmas with a finding {per100(r['findings'], r['lemmas'])}%; "
          f"per 100 lemmas: facts {per100(p['fact'], r['lemmas'])}, haves {per100(p['have'], r['lemmas'])}, "
          f"applys {per100(p['apply'], r['lemmas'])}, removed {per100(removed, r['lemmas'])}; "
          f"per 100 steps: removed {per100(removed, r['steps'])}; timed fixes {len(r['timed'])}: "
          f"{before} -> {after} ms ({per100(after - before, before)}%), median ratio "
          f"{st.median(ratios) if ratios else float('nan'):.2f}; >10% and >=50 ms faster {faster}, slower {slower}")


# one finding per proof at most, as each theory holds one theorem
def show_proofs(r):
    counts = [sum(f["pieces"].values()) - f["pieces"]["assumption"] for f in r["findings_list"]]
    if counts:
        print(f"{r['name']}: {len(r['per_file'])} files with findings, removed pieces per fixed proof: "
              f"median {st.median(counts)}, max {max(counts)}, distribution {sorted(Counter(counts).items())}")


if __name__ == "__main__":
    for arg in sys.argv[1:]:
        rows = summarise_run(Path(arg))
        print(f"\n## {arg}\n")
        show_table(rows)
        print()
        show_rates(arg, total(rows))
        if len(rows) == 1:
            show_proofs(rows[0])
