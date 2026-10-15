#!/usr/bin/env python3
"""Why slow `by` steps are slow: Poly/ML profiles grouped by Isabelle subsystem.

Usage: scripts/root_causes.py [-O STEPS.tsv]
Reads the profiles of `linter_retime -P` for the census's top 200 steps (laptop) and the 1-5 s
band (timing PC), their re-times, the AFP sources and the faster_step question logs. Prints, per
corpus, each subsystem's share of the samples, the steps' dominant cause weighted by re-timed
time, and that cause against the step's method and against whether faster_step found an edit.
"""

import csv
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORPORA = [
    ("top 200 (laptop)", "census/profiles.tsv", "census/retime2.tsv"),
    ("1-5 s band (PC)", "census/pc/profiles_band.tsv", "census/pc/retime_band.tsv"),
]
LOGS = "census/pc/faster_step/logs"
ISABELLE_HOME = "~/opt/isabelle/Isabelle2025-2"
SPEEDUP = 2

# a profile covering less of the wall time than this ran mostly off this thread; one with fewer
# samples than MIN_SAMPLES says nothing
MIN_COVERAGE = 0.5
MIN_SAMPLES = 50

# first match wins; names are Poly/ML's, with functor instances as `Table()`
SUBSYSTEMS = [
    ("metis", r"Metis_|Metis\.|Meson\.|ATP_"),
    ("smt", r"SMT|Verit_|Z3_|Lethe_|Monomorph\."),
    ("code_eval", r"Generated_Code\.|Code_|Code\.|Codetree|BaseCodeTree|X86|CODEGEN|TYPE_TREE|TYPECHECK|"
                  r"LEX_|SKIPS_|UTILITIES_|ML_Compiler|ML_Env|polyCompiler|IntSet\.|StronglyConnected"),
    ("classical", r"Blast\(|Classical|Clasimp|Hypsubst|Context_Rules|Bires\.|Search\."),
    ("arith", r"Lin_Arith|Fast_Lin_Arith|Arith_Data|Numeral_Simprocs|Nat_Arith|Base_Order_Tac|"
              r"Order_Procedure|Cooper|Presburger|Semiring_Normalizer|Groebner|HOLogic\.dest_number"),
    ("datatype_sugar", r"BNF_|Ctr_Sugar|Datatype_Simprocs|Morphism\.|Binding\."),
    ("transfer", r"Thm\.(transfer|join_transfer|join_certificate)|Context\.(proper_)?subthy|IntInf\.divMod$|Bitset\."),
    ("simp", r"Raw_Simplifier|Simplifier|Splitter\(|Simpdata|Term_Ord\.|Record\.|Conv\.|Config\.|"
             r"Pattern\.(match_rew|rewrite_term)|Thm\.(eta_conversion|check_conv)|Term\.could_eta_contract"),
    ("sorts", r"Sorts\.|Thm\.(theory_names_of_arity|solve_constraints|strip_shyps|constraint_digest|"
              r"insert_constraints|add_sorts)|Type\.cert_sort"),
    ("proof_state", r"Logic\.(nth_prem|list_implies|count_prems|strip_params|remove_params|strip_assums_hyp|"
                    r"strip_imp_prems)|Thm\.(dest_state|strip_assums2|norm_term_skip)|Drule\.strip_imp_prems"),
    ("term_index", r"Net\.|Item_Net"),
    ("match", r"Pattern\.(match|first_order_match|typ_match)$|Thm\.(match|first_order_match|gen_match)|"
              r"Type\.(typ_match|raw_match|could_match)"),
    ("unify", r"Unify\.|Pattern\.|Envir\.|Thm\.(bicompose|biresolution|could_bires|eq_assumption|assumption)|"
              r"Type\.(unify|unified)|Term\.could_unify"),
    ("inst_lift", r"Term_Subst\.|Same\.|Drule\.|TVars|Vars\.|"
                  r"Thm\.(lift_rule|incr_indexes|instantiate|gen_instantiate|make_inst|prep_insts|rename_bv|"
                  r"adjust_maxidx|unify_var_types)|Logic\.(incr_indexes_operation|incr_tvar_same|lift_all|lift_abs)|"
                  r"Term\.(map_atyps_same|map_types_same|incr_bv_same|map_aterms_same)"),
    ("elaboration", r"Type_Infer|Syntax|Sign\.|Proof_Context|Variable\.|Name_Space|Consts\.|Name\.|"
                    r"Pretty\.|Symbol\.|Term_Position"),
]
# mechanisms recognisable from a few telltale functions, whatever the dominant subsystem
SIGNATURES = [
    ("datatype simproc transfers sugar", lambda f: f["BNF_Def.map_facts"] > 0),
    ("many subgoals (nth_prem, dest_state)", lambda f: f["Logic.nth_prem"] + f["Thm.dest_state"] >= 0.05),
    ("sort constraints (Sorts.*) >= 5%", lambda f: sum(v for k, v in f.items() if k.startswith("Sorts.")) >= 0.05),
    ("lifting (incr_indexes) >= 5%", lambda f: f["Logic.incr_indexes_operation"] >= 0.05),
    ("code evaluation >= 20%", lambda f: sum(v for k, v in f.items() if k.startswith("Generated_Code")) >= 0.2),
    ("metis search >= 50%", lambda f: sum(v for k, v in f.items() if k.startswith("Metis_")) >= 0.5),
]
SHARED = "shared"
TAIL = "tail"
CAUSES = [name for name, _ in SUBSYSTEMS]

METHOD_FAMILIES = [
    ("smt", r"smt"), ("metis", r"metis|meson"), ("eval", r"eval|approximation|normalization|code_simp"),
    ("blast", r"blast"), ("force", r"force|fastforce|fast|best|bestsimp|slowsimp"), ("auto", r"auto"),
    ("simp", r"simp|simp_all"), ("arith", r"arith|linarith|presburger"),
]
METHOD_WORDS = re.compile(r"\b(" + "|".join(p for _, p in METHOD_FAMILIES) + r"|clarsimp|induct|induction|cases|"
                          r"rule|intro|elim|erule|drule|frule|subst|unfold|insert|use|in|add|del|only|split|"
                          r"splits|cong|dest|iff|simp_all|no_types|opaque_lifting|full_types|verit|z3|cvc5|"
                          r"arbitrary|taking|of|OF|THEN|where|for|symmetric|rule_format|auto|assumption)\b")
SYMBOL = re.compile(r"\\<\^?[A-Za-z0-9_']+>|.", re.S)
LEMMA = re.compile(r"^\s*(lemma|theorem|corollary|proposition|schematic_goal|interpretation|instance|"
                   r"termination|function|lift_definition)\b", re.M)
PROOF_START = re.compile(r"\b(proof|apply|by|using|unfolding|including|supply)\b")
CLAUSE = re.compile(r"\b(have|show|hence|thus|obtain|then|moreover|ultimately|case|next|from|with|note)\b")


def subsystem(function):
    for name, pattern in SUBSYSTEMS:
        if re.match(pattern, function):
            return name
    return SHARED


def read_tsv(path):
    with open(ROOT / path) as f:
        return list(csv.DictReader(f, delimiter="\t"))


def step_key(row):
    return row["file"], row["offset"]


# the top 40 functions of each step, summed by subsystem; what the top 40 miss is the tail
def read_profiles(path):
    profiles = defaultdict(lambda: {"total": 0, "functions": Counter()})
    for r in read_tsv(path):
        p = profiles[step_key(r)]
        p["total"] = int(r["total"])
        p["functions"][r["function"]] += int(r["count"])
    return profiles


def shares(profile):
    total = profile["total"] or 1
    out = Counter()
    for function, count in profile["functions"].items():
        out[subsystem(function)] += count / total
    out[TAIL] = max(0.0, 1 - sum(profile["functions"].values()) / total)
    return out


def method_family(text):
    body = re.sub(r"\\<comment>.*", "", text)
    for name, pattern in METHOD_FAMILIES:
        if re.search(r"\b(" + pattern + r")\b", body):
            return name
    return "other"


def dominant(step):
    if step["samples"] < MIN_SAMPLES:
        return "no_profile"
    if step["coverage"] < MIN_COVERAGE and step["method"] == "smt":
        return "external_wait"
    own = {c: step["shares"][c] for c in CAUSES}
    return max(own, key=own.get)


# --- goal-size proxies from the AFP source, without Isabelle ---

def entry(file):
    return file.split("/thys/")[1].split("/")[0] if "/thys/" in file else "Isabelle/" + file.split("/")[-2]


def source(file):
    try:
        return Path(file.replace("~~", ISABELLE_HOME, 1)).expanduser().read_text(errors="replace")
    except OSError:
        return None


# 1-based Isabelle symbol offset -> 0-based character offset
def char_offset(text, symbol_offset):
    for pos, m in enumerate(SYMBOL.finditer(text), start=1):
        if pos == symbol_offset:
            return m.start()
    return len(text)


def fact_count(text):
    body = re.sub(r"\\<comment>.*|\(\*.*?\*\)", "", text, flags=re.S)
    words = re.findall(r"[A-Za-z_][\w'.]*", METHOD_WORDS.sub(" ", body[2:] if body.startswith("by") else body))
    return len(words)


def proxies(row, cache):
    text = cache.setdefault(row["file"], source(row["file"]))
    out = {"text_len": len(row["text"].strip()), "facts": fact_count(row["text"]),
           "using_facts": "", "statement_len": "", "depth_chars": ""}
    if text is None:
        return out
    at = char_offset(text, int(row["offset"]))
    lemmas = list(LEMMA.finditer(text, 0, at))
    if not lemmas:
        return out
    start = lemmas[-1].start()
    proof = PROOF_START.search(text, lemmas[-1].end(), at + 1)
    out["statement_len"] = (proof.start() if proof else at) - start
    out["depth_chars"] = at - start
    clauses = list(CLAUSE.finditer(text, start, at))
    lead = text[clauses[-1].start() if clauses else start:at]
    using = re.search(r"\b(using|from|with)\b(.*)", lead, re.S)
    out["using_facts"] = name_count(using.group(2)) if using else 0
    return out


def name_count(facts):
    return len(re.findall(r"[A-Za-z_][\w'.]*", re.sub(r"\b(and|of|OF|THEN|where)\b", " ", facts)))


# --- faster_step: which profiled steps got a faster verified edit ---

def ms(question, name="ms"):
    for p in question[5:]:
        if p.startswith(name + "="):
            return int(p.split("=", 1)[1])
    return 0


def norm(methods):
    return " ".join(methods.split())


# (theory base name, methods) -> [(character offset, hit)] for every step faster_step searched
def read_searches():
    found = defaultdict(list)
    for log in sorted((ROOT / LOGS).glob("*.tsv")):
        steps = defaultdict(list)
        with open(log) as f:
            for r in csv.reader(f, delimiter="\t"):
                if len(r) >= 5 and r[0] == "faster_step":
                    steps[":".join(r[2].split(":", 3)[:3])].append(r)
        for key, questions in steps.items():
            original, rest = questions[0], questions[1:]
            if not rest or original[4] != "closes":
                continue
            hit = any(q[1] == "linter_time" and q[4] == "closes" and ms(q, "ms2") * SPEEDUP < ms(q) for q in rest)
            theory, _, offset = key.split(":")
            found[(theory.split(".")[-1], norm(original[3]))].append((int(offset), hit))
    return found


def edit_status(row, searches, cache):
    methods = norm(re.sub(r"\\<comment>.*|\(\*.*?\*\)", "", row["text"])[2:])
    candidates = searches.get((Path(row["file"]).stem, methods))
    if not candidates:
        return "not_searched"
    text = cache.get(row["file"])
    at = char_offset(text, int(row["offset"])) if text else 0
    hits = [hit for offset, hit in candidates if offset == at]
    if not hits:
        return "not_searched"
    return "faster_edit" if hits[0] else "no_edit"


# --- one record per profiled step ---

def steps_of(corpus, searches, cache):
    name, profile_path, retime_path = corpus
    profiles = read_profiles(profile_path)
    out = []
    for r in read_tsv(retime_path):
        p = profiles.get(step_key(r))
        if r["verdict"] != "closes" or p is None:
            continue
        step = {"corpus": name, "file": r["file"], "offset": r["offset"], "text": r["text"].strip(),
                "entry": entry(r["file"]), "ms": int(r["median_ms"]),
                "gc_ms": int(r["gc_ms"] or 0), "samples": p["total"], "method": method_family(r["text"]),
                "shares": shares(p), "top": p["functions"].most_common(3),
                "fractions": Counter({k: v / max(1, p["total"]) for k, v in p["functions"].items()})}
        step["coverage"] = step["samples"] / max(1, step["ms"])
        step["cause"] = dominant(step)
        step.update(proxies(r, cache))
        step["edit"] = edit_status(r, searches, cache)
        out.append(step)
    return out


# --- printing ---

def pct(x):
    return f"{x:6.1%}"


def subsystem_shares(steps):
    weight = sum(s["ms"] for s in steps)
    print("  subsystem share of samples, steps weighted by re-timed time:")
    for c in CAUSES + [SHARED, TAIL]:
        share = sum(s["shares"][c] * s["ms"] for s in steps) / weight
        print(f"    {c:15s} {pct(share)}")
    print(f"    (gc, from the re-time, as a share of wall time: {pct(sum(s['gc_ms'] for s in steps) / weight).strip()}; "
          f"samples per wall ms: {sum(s['samples'] for s in steps) / weight:.2f})")


def distribution(steps):
    weight = sum(s["ms"] for s in steps)
    by_cause = defaultdict(list)
    for s in steps:
        by_cause[s["cause"]].append(s)
    print(f"  dominant cause ({len(steps)} steps, {weight / 1000:.0f} s): steps, share of time, "
          f"median share of the step's samples, steps profiled under half their wall time")
    for c, group in sorted(by_cause.items(), key=lambda kv: -sum(s["ms"] for s in kv[1])):
        own = median([s["shares"].get(c, 0) for s in group])
        low = sum(s["coverage"] < MIN_COVERAGE for s in group)
        print(f"    {c:15s} {len(group):4d}  {pct(sum(s['ms'] for s in group) / weight)}  {pct(own)}  {low:4d}")


def crosstab(steps, field, title):
    causes = [c for c, _ in Counter(s["cause"] for s in steps).most_common()]
    values = [v for v, _ in Counter(s[field] for s in steps).most_common()]
    print(f"  {title}: steps (seconds)")
    print("    " + " " * 15 + "".join(f"{v[:12]:>16s}" for v in values))
    for c in causes:
        cells = [[s for s in steps if s["cause"] == c and s[field] == v] for v in values]
        print(f"    {c:15s}" + "".join(f"{len(g):6d} ({sum(s['ms'] for s in g) / 1000:6.0f})" for g in cells))


def proxy_summary(steps):
    print("  goal-size proxies by cause (medians): text_len facts using_facts statement_len depth_chars gc%")
    for c in sorted({s["cause"] for s in steps}):
        group = [s for s in steps if s["cause"] == c]
        cells = [median([s[k] for s in group if s[k] != ""]) for k in
                 ("text_len", "facts", "using_facts", "statement_len", "depth_chars")]
        gc = median([s["gc_ms"] / max(1, s["ms"]) for s in group])
        print(f"    {c:15s} " + " ".join(f"{x:8.0f}" for x in cells) + f"  {pct(gc)}")


def median(xs):
    xs = sorted(xs)
    return xs[len(xs) // 2] if xs else float("nan")


def signatures(steps):
    weight = sum(s["ms"] for s in steps)
    print("  signatures: steps, share of time, faster edits / searched")
    for name, test in SIGNATURES:
        group = [s for s in steps if test(s["fractions"])]
        searched = [s for s in group if s["edit"] != "not_searched"]
        hits = sum(s["edit"] == "faster_edit" for s in searched)
        print(f"    {name:38s} {len(group):4d}  {pct(sum(s['ms'] for s in group) / weight)}  {hits}/{len(searched)}")


def examples(steps):
    print("  slowest step per cause:")
    for c in sorted({s["cause"] for s in steps}):
        s = max((s for s in steps if s["cause"] == c), key=lambda s: s["ms"])
        print(f"    {c:15s} {s['ms'] / 1000:6.1f} s  {s['entry']}: {s['text'][:70]}")


def entries(steps):
    weight = sum(s["ms"] for s in steps)
    by_entry = Counter()
    for s in steps:
        by_entry[s["entry"]] += s["ms"]
    print("  top entries by time: " + ", ".join(f"{e} {pct(t / weight).strip()}" for e, t in by_entry.most_common(6)))


def write(steps, path):
    fields = ["corpus", "entry", "file", "offset", "ms", "gc_ms", "samples", "coverage", "method", "cause", "edit",
              "text_len", "facts", "using_facts", "statement_len", "depth_chars"] + CAUSES + [SHARED, TAIL, "top", "text"]
    with open(path, "w", newline="") as f:
        w = csv.writer(f, delimiter="\t")
        w.writerow(fields)
        for s in steps:
            row = {**s, **{c: f"{s['shares'][c]:.3f}" for c in CAUSES + [SHARED, TAIL]},
                   "coverage": f"{s['coverage']:.2f}", "top": "; ".join(f"{n} {k}" for n, k in s["top"])}
            w.writerow([row[k] for k in fields])


if __name__ == "__main__":
    args = sys.argv[1:]
    output = args[args.index("-O") + 1] if "-O" in args else None
    searches, cache = read_searches(), {}
    everything = []
    for corpus in CORPORA:
        steps = steps_of(corpus, searches, cache)
        everything += steps
        print(f"\n== {corpus[0]}: {len(steps)} profiled steps")
        subsystem_shares(steps)
        distribution(steps)
        crosstab(steps, "method", "cause by method")
        crosstab([s for s in steps if s["edit"] != "not_searched"], "edit", "cause by faster_step outcome (searched steps)")
        proxy_summary(steps)
        signatures(steps)
        examples(steps)
        entries(steps)
    if output:
        write(everything, output)
