#!/usr/bin/env python3
"""Run out the prover's heap on purpose and check that the linter says so.

Usage: scripts/oom_probe.py [--maxheap 1500M] [--lemmas 16] [--size 20000000] [--threads 8]

Each lemma allocates a list of SIZE ints in its proof. Loading the theory runs them one at a time,
but the linter's first round runs them all at once, under a prover heap capped with --maxheap.
The linter of this checkout runs in an isolated USER_HOME (shared heaps, heap cap in its
etc/settings, since the ML_OPTIONS environment variable is overridden), so the main checkout's jar
is not rebuilt. Expect "prover: Run out of store" and then either "interrupted" answers and a
"questions unanswered" warning with the heap, or "prover exited" and "Prover died".
"""

import argparse
import os
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ISABELLE_USER = Path.home() / ".isabelle" / "Isabelle2025-2"


def theory(lemmas, size):
    proof = (f"by (tactic \\<open>fn st => if length (List.tabulate ({size}, I)) = {size} "
             "then resolve_tac \\<^context> @{thms TrueI} 1 st else no_tac st\\<close>)")
    body = "\n\n".join(f"lemma hog{i}: \"True\"\n  using TrueI conjI\n  {proof}" for i in range(lemmas))
    return f"theory Oom_Probe\n  imports Main\nbegin\n\n{body}\n\nend\n"


# a USER_HOME whose components list only this checkout, with the real heaps and a capped ML heap
def isolated_home(tmp, maxheap):
    user = tmp / "home" / ".isabelle" / "Isabelle2025-2"
    (user / "etc").mkdir(parents=True)
    (user / "etc" / "components").write_text(f"{ROOT}\n")
    (user / "etc" / "settings").write_text(f'ML_OPTIONS="--minheap 500 --maxheap {maxheap}"\n')
    (user / "heaps").symlink_to(ISABELLE_USER / "heaps")
    return tmp / "home"


def run(args):
    tmp = Path(tempfile.mkdtemp(prefix="oom_probe_"))
    (tmp / "session").mkdir()
    (tmp / "session" / "ROOT").write_text("session Oom_Probe = HOL +\n  theories Oom_Probe\n")
    (tmp / "session" / "Oom_Probe.thy").write_text(theory(args.lemmas, args.size))

    env = dict(os.environ, USER_HOME=str(isolated_home(tmp, args.maxheap)))
    log = tmp / "linter.log"
    command = ["isabelle", "linter", "-l", "unused", "-o", f"threads={args.threads}",
               "-o", f"linter_log={tmp / 'questions.tsv'}", "-d", str(tmp / "session"), "Oom_Probe"]
    with log.open("w") as out:
        rc = subprocess.run(command, env=env, stdout=out, stderr=subprocess.STDOUT).returncode
    return tmp, log, rc


def report(tmp, log, rc):
    text = log.read_text()
    print("linter exit code", rc, "- log", log)
    for label, pattern in (("out of store", r"Run out of store"), ("failed to recover", r"Failed to recover"),
                           ("prover exited", r"prover exited"), ("prover died", r"Prover died"),
                           ("unanswered", r"questions unanswered.*")):
        found = re.findall(pattern, text)
        print(f"{label}: {len(found)}", found[-1] if found and label == "unanswered" else "")
    tsv = tmp / "questions.tsv"
    if tsv.exists():
        verdicts = [line.split("\t")[4] for line in tsv.read_text().splitlines()]
        print("verdicts:", {v: verdicts.count(v) for v in sorted(set(verdicts))})


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--maxheap", default="1500M")
    parser.add_argument("--lemmas", type=int, default=16)
    parser.add_argument("--size", type=int, default=20_000_000)
    parser.add_argument("--threads", type=int, default=8)
    report(*run(parser.parse_args()))
