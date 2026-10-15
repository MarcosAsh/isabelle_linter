#!/usr/bin/env python3
"""Everything the laptop was going to do, on the timing PC, one stage after another.

Usage: scripts/pc_queue.py        (run detached from the repo root; finished stages are skipped)
Stages: census of the built AFP, unused on 20 entries, CAVA redo, DSP unused and faster_step,
profiles of 200 steps from the 1-5 s band. Log: census/pc_queue.log, stages done: census/pc_queue.done
"""

import os
import shutil
import subprocess
import time
from pathlib import Path

REPO = Path.home() / "dev/isabelle_linter"
AFP = Path.home() / "dev/etc/afp/afp-2026-10-01/thys"
DSP = Path.home() / "dev/audit_dsp"
LOG = REPO / "census/pc_queue.log"
DONE = REPO / "census/pc_queue.done"
PIN = ["taskset", "-c", "2-7"]
THREADS = ["-o", "threads=6"]


def log(text):
    with open(LOG, "a") as f:
        f.write(time.strftime("%Y-%m-%d %H:%M ") + text + "\n")


def stage(name, command, out):
    if name in DONE.read_text().split("\n"):
        return
    log("start " + name)
    with open(out, "w") as f:
        rc = subprocess.run(command, cwd=REPO, stdout=f, stderr=subprocess.STDOUT).returncode
    log(f"end {name}: return code {rc}")
    with open(DONE, "a") as f:
        f.write(name + "\n")


def redo_cava():
    logs, old = REPO / "census/unused/logs", REPO / "census/old/unused_cava_schematic"
    old.mkdir(parents=True, exist_ok=True)
    for name in ["CAVA_LTL_Modelchecker.build", "SM_Base_Patched", "SM_Patched", "CAVA_Setup_Patched",
                 "CAVA_LTL_Modelchecker_Patched"]:
        for p in logs.glob(name + "*"):
            shutil.move(str(p), old / p.name)
    shutil.rmtree(REPO / "census/unused/CAVA_LTL_Modelchecker", ignore_errors=True)


def dsp(lint, options):
    out = REPO / "census/dsp" / lint
    shutil.rmtree(out, ignore_errors=True)
    shutil.copytree(DSP, out)
    question_log = ["-o", f"linter_log={out}/questions.tsv"]
    stage(f"dsp {lint}", PIN + ["isabelle", "linter", "-l", lint, "-F", *THREADS, *options, *question_log,
                                "-d", str(out), "Audit_DSP"], out / "lint.log")
    stage(f"dsp {lint} build", PIN + ["isabelle", "build", "-d", str(out), "-o", "document=false",
                                      *THREADS, "Audit_DSP"], out / "build.log")


if __name__ == "__main__":
    os.environ["PATH"] = str(Path.home() / "opt/isabelle/Isabelle2025-2/bin") + ":" + os.environ["PATH"]
    DONE.touch()
    subprocess.run(["git", "pull", "-q", "--ff-only"], cwd=REPO)
    stage("census", ["isabelle", "linter_census", "-D", str(AFP), "-O", "census/timings_afp.tsv"],
          REPO / "census/census_afp.out")
    stage("unused", PIN + ["python3", "scripts/lint_afp.py", "unused", *THREADS, "-n", "20"],
          REPO / "census/unused/pc.out")
    if "cava" not in DONE.read_text().split("\n"):
        redo_cava()
    stage("cava", PIN + ["python3", "scripts/lint_afp.py", "unused", *THREADS, "CAVA_LTL_Modelchecker"],
          REPO / "census/unused/cava.out")
    dsp("unused", [])
    dsp("faster_step", ["-o", "faster_step_slow=0.5"])
    stage("band", PIN + ["isabelle", "linter_retime", "-d", str(AFP), *THREADS, "-I", "census/band_1_5.tsv",
                         "-n", "200", "-O", "census/retime_band.tsv", "-P", "census/profiles_band.tsv"],
          REPO / "census/retime_band.log")
    log("queue done")
