#!/usr/bin/env python3
"""The timing PC's work queue, run in a daytime window (cron: start 08:30, stop 23:00).

Usage: scripts/pc_queue.py start | stop       (from the repo root; finished stages are skipped)
Stages: DSP faster_step at 0.1 s, then faster_step on the AFP entries in scripts/faster_entries.txt
(most slow-step time first; lint_afp.py resumes per entry and session).
Log: census/pc_queue.log, stages done: census/pc_queue.done
"""

import os
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

REPO = Path.home() / "dev/isabelle_linter"
DSP = Path.home() / "dev/audit_dsp"
LOG = REPO / "census/pc_queue.log"
DONE = REPO / "census/pc_queue.done"
PID = REPO / "census/pc_queue.pid"
PIN = ["taskset", "-c", "2-7"]
THREADS = ["-o", "threads=6"]


def log(text):
    with open(LOG, "a") as f:
        f.write(time.strftime("%Y-%m-%d %H:%M ") + text + "\n")


def done(name):
    return name in DONE.read_text().split("\n")


# a stage cut short by stop is not marked done, so the next start runs it again
def stage(name, command, out):
    if done(name):
        return
    log("start " + name)
    with open(out, "a") as f:
        rc = subprocess.run(command, cwd=REPO, stdout=f, stderr=subprocess.STDOUT).returncode
    log(f"end {name}: return code {rc}")
    with open(DONE, "a") as f:
        f.write(name + "\n")


def dsp(name, lint, options):
    out = REPO / "census/dsp" / name
    if not done(f"dsp {name}"):
        shutil.rmtree(out, ignore_errors=True)
        shutil.copytree(DSP, out)
    question_log = ["-o", f"linter_log={out}/questions.tsv"]
    stage(f"dsp {name}", PIN + ["isabelle", "linter", "-l", lint, "-F", *THREADS, *options, *question_log,
                                "-d", str(out), "Audit_DSP"], out / "lint.log")
    stage(f"dsp {name} build", PIN + ["isabelle", "build", "-d", str(out), "-o", "document=false",
                                      *THREADS, "Audit_DSP"], out / "build.log")


def queue():
    dsp("faster_step_01", "faster_step", ["-o", "faster_step_slow=0.1"])
    entries = (REPO / "scripts/faster_entries.txt").read_text().split()
    options = ["-o", "faster_step_slow=3", "-o", "linter_timeout=300", *THREADS]
    stage("faster afp", PIN + ["python3", "scripts/lint_afp.py", "faster_step", *options, *entries],
          REPO / "census/faster_step/afp.out")
    log("queue done")


def running():
    return PID.exists() and Path(f"/proc/{PID.read_text().strip()}").exists()


def start():
    if running():
        return
    PID.write_text(str(os.getpid()))
    os.environ["PATH"] = str(Path.home() / "opt/isabelle/Isabelle2025-2/bin") + ":" + os.environ["PATH"]
    DONE.touch()
    queue()


# kills the whole queue, including the Isabelle processes it started
def stop():
    if not running():
        return
    log("stopped")
    os.killpg(os.getpgid(int(PID.read_text())), signal.SIGTERM)
    time.sleep(10)
    subprocess.run(["pkill", "-u", os.environ.get("USER", "marcos"), "-f", "^" + str(Path.home() / "opt/isabelle")])


if __name__ == "__main__":
    os.chdir(REPO)
    {"start": start, "stop": stop}[sys.argv[1]]()
