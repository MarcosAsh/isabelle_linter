#!/usr/bin/env python3
"""The timing PC's work queue, run in a daytime window (cron: start 08:30, stop 23:00).

Usage: scripts/pc_queue.py start | stop       (from the repo root; finished stages are skipped)
Stages: re-times with boost off (the full-AFP plan census/retime_full.tsv, the 21-entry winners
before and after), then faster_step with boost on over scripts/faster_entries.txt (most slow-step
time first; lint_afp.py and linter_retime resume). Boost is set with `sudo -n tee` (sudoers rule).
Boost-off stages are skipped while boost cannot be set. A stage whose log stops growing for STALL
seconds is killed and resumed, at most 3 times.
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
AFP = Path.home() / "dev/etc/afp/afp-2026-10-01/thys"
BOOST = Path("/sys/devices/system/cpu/cpufreq/boost")
STALL = 3600
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


def boost(on):
    value = "1" if on else "0"
    if BOOST.read_text().strip() != value:
        subprocess.run(["sudo", "-n", "tee", str(BOOST)], input=value, text=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return BOOST.read_text().strip() == value


# the newest change to a log file, or to any file in a log directory
def last_change(watch):
    files = list(watch.iterdir()) if watch.is_dir() else [watch]
    return max((f.stat().st_mtime for f in files if f.exists()), default=time.time())


# runs until done; True if it stalled and was killed
def watched(command, out, watch, stall):
    with open(out, "a") as f:
        proc = subprocess.Popen(command, cwd=REPO, stdout=f, stderr=subprocess.STDOUT)
        while proc.poll() is None:
            time.sleep(60)
            if time.time() - last_change(watch) > stall:
                proc.kill()
                subprocess.run(["pkill", "-f", "^" + str(Path.home() / "opt/isabelle")])
                proc.wait()
                return True
    return False


# a stage cut short by stop is not marked done, so the next start runs it again
def stage(name, command, out, boost_on=True, watch=None, stall=STALL):
    if done(name):
        return
    if not boost(boost_on):
        log(f"skip {name}: cannot set boost")
        return
    log("start " + name)
    for attempt in range(3):
        if not watched(command, out, watch or out, stall):
            break
        log(f"stalled {name}, restarting")
    log("end " + name)
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


def retime(name, rows, out, options=(), dirs=()):
    command = PIN + ["isabelle", "linter_retime", "-d", str(AFP), *dirs, *THREADS, *options, "-I", rows,
                     "-n", "100000", "-O", f"census/{out}.tsv"]
    stage(name, command, REPO / f"census/{out}.log", boost_on=False)


# the copies the 21-entry faster_step run patched
def patched_dirs():
    rows = (REPO / "census/winners_21_retime_patched.tsv").read_text().splitlines()[1:]
    entries = sorted({row.split("\t")[1].split("/faster_step/")[1].split("/")[0] for row in rows})
    return [arg for e in entries for arg in ("-d", f"census/faster_step/{e}")]


def queue():
    dsp("faster_step_01", "faster_step", ["-o", "faster_step_slow=0.1"])
    retime("retime full", "census/retime_full.tsv", "retime_full_out", ["-o", "retime_runs=1"])
    retime("winners before", "census/winners_21_retime.tsv", "winners_before")
    retime("winners after", "census/winners_21_retime_patched.tsv", "winners_after", dirs=patched_dirs())
    entries = (REPO / "scripts/faster_entries.txt").read_text().split()
    options = ["-o", "faster_step_slow=3", "-o", "linter_timeout=300", *THREADS]
    stage("faster afp", PIN + ["python3", "scripts/lint_afp.py", "faster_step", *options, *entries],
          REPO / "census/faster_step/afp.out", watch=REPO / "census/faster_step/logs", stall=2 * STALL)
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
