#!/usr/bin/env python3
"""Quiet the timing machine: stop k3s and its pods, performance governor, boost off. Needs root.

Usage: sudo python3 scripts/timing_box.py [--boost] [--undo]
  --boost  keep boost on (faster, possibly noisier)
"""

import subprocess
import sys
from pathlib import Path

CPUS = Path("/sys/devices/system/cpu")
BOOST = CPUS / "cpufreq/boost"


def write_all(name, value):
    for f in CPUS.glob(f"cpu[0-9]*/cpufreq/{name}"):
        try:
            f.write_text(value)
        except OSError:
            pass  # amd-pstate-epp refuses a preference under the performance governor


def setup(boost):
    subprocess.run(["systemctl", "stop", "k3s-agent"])
    if Path("/usr/local/bin/k3s-killall.sh").exists():
        subprocess.run(["/usr/local/bin/k3s-killall.sh"], stdout=subprocess.DEVNULL)
    write_all("scaling_governor", "performance")
    write_all("energy_performance_preference", "performance")
    BOOST.write_text("1" if boost else "0")


def undo():
    BOOST.write_text("1")
    write_all("scaling_governor", "powersave")
    write_all("energy_performance_preference", "balance_performance")
    subprocess.run(["systemctl", "start", "k3s-agent"])


if __name__ == "__main__":
    undo() if "--undo" in sys.argv else setup("--boost" in sys.argv)
    print("governor", (CPUS / "cpu0/cpufreq/scaling_governor").read_text().strip(),
          "boost", BOOST.read_text().strip())
