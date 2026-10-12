#!/usr/bin/env python3
"""Make this machine quiet enough for timing runs, or undo it. Needs root.

Usage: sudo python3 scripts/timing_box.py [--undo]

Stops the k3s agent and kills its pods (stopping the agent alone leaves them running), sets
every core's governor to performance and turns boost off, so a step's time does not depend on
heat or on what else runs. --undo puts it all back.
"""

import subprocess
import sys
from pathlib import Path

CPUS = Path("/sys/devices/system/cpu")
BOOST = CPUS / "cpufreq/boost"
SERVICE = "k3s-agent"
KILLALL = "/usr/local/bin/k3s-killall.sh"


def write_all(name, value):
    for f in sorted(CPUS.glob(f"cpu[0-9]*/cpufreq/{name}")):
        try:
            f.write_text(value)
        except OSError:
            # amd-pstate-epp refuses a preference while the performance governor is set
            pass


def setup():
    subprocess.run(["systemctl", "stop", SERVICE], check=False)
    subprocess.run([KILLALL], check=False, stdout=subprocess.DEVNULL)
    write_all("scaling_governor", "performance")
    write_all("energy_performance_preference", "performance")
    BOOST.write_text("0")


def undo():
    BOOST.write_text("1")
    write_all("scaling_governor", "powersave")
    write_all("energy_performance_preference", "balance_performance")
    subprocess.run(["systemctl", "start", SERVICE], check=False)


def show():
    cpu0 = CPUS / "cpu0/cpufreq"
    agent = subprocess.run(["systemctl", "is-active", SERVICE], capture_output=True, text=True)
    print("governor", (cpu0 / "scaling_governor").read_text().strip())
    print("boost", BOOST.read_text().strip())
    print(SERVICE, agent.stdout.strip())


if __name__ == "__main__":
    undo() if "--undo" in sys.argv else setup()
    show()
