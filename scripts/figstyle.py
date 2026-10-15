"""Shared look for the paper figures: palette, axes, saving as PDF and PNG.

Import from a figure script in scripts/: `from figstyle import *`.
"""

from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

# categorical slots in fixed order; scatters use at most the first three
BLUE = "#2a78d6"
ORANGE = "#eb6834"
AQUA = "#1baf7a"
SERIES = [BLUE, ORANGE, AQUA]

INK = "#0b0b0b"
MUTED = "#52514e"
GRID = "#e4e3df"
OUT = Path(__file__).parent.parent / "census/figures"

plt.rcParams.update({
    "font.size": 9,
    "axes.titlesize": 10,
    "axes.labelsize": 9,
    "axes.labelcolor": MUTED,
    "axes.edgecolor": MUTED,
    "xtick.color": MUTED,
    "ytick.color": MUTED,
    "legend.frameon": False,
    "figure.facecolor": "white",
    "savefig.facecolor": "white",
    "pdf.fonttype": 42,
})


def style(ax, title=None, grid="y"):
    if title:
        ax.set_title(title, loc="left", color=INK)
    if grid:
        ax.grid(axis=grid, color=GRID, linewidth=0.8)
    ax.set_axisbelow(True)
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)


def note(ax, text, x=0.99, y=0.97, ha="right"):
    ax.text(x, y, text, transform=ax.transAxes, ha=ha, va="top", color=MUTED, fontsize=8,
            bbox=dict(facecolor="white", edgecolor="none", pad=1))


# PDF for LaTeX, PNG to look at
def save(fig, name):
    OUT.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(OUT / f"{name}.pdf")
    fig.savefig(OUT / f"{name}.png", dpi=200)
    plt.close(fig)
    print("wrote", OUT / f"{name}.png")
