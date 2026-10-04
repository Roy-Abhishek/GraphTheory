"""Figure for notes/log.md (2026-10-04): the explicit family T = 3(n-1)/2 (n = 2^k - 3) against the paper's residue-class sets.

Data: notes/family-comparison.csv, written by `python3 sage/gadget.py table 5 13 29 61 125 253 --out notes/family-comparison.csv`
(columns n, lower_bound, family, shifted, canonical, best_class; blank where the simulation was skipped as too slow).

Left: T against n on log-log axes. Right: T / n², which levels off for quadratic growth and falls like 1/n for linear.
Series: the family (aqua, the colour used for "our sets" in best-T-vs-n.png), the best residue class {sum(v) = c mod n}
(blue) and the shifted set A' of the paper (orange); the dashed line is the lower bound 3(n-1)/2, which the family meets.

Needs matplotlib (conda env `sage`):  ~/miniforge3/envs/sage/bin/python sage/plot_family.py
Colours and chart tokens as in plot_growth.py (the dataviz skill's reference palette: categorical slots 1-3 in fixed order,
validated all-pairs; aqua has 2.74:1 contrast on the surface, relieved by the direct labels and the CSV as table view).
"""

import argparse
import csv
from pathlib import Path

import numpy as np
from matplotlib.ticker import FuncFormatter, NullFormatter

from plot_growth import AXIS, COLOR, GRID, INK, INK2, MUTED, SURFACE, plt

NOTES = Path(__file__).resolve().parent.parent / "notes"
SERIES = [  # (csv column, colour, direct label)
    ("shifted", COLOR["shifted"], "A' (shifted class)"),
    ("best_class", COLOR["canonical"], "best residue class"),
    ("family", COLOR["recursive"], "explicit family, T = 3(n-1)/2"),
]


def read(path):
    rows = list(csv.DictReader(path.open()))
    return {col: [(int(r["n"]), int(r[col])) for r in rows if r[col] != ""] for col in
            ("lower_bound", "family", "shifted", "canonical", "best_class")}


def style(ax):
    ax.set_facecolor(SURFACE)
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    for side in ("left", "bottom"):
        ax.spines[side].set_color(AXIS)
    ax.tick_params(colors=INK2, labelsize=9.5, length=3, color=AXIS, which="both")
    ax.grid(True, which="major", color=GRID, linewidth=0.8)
    ax.set_axisbelow(True)
    ax.set_xscale("log")
    ax.xaxis.set_major_formatter(FuncFormatter(lambda x, _: f"{x:g}"))
    ax.xaxis.set_minor_formatter(NullFormatter())


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--csv", type=Path, default=NOTES / "family-comparison.csv")
    parser.add_argument("--out", type=Path, default=NOTES / "family-T-vs-n.png")
    args = parser.parse_args()
    data = read(args.csv)
    ns = [n for n, _ in data["family"]]

    fig, (left, right) = plt.subplots(1, 2, figsize=(11.6, 5.4))
    fig.patch.set_facecolor(SURFACE)
    for ax in (left, right):
        style(ax)
    grid_n = np.geomspace(3, 300, 100)

    for col, color, _ in SERIES:
        pts = data[col]
        for ax, y in ((left, lambda n, t: t), (right, lambda n, t: t / n ** 2)):
            ax.plot([n for n, _ in pts], [y(n, t) for n, t in pts], color=color, lw=1.8, marker="o", ms=6.5,
                    mec=SURFACE, mew=1.1, zorder=4)
    left.plot(grid_n, 1.5 * (grid_n - 1), color=MUTED, lw=1.0, ls=(0, (4, 3)), zorder=2)
    right.plot(grid_n, 1.5 * (grid_n - 1) / grid_n ** 2, color=MUTED, lw=1.0, ls=(0, (4, 3)), zorder=2)

    left.set_yscale("log")
    right.set_yscale("log")
    left.set_xlim(4, 330)
    right.set_xlim(4, 330)
    left.set_ylim(4, 12000)
    right.set_ylim(0.004, 0.5)
    left.set_xticks(ns)
    right.set_xticks(ns)
    left.yaxis.set_major_formatter(FuncFormatter(lambda y, _: f"{y:g}"))
    right.yaxis.set_major_formatter(FuncFormatter(lambda y, _: f"{y:g}"))
    left.set_xlabel(r"n  (the family has $n = 2^k - 3$)", color=INK2, fontsize=10)
    right.set_xlabel("n", color=INK2, fontsize=10)
    left.set_ylabel("percolation time T (rounds)", color=INK2, fontsize=10)
    right.set_ylabel("T / n²", color=INK2, fontsize=10)

    def label(ax, x, y, text, dx=8, dy=0, ha="left"):
        ax.annotate(text, xy=(x, y), xytext=(dx, dy), textcoords="offset points", fontsize=9.5, color=INK, va="center",
                    ha=ha, annotation_clip=False)

    sh, bc, fam = data["shifted"][-1], data["best_class"][-1], data["family"][-1]       # last n of each series
    label(left, *sh, "A' (shifted class)", dy=8)
    label(left, bc[0], bc[1], "best residue class", dx=-6, dy=16, ha="right")
    label(left, *data["family"][-2], "explicit family\nT = 3(n-1)/2", dx=10, dy=-20)
    label(right, sh[0], sh[1] / sh[0] ** 2, "A'", dy=9)
    label(right, bc[0], bc[1] / bc[0] ** 2, "best residue class", dx=10, dy=-20)
    label(right, fam[0], fam[1] / fam[0] ** 2, "explicit family: 1.5/n", dx=-12, dy=-12, ha="right")

    fig.text(0.04, 0.955, "Explicit sets with T = 1.5(n-1) at n = 5, 13, 29, 61, 125, 253; the paper's residue-class sets grow like n²",
             fontsize=13, fontweight="bold", color=INK, ha="left", va="center")
    fig.text(0.04, 0.915, "Dashed: lower bound 3(n-1)/2, which the family meets exactly (so these are optimal). T / n² levels off near "
             "1/8 for the residue-class sets and falls like 1/n for the family.", fontsize=9.5, color=INK2, ha="left", va="center")
    fig.text(0.04, 0.02, "Data: notes/family-comparison.csv (exact simulation). Best residue class only up to n = 61 and A' up to n = 125: "
             "larger runs skipped as too slow.", fontsize=8, color=MUTED, ha="left", va="center")
    fig.subplots_adjust(left=0.07, right=0.97, top=0.86, bottom=0.14, wspace=0.26)
    fig.savefig(args.out, dpi=150, facecolor=SURFACE)
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
