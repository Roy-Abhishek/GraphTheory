"""Figure for notes/log.md (2026-10-04): the best percolation times found, against n, d = 3.

Series: the lower bound floor(3(n-1)/2); the best minimum percolating set found (notes/best-sets-d3.json);
the best residue class {sum(v) = c mod n} (scanned over all c); and A' (the shifted class from the paper).
Filled dots are exact (the best set meets the lower bound, so it is the optimum); open dots are open.

Needs matplotlib (conda env `sage`):  ~/miniforge3/envs/sage/bin/python sage/plot_best.py
Colours and chart tokens as in plot_growth.py (the dataviz skill's reference palette).
"""

import argparse
import json
from pathlib import Path

import minperc as mp
import sweep
from plot_growth import AXIS, COLOR, GRID, INK, INK2, MUTED, SURFACE, plt

NOTES = Path(__file__).resolve().parent.parent / "notes"


def class_times(n):
    """T of every residue class {sum(v) = c mod n}, c = 0..n-1 (all of them percolate)."""
    S = sweep.coordinate_sums(n, 3)
    return [mp.percolates(S % n == c)[1] for c in range(n)]


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--out", type=Path, default=NOTES / "best-T-vs-n.png")
    args = parser.parse_args()
    best = {row["n"]: row["T"] for row in json.loads((NOTES / "best-sets-d3.json").read_text())}
    ns = list(range(3, 14))
    lower = [3 * (n - 1) // 2 for n in ns]
    residue = [min(class_times(n)) for n in ns]
    shifted = [mp.percolates(sweep.shifted(n, 3))[1] for n in ns]

    fig, ax = plt.subplots(figsize=(9.6, 5.6))
    fig.patch.set_facecolor(SURFACE)
    ax.set_facecolor(SURFACE)
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    for side in ("left", "bottom"):
        ax.spines[side].set_color(AXIS)
    ax.tick_params(colors=INK2, labelsize=9.5, length=3, color=AXIS)
    ax.yaxis.grid(True, color=GRID, linewidth=0.8)
    ax.set_axisbelow(True)

    ax.plot(ns, shifted, color=COLOR["shifted"], lw=1.5, marker="o", ms=4, mec=SURFACE, mew=1.0, zorder=3)
    ax.plot(ns, residue, color=COLOR["canonical"], lw=1.5, marker="o", ms=4, mec=SURFACE, mew=1.0, zorder=3)
    ax.plot(ns, lower, color=MUTED, lw=1.0, ls=(0, (4, 3)), zorder=2)
    bn = sorted(best)
    for n0, n1 in zip(bn, bn[1:]):                      # join only consecutive n: no line across n with no stored set
        if n1 == n0 + 1:
            ax.plot([n0, n1], [best[n0], best[n1]], color=COLOR["recursive"], lw=1.8, zorder=4)
    for n in bn:
        exact = best[n] == 3 * (n - 1) // 2
        ax.plot([n], [best[n]], "o", ms=7.5, color=COLOR["recursive"], mfc=COLOR["recursive"] if exact else SURFACE,
                mec=COLOR["recursive"], mew=1.8, zorder=5)

    def label(y, text, dy=0):
        ax.annotate(text, xy=(13, y), xytext=(8, dy), textcoords="offset points", fontsize=9.5, color=INK, va="center",
                    annotation_clip=False)

    label(shifted[-1], "A' (shifted class)")
    label(residue[-1], "best residue class")
    label(best[13], "best set found", dy=-9)
    label(lower[-1], "lower bound 3(n-1)/2 (dashed)", dy=9)
    ax.set_xlim(2.7, 13.2)
    ax.set_ylim(0, 45)
    ax.set_xticks(ns)
    ax.set_xlabel("n", color=INK2, fontsize=10)
    ax.set_ylabel("percolation time T (rounds)", color=INK2, fontsize=10)
    fig.text(0.04, 0.965, "Best sets stay within 2 of the linear lower bound for n <= 13; residue-class sets grow quadratically",
             fontsize=13.5, fontweight="bold", color=INK, ha="left", va="center")
    fig.text(0.04, 0.925, "Filled dots: the best set found meets the lower bound, so it is optimal (n = 3-7, 13). "
             "Open dots: open, between the bound and the dot (n = 9, 11).", fontsize=9.5, color=INK2, ha="left", va="center")
    fig.text(0.04, 0.02, "Data: notes/best-sets-d3.json (verified sets); residue classes and A' simulated here. n = 8, 10, 12 omitted: "
             "no best set stored.", fontsize=8, color=MUTED, ha="left", va="center")
    fig.subplots_adjust(left=0.08, right=0.80, top=0.88, bottom=0.12)
    fig.savefig(args.out, dpi=150, facecolor=SURFACE)
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
