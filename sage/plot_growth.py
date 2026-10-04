"""Figure for notes/log.md: growth of T(A), T(A') in n, from the sweep CSVs.

Columns are d = 3, 4, 5. Rows:
  1. T against n on log-log axes, with a slope key (guides for T ~ n and T ~ n^2).
  2. T / n^2: it flattens at a nonzero constant for quadratic growth and falls to 0 for
     sub-quadratic growth.
  3. The exact test from analyze_growth.py: a(n) = D_P(n) / 2P^2, the lag-P second difference
     over the series' own period P. It is a constant for a quasi-quadratic T with leading
     coefficient a, and would decay like 1/n for n log n growth.
Large dots mark prime n. The recursive set exists only for n = 2^p, so it is absent from row 3.

Needs matplotlib, which the default python3 here lacks; the conda env `sage` has it:
    ~/miniforge3/envs/sage/bin/python sage/plot_growth.py [--out notes/growth-plots.png]

Colours follow the dataviz skill's reference palette: categorical slots 1-3 in fixed order
(A blue, A' orange, recursive aqua) and its light-mode ink / hairline tokens. Palette check,
light mode, --pairs all (small multiples): lightness band, chroma floor, CVD separation (worst
dE 9.2) and normal-vision floor (worst dE 24.0) PASS; contrast WARN for aqua (2.74:1 on the
surface), relieved by direct labels on every series plus the table view (the CSVs and the
tables in notes/log.md).
"""

import argparse
from fractions import Fraction
from pathlib import Path

try:
    import matplotlib
except ModuleNotFoundError:
    raise SystemExit("plot_growth.py needs matplotlib, which the default python3 lacks. "
                     "Run it with the conda env's Python:\n"
                     "    ~/miniforge3/envs/sage/bin/python sage/plot_growth.py")
matplotlib.use("Agg")                       # headless: write the PNG, never open a window
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.lines import Line2D
from matplotlib.ticker import FuncFormatter, NullFormatter, NullLocator

import analyze_growth as ag

SURFACE, INK, INK2, MUTED = "#fcfcfb", "#0b0b0b", "#52514e", "#898781"
GRID, AXIS = "#e1e0d9", "#c3c2b7"
COLOR = {"canonical": "#2a78d6", "shifted": "#eb6834", "recursive": "#1baf7a"}
NAME = {"canonical": "A", "shifted": "A'", "recursive": "recursive"}
LEGEND = {"canonical": "A (canonical)", "shifted": "A' (shifted)", "recursive": r"recursive set ($n=2^p$)"}
DS = (3, 4, 5)
LINE, MARKER, RING = 1.5, 5.4, 1.1          # pt: 2px-ish lines, >= 8px markers, 2px surface ring
OUT = Path(__file__).resolve().parent.parent / "notes" / "growth-plots.png"

plt.rcParams.update({
    "font.family": "sans-serif",
    "font.sans-serif": ["Helvetica Neue", "Helvetica", "Arial", "DejaVu Sans"],
    "mathtext.fontset": "dejavusans",
    "axes.unicode_minus": False,
})


def fraction_text(a):
    return str(a)                            # Fraction(1, 8) -> "1/8", Fraction(1) -> "1"


def local_a(T):
    """(P, exact a or None, x, y): a(n) = D_P(n) / 2P^2 centred at n + P, P = the series' period."""
    found = ag.find_quasi_quadratic(T)
    P = found[0] if found else 6             # no exact period found (d = 5, A'): show the P = 6 estimate
    D = ag.lag_second_differences(T, P)
    ns = sorted(D)
    return P, (found[2] if found else None), np.array([n + P for n in ns]), np.array([D[n] / (2 * P * P) for n in ns])


def style(ax):
    ax.set_facecolor(SURFACE)
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    for side in ("left", "bottom"):
        ax.spines[side].set_color(AXIS)
        ax.spines[side].set_linewidth(0.8)
    ax.tick_params(colors=INK2, labelsize=8.5, length=3, width=0.8, color=AXIS)
    ax.yaxis.grid(True, color=GRID, linewidth=0.8)
    ax.set_axisbelow(True)


def line(ax, x, y, key, dots=None):
    """2px series line; `dots` = x values that get a ringed marker (prime n, or every point)."""
    ax.plot(x, y, color=COLOR[key], lw=LINE, solid_capstyle="round", solid_joinstyle="round", zorder=3)
    if dots is not None and len(dots):
        ax.plot(dots[0], dots[1], "o", color=COLOR[key], ms=MARKER, mec=SURFACE, mew=RING, zorder=4)


def end_label(ax, x, y, text, dy=0):
    ax.annotate(text, xy=(x, y), xytext=(7, dy), textcoords="offset points", fontsize=8.5,
                color=INK, va="center", ha="left", annotation_clip=False, zorder=5)


def slope_key(ax):
    """Two guide lines, T ~ n and T ~ n^2, in the empty lower right of a log-log panel."""
    (x_lo, x_hi), (y_lo, y_hi) = ax.get_xlim(), ax.get_ylim()
    at = lambda lo, hi, f: float(np.exp(np.log(lo) + f * (np.log(hi) - np.log(lo))))
    x0, x1, y0 = at(x_lo, x_hi, 0.50), at(x_lo, x_hi, 0.76), at(y_lo, y_hi, 0.07)
    for slope, text in ((1, r"$\propto n$"), (2, r"$\propto n^2$")):
        y1 = y0 * (x1 / x0) ** slope
        ax.plot([x0, x1], [y0, y1], color=MUTED, lw=0.9, zorder=1)
        ax.annotate(text, xy=(x1, y1), xytext=(4, 0), textcoords="offset points", fontsize=8,
                    color=INK2, va="center")


def make_figure(series):
    fig, axes = plt.subplots(3, 3, figsize=(13.2, 10.4), sharex="col", sharey="row")
    fig.patch.set_facecolor(SURFACE)
    top = {d: max(series[(d, "canonical")]) for d in DS}
    for row in axes:
        for ax in row:
            style(ax)

    for j, d in enumerate(DS):
        n_max = top[d]
        A, Ap = series[(d, "canonical")], series[(d, "shifted")]
        rec = series.get((d, "recursive"), {})
        for key, T in (("canonical", A), ("shifted", Ap)):
            ns = sorted(T)
            primes = [n for n in ns if ag.is_prime(n)]
            # row 1: T vs n;  row 2: T / n^2
            line(axes[0][j], ns, [T[n] for n in ns], key, (primes, [T[n] for n in primes]))
            line(axes[1][j], ns, [T[n] / n ** 2 for n in ns], key, (primes, [T[n] / n ** 2 for n in primes]))
            P, a, x, y = local_a(T)
            line(axes[2][j], x, y, key)
            if a is not None:                # exact leading coefficient: a dashed limit in row 2, ending at the data
                axes[1][j].plot([2.7, n_max], [float(a)] * 2, color=COLOR[key], lw=0.9, ls=(0, (4, 3)), zorder=2)
            est = f"{np.mean(y[-8:]):.2f}"
            end_label(axes[2][j], x[-1], y[-1], f"{NAME[key]}  a = {fraction_text(a)}" if a is not None
                      else f"{NAME[key]}  a ≈ {est}")
            end_label(axes[1][j], n_max, T[n_max] / n_max ** 2,
                      NAME[key] + (r" $\rightarrow$ " + fraction_text(a) if a is not None else r" $\rightarrow\approx$" + est))
            if abs(np.log(A[n_max] / Ap[n_max])) > 0.25:      # converging lines: legend only, never nudged labels
                end_label(axes[0][j], n_max, T[n_max], NAME[key])
        if rec:
            rn = sorted(rec)
            dots_row1 = (rn, [rec[n] for n in rn])
            line(axes[0][j], rn, [rec[n] for n in rn], "recursive", dots_row1)
            line(axes[1][j], rn, [rec[n] / n ** 2 for n in rn], "recursive", (rn, [rec[n] / n ** 2 for n in rn]))
            end_label(axes[0][j], rn[-1], rec[rn[-1]], "recursive")
            end_label(axes[1][j], rn[-1], rec[rn[-1]] / rn[-1] ** 2, "recursive")

        # row 3 reference: what n log n growth would look like (a(n) ~ 1/n), scaled to meet A' at the left
        found = ag.find_quasi_quadratic(Ap)
        P, a, x, y = local_a(Ap)
        x0 = found[1] + P if found else x[0]                  # first point on the stable plateau
        y0 = float(a) if a is not None else float(np.mean(y[-8:]))
        xs = np.linspace(x0, n_max * 1.5, 80)
        axes[2][j].plot(xs, y0 * x0 / xs, color=MUTED, lw=0.9, ls=(0, (4, 3)), zorder=2)

        axes[0][j].set_title(f"d = {d}", loc="left", fontsize=11.5, color=INK, fontweight="bold", pad=8)

    # axes: log-log row 1, semilog-x rows 2 and 3; shared x per column, shared y per row
    axes[0][0].set_yscale("log")
    for j, d in enumerate(DS):
        axes[0][j].set_xscale("log")
        axes[0][j].set_xlim(2.7, top[d] * 1.9)               # room on the right for the end labels
        ticks = [t for t in (3, 5, 10, 20, 40, 80) if t <= top[d]]
        axes[2][j].set_xticks(ticks)
        axes[2][j].set_xticklabels([str(t) for t in ticks])
        axes[2][j].xaxis.set_minor_locator(NullLocator())
        axes[2][j].xaxis.set_minor_formatter(NullFormatter())
        axes[2][j].set_xlabel("n", color=INK2, fontsize=9.5)
    axes[0][0].set_ylim(2, 9000)
    axes[0][0].yaxis.set_major_formatter(FuncFormatter(lambda v, _: f"{int(v):,}"))
    axes[0][0].yaxis.set_minor_locator(NullLocator())
    axes[1][0].set_ylim(0, 1.1)
    axes[2][0].set_ylim(0, 1.1)
    for ax in axes[0]:
        slope_key(ax)
    axes[0][0].set_ylabel("T  (rounds)", color=INK2, fontsize=9.5)
    axes[1][0].set_ylabel(r"$T\,/\,n^2$", color=INK2, fontsize=10)
    axes[2][0].set_ylabel(r"$a(n)=D_P(n)\,/\,2P^2$", color=INK2, fontsize=10)

    handles = [Line2D([0], [0], color=COLOR[k], lw=LINE, marker="o" if k == "recursive" else None,
                      ms=MARKER, mec=SURFACE, mew=RING, label=LEGEND[k]) for k in ("canonical", "shifted", "recursive")]
    handles.append(Line2D([0], [0], color=INK2, lw=0, marker="o", ms=MARKER, mec=SURFACE, label="prime n"))
    handles.append(Line2D([0], [0], color=MUTED, lw=0.9, ls=(0, (4, 3)), label=r"$n\,\log\,n$ growth would look like this (row 3)"))
    fig.legend(handles=handles, loc="upper left", bbox_to_anchor=(0.062, 0.918), ncol=5, frameon=False,
               fontsize=9.5, labelcolor=INK, handlelength=2.2, columnspacing=1.8)
    fig.text(0.062, 0.972, "Percolation time of A and A' grows like n², primes included; only the recursive set (n a power of 2) is linear",
             fontsize=13.5, fontweight="bold", color=INK, ha="left", va="center")
    fig.text(0.062, 0.945, "Row 1: T on log-log axes.   Row 2: T/n² (levels off = quadratic, keeps falling to 0 = sub-quadratic).   "
             "Row 3: a(n) = second difference of T over 2P² (flat = exactly quadratic).",
             fontsize=9.5, color=INK2, ha="left", va="center")
    fig.text(0.062, 0.010, "Data: notes/sweep-results.csv + notes/sweep-results-extended.csv (d=3 n<=80, d=4 n<=40, d=5 n<=24). "
             "Dashed in row 2: exact limit a. Row 3: each series' own period P; A' at d=5 has no exact period by n=24 (P=6, estimate).",
             fontsize=8, color=MUTED, ha="left", va="center")
    fig.subplots_adjust(left=0.062, right=0.99, top=0.865, bottom=0.075, wspace=0.05, hspace=0.10)
    return fig


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--out", type=Path, default=OUT)
    parser.add_argument("--dpi", type=int, default=150)
    args = parser.parse_args()
    series = ag.load([p for p in ag.DEFAULT_CSVS if p.exists()])
    fig = make_figure(series)
    fig.savefig(args.out, dpi=args.dpi, facecolor=SURFACE)
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
