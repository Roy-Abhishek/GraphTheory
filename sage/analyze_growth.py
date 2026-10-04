"""Growth of T(A) (canonical) and T(A') (shifted) in n, from the sweep CSVs.

Question: for n that are not powers of 2, primes especially, is T sub-quadratic (linear,
n log n), or Theta(n^2) like the Theorem 2 bound?

The model-free test used throughout is the lag-P second difference
    D_P(n) = T(n+2P) - 2 T(n+P) + T(n).
If T(n) = a n^2 + (terms linear in n, with coefficients that depend only on n mod P), then
D_P(n) = 2 a P^2 is exactly CONSTANT. If T grew like n log n, D_P(n) would decay like
P^2/n; if linearly, it would tend to 0. Naive power-law fits are misleading at small n
because of the large linear term (section 4 shows the apparent exponent creeping up to 2).

Exactness claims use integer/Fraction arithmetic. Fits use floats and are only evidence.

Run:  python3 sage/analyze_growth.py [csv ...]
          default: notes/sweep-results.csv (+ notes/sweep-results-extended.csv if present)
      python3 sage/analyze_growth.py --residue-classes      (adds ~100 s)
          also tries every class {sum(v) = c mod n}, n = 3..44 at d=3 (not only the shifts A, A')

The extended CSV was produced with (then merged, sorted by d, n, construction):
      python3 sage/sweep.py --dmin 3 --dmax 3 --nmin 21 --nmax 80 --out <file>
      python3 sage/sweep.py --dmin 4 --dmax 4 --nmin 21 --nmax 40 --out <file>
      python3 sage/sweep.py --dmin 5 --dmax 5 --nmin 21 --nmax 24 --out <file>
"""

import argparse
import csv
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

import numpy as np

NOTES = Path(__file__).resolve().parent.parent / "notes"
DEFAULT_CSVS = [NOTES / "sweep-results.csv", NOTES / "sweep-results-extended.csv"]


def is_prime(n):
    return n >= 2 and all(n % q for q in range(2, int(n ** 0.5) + 1))


def is_power_of_two(n):
    return n >= 2 and n & (n - 1) == 0


def load(paths):
    """(d, construction) -> {n: T}, merged over all files."""
    series = defaultdict(dict)
    for path in paths:
        for row in csv.DictReader(open(path)):
            key, n, T = (int(row["d"]), row["construction"]), int(row["n"]), int(row["time"])
            assert series[key].get(n, T) == T, f"conflicting T for {key}, n={n}"
            series[key][n] = T
    return series


# ---------------------------------------------------- exact quasi-quadratic structure

def lag_second_differences(T, P):
    """{n: T(n+2P) - 2 T(n+P) + T(n)} wherever all three values exist."""
    return {n: T[n + 2 * P] - 2 * T[n + P] + T[n] for n in sorted(T) if n + 2 * P in T}


def constant_suffix(D):
    """(first n, value, length) of the longest run of equal D values ending at the largest n."""
    ns = sorted(D)
    value = D[ns[-1]]
    run = [n for n in reversed(ns)]
    count = 0
    for n in run:
        if D[n] != value:
            break
        count += 1
    return ns[len(ns) - count], value, count


def find_quasi_quadratic(T, max_period=12, min_run=8):
    """Smallest P whose lag-P second difference is constant on a final run of >= min_run values.

    Returns (P, n0, a, run) with a = D/(2P^2) as a Fraction, or None. Then for n >= n0 and
    each residue r mod P, T is exactly a quadratic in n with leading coefficient a.
    """
    for P in range(1, max_period + 1):
        D = lag_second_differences(T, P)
        if len(D) < min_run:
            break
        n0, value, run = constant_suffix(D)
        if run >= min_run:
            return P, n0, Fraction(value, 2 * P * P), run
    return None


def class_polynomials(T, P, n0, a):
    """r -> (b, c, points, exceptions): T(n) = a n^2 + b n + c for n >= n0, n = r mod P.

    b, c come from the first two points of the class; every point is then checked exactly.
    """
    polys = {}
    for r in range(P):
        pts = [n for n in sorted(T) if n >= n0 and n % P == r]
        if len(pts) < 3:
            continue
        n1, n2 = pts[0], pts[1]
        y1, y2 = T[n1] - a * n1 * n1, T[n2] - a * n2 * n2
        b = (y2 - y1) / (n2 - n1)
        c = y1 - b * n1
        polys[r] = (b, c, pts, [n for n in pts if a * n * n + b * n + c != T[n]])
    return polys


def tail_estimate(T, P, count=8):
    """Fallback when no exact pattern is found: (min, mean, max) of D_P/(2P^2) over the last `count` n."""
    D = lag_second_differences(T, P)
    vals = [D[n] / (2 * P * P) for n in sorted(D)[-count:]]
    return min(vals), sum(vals) / len(vals), max(vals)


# ---------------------------------------------------------------------- fits (floats)

def rms_residuals(ns, Ts):
    """RMS residual (in rounds) of least-squares fits with three free parameters each."""
    n = np.array(ns, dtype=float)
    y = np.array(Ts, dtype=float)
    ones = np.ones_like(n)
    models = {"n log n": [n * np.log(n), n, ones], "quadratic": [n ** 2, n, ones]}
    out = {"linear": None, "n log n": None, "quadratic": None}
    for name, cols in {"linear": [n, ones], **models}.items():
        X = np.column_stack(cols)
        coef, *_ = np.linalg.lstsq(X, y, rcond=None)
        out[name] = float(np.sqrt(((y - X @ coef) ** 2).mean()))
    return out


def loglog_exponent(T, lo, hi):
    ns = [n for n in sorted(T) if lo <= n <= hi]
    return float(np.polyfit(np.log(ns), np.log([T[n] for n in ns]), 1)[0])


# ------------------------------------------------------------------------- reports

def report_tables(series, d, small=20):
    can, sh, rec = series[(d, "canonical")], series[(d, "shifted")], series.get((d, "recursive"), {})
    print(f"\n=== d = {d} ===   T(A) canonical, T(A') shifted, T(rec) recursive;  * prime, ^ power of 2")
    print("     n        T(A)   T(A')   T(rec)   T(A)/n^2  T(A')/n^2")
    for n in sorted(can):
        if n > small and not (is_prime(n) or is_power_of_two(n)):
            continue
        tag = ("*" if is_prime(n) else " ") + ("^" if is_power_of_two(n) else " ")
        print(f"  {n:4d} {tag}  {can[n]:8d} {sh[n]:7d} {str(rec.get(n, '')):>8s}   {can[n] / n ** 2:8.4f}  {sh[n] / n ** 2:8.4f}")


def report_structure(series, d):
    print(f"\n--- d = {d}: exact quasi-quadratic structure (lag-P second differences) ---")
    for construction in ("canonical", "shifted"):
        T = series[(d, construction)]
        top = max(T)
        found = find_quasi_quadratic(T)
        if found is None:
            P, (lo, mean, hi) = 6, tail_estimate(T, 6)
            print(f"  {construction:9s} n=3..{top}: no exact pattern with period <= 12 and a run >= 8; "
                  f"D_6/72 over the last 8 n: min {lo:.3f}, mean {mean:.3f}, max {hi:.3f}")
            continue
        P, n0, a, run = found
        polys = class_polynomials(T, P, n0, a)
        primes = [n for n in sorted(T) if n >= n0 and is_prime(n)]
        bad = [n for r in polys for n in polys[r][3]]
        below = [n for n in sorted(T) if n < n0]
        print(f"  {construction:9s} n=3..{top}: D_{P} = {2 * P * P * a} on n0={n0}..{top - 2 * P} ({run} values) "
              f"=> leading coefficient a = {a} (~{float(a):.4f}), period {P}")
        print(f"            exceptions to the class polynomials for n >= {n0}: {bad if bad else 'none'}; "
              f"{len(primes)} primes in that range, all on their class polynomial"
              f"{'' if not bad else ' EXCEPT ' + str([p for p in primes if p in bad])}; "
              f"transient below n0: {below if below else 'none'}")


def report_fits(series, d):
    print(f"\n--- d = {d}: RMS residual (rounds) of 3-parameter least-squares fits ---")
    print("                        primes n>=5                 all n>=8")
    print("                    linear  nlogn   quad       linear  nlogn   quad")
    for construction in ("canonical", "shifted"):
        T = series[(d, construction)]
        rows = []
        for ns in ([n for n in sorted(T) if n >= 5 and is_prime(n)], [n for n in sorted(T) if n >= 8]):
            r = rms_residuals(ns, [T[n] for n in ns])
            rows.append(f"{r['linear']:8.2f}{r['n log n']:7.2f}{r['quadratic']:7.2f}")
        print(f"  {construction:9s}      {rows[0]}      {rows[1]}")


def report_exponents(series):
    print("\n--- apparent exponent: log-log slope of T vs n (a pure quadratic plus a linear term looks sub-quadratic) ---")
    print("                    slope n in [8,20]   slope n in [N/2,N]   doubling exponents log2(T(2n)/T(n)), n = 10, 20, 40")
    for d in (3, 4, 5):
        for construction in ("canonical", "shifted"):
            T = series[(d, construction)]
            top = max(T)
            dbl = [f"{np.log2(T[2 * n] / T[n]):.2f}" if 2 * n in T else "  - " for n in (10, 20, 40)]
            print(f"  d={d} {construction:9s}   {loglog_exponent(T, 8, 20):6.2f}              "
                  f"{loglog_exponent(T, top // 2, top):6.2f} (N={top:2d})      {', '.join(dbl)}")


def report_recursive(series):
    print("\n--- contrast: the recursive construction at n = 2^p ---")
    for d in (3, 4, 5):
        rec = series.get((d, "recursive"), {})
        print(f"  d={d}: " + "  ".join(f"n={n}: T={T} (T/n={T / n:.2f}, T/n^2={T / n ** 2:.3f})" for n, T in sorted(rec.items())))


def check_closed_forms_d3(series):
    """d = 3 closed forms, asserted against every n in the data (conjectures beyond it)."""
    can, sh = series[(3, "canonical")], series[(3, "shifted")]
    even_shifted = lambda m: -(-(m * m + 16 * m - 24) // 8)        # ceil(m^2/8 + 2m - 3)
    assert all(can[n] == (n * n - 2 * n + 4) // 2 for n in can), "canonical closed form fails"
    assert all(sh[n] == (even_shifted(n) if n % 2 == 0 else even_shifted(n - 1) + 2) for n in sh), \
        "shifted closed form fails"
    print(f"\nd = 3 closed forms hold exactly for every n = 3..{max(can)} in the data:\n"
          "  T(A)  = floor((n^2 - 2n + 4) / 2)\n"
          "  T(A') = ceil(n^2/8 + 2n - 3) for even n;  for odd n, the same expression at n-1, plus 2")


# ------------------------------------------------- optional: every residue class

def residue_scan(d, nmax):
    """T for every class {v : sum(v) = c mod n}, not just c = 0 (A) and c = -floor(n/2) (A'), n = 3..nmax."""
    import simulate as sim            # imported here: only this mode needs the simulator
    import sweep
    print(f"\n=== d = {d}: all residue classes c, sets of size n^(d-1); lines shown for primes ===")
    best, worst, percolating = {}, {}, {}
    for n in range(3, nmax + 1):
        S = sweep.coordinate_sums(n, d)
        T = {}
        for c in range(n):
            infected, time = sim.simulate(S % n == c, n, d)
            if infected:
                T[c] = time
        c_shift = (-(n // 2)) % n
        best[n], worst[n], percolating[n] = min(T.values()), max(T.values()), len(T)
        if is_prime(n):
            c_best = [c for c in T if T[c] == best[n]]
            print(f"  n={n:3d}: {len(T):3d}/{n} classes percolate; T(A: c=0) = {T[0]}, T(A': c={c_shift}) = {T[c_shift]}, "
                  f"best c={c_best} T={best[n]}; worst T={worst[n]}")
    print(f"  every class percolates for every n = 3..{nmax}: {all(percolating[n] == n for n in percolating)}")
    for name, series in (("best class", best), ("worst class", worst)):
        found = find_quasi_quadratic(series)
        if found:
            P, n0, a, run = found
            print(f"  T({name}): D_{P} = {2 * P * P * a} on n0={n0}..{nmax - 2 * P} ({run} values) => a = {a}, period {P}")
        else:
            print(f"  T({name}): no exact pattern found; D_6/72 over the last 8 n: {tail_estimate(series, 6)}")
    print(f"  T(best class), n = 3..{nmax}: {[best[n] for n in sorted(best)]}")


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("csv", nargs="*", type=Path, help="sweep CSVs (default: notes/sweep-results*.csv)")
    parser.add_argument("--residue-classes", action="store_true", help="also scan all residue classes (d=3 primes)")
    args = parser.parse_args()
    paths = args.csv or [p for p in DEFAULT_CSVS if p.exists()]
    series = load(paths)
    for key, T in series.items():
        if key[1] != "recursive":                 # recursive rows are only n = 2^p, not consecutive
            assert sorted(T) == list(range(3, max(T) + 1)), f"{key}: n values are not consecutive from 3"
    print("data:", ", ".join(f"d={d} n<={max(series[(d, 'canonical')])}" for d in (3, 4, 5)), "from", [p.name for p in paths])
    for d in (3, 4, 5):
        report_tables(series, d)
    for d in (3, 4, 5):
        report_structure(series, d)
    for d in (3, 4, 5):
        report_fits(series, d)
    report_exponents(series)
    report_recursive(series)
    if (3, "canonical") in series and max(series[(3, "canonical")]) >= 20:
        check_closed_forms_d3(series)
    if args.residue_classes:
        residue_scan(3, 44)


if __name__ == "__main__":
    main()
