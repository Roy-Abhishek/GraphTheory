# Log — Question 7 (bootstrap percolation on grids)

## 2026-10-03 — `sage/hand_verify.py`: brute-force ground truth

Pure-Python simulator of d-neighbour (r = d) bootstrap percolation on [n]^d.
Synchronous rounds; "rounds taken" = number of rounds that infected >= 1 new vertex
(= T(A) when A percolates). Run: `python3 sage/hand_verify.py` (~55 s total).

### Canonical set A = ⋃_{i=1}^d V_{in}, d = 3 — exact results

| n | \|V_n\|, \|V_2n\|, \|V_3n\| | \|A\| | percolates? | **T(A)** | \|A_t\|, t = 0..T |
|---|---|---|---|---|---|
| 3 | 1, 7, 1  | 9  = 3² | yes | **3** | 9, 15, 21, 27 |
| 4 | 3, 12, 1 | 16 = 4² | yes | **6** | 16, 30, 34, 40, 49, 61, 64 |

- Layer sizes were also counted by hand (bounded compositions) and agree.
- n = 3, round 1 checked by hand: the 3 permutations of (2,2,1) and the 3 of (3,2,2)
  each have exactly 3 infected neighbours → |A_1| = 9 + 6 = 15. Matches the simulator.

### Is n^(d-1) the minimum? (n = 3, d = 3, bound = 9)

- Argument: P(S) = 2d|S| − 2e(S) never increases under the r = d rule (Δ = 2d − 2a ≤ 0
  for a ≥ d infected neighbours), ends at 2d·n^(d-1), starts at <= 2d|A| ⇒ |A| >= n^(d-1).
  (My own sketch, not checked against the paper — treat as a hypothesis; the brute force
  below is the real check. It is consistent with Theorem 1 of the paper.)
- Brute force: percolation is monotone in A, so it suffices to test size 8 exactly.
  All C(27,8) = 2,220,075 subsets of size 8 tested: **0 percolate**.
  Positive control: the same search finds a percolating 9-set immediately.
  ⇒ for n = d = 3 the minimum percolating set size is exactly 9 = n^(d-1).

### Simulator calibration (brute-force m_d(n) over all optimal-size sets)

- d = 2, n = 2..5: m_2(n) = 1, 2, 3, 4 = n − 1. **Matches Theorem 2.**
- d = 1, n = 2..7: m_1(n) = 1, 1, 2, 2, 3, 3 = ⌊n/2⌋.
  **Discrepancy with refs/code-context.md**, which says m_1(n) = ⌈n/2⌉ (differs for odd n).
  For a path the best single seed is the middle vertex, T = max(v−1, n−v) = ⌊n/2⌋, so the
  simulator is right for the graph as defined, and the summary (or the paper's convention)
  is the thing to check. NOT yet verified against the PDF (no PDF tooling installed here:
  no pdftotext / pdftoppm). Irrelevant to Question 7 (d >= 3) but fix code-context.md once
  the paper's exact statement is confirmed.

## 2026-10-03 — Growth of T(A), T(A') in n: anything sub-quadratic for non-powers of 2?

**Question** (decides explicit construction vs. sharper potential-function argument): for n that are
not powers of 2, primes especially, do T(A) (canonical) and T(A') (shifted, V_{in-⌊n/2⌋}) grow
linearly, like n log n, or like n² (the Theorem 2 bound)?

**Answer: Θ(n²). A' is not sub-quadratic for primes, and nothing else tested is either.** For d = 3, 4
(and A at d = 5), T is *exactly* a degree-2 quasi-polynomial in n with a strictly positive leading
coefficient over the whole range tested (d = 3: n = 3..80), with no exceptions at primes. A' beats A
by a constant factor (4× asymptotically at d = 3), not by a better exponent.

### Data and method
- `notes/sweep-results.csv` (n = 3..20) + new `notes/sweep-results-extended.csv` (d=3 n ≤ 80, d=4 n ≤ 40,
  d=5 n ≤ 24; produced by the same `sage/sweep.py`, so same preflight tests). Analysis:
  `sage/analyze_growth.py` (numpy + exact Fractions); figure: `sage/plot_growth.py` (matplotlib, see
  "Figure" below).
- Test: lag-P second difference D_P(n) = T(n+2P) − 2T(n+P) + T(n). If T = a·n² + (linear terms whose
  coefficients depend only on n mod P), then D_P ≡ 2aP² exactly. If T ~ c·n log n, D_P ~ cP²/n would
  shrink ~25× between n = 3 and n = 80; if T were linear, D_P → 0.

### Results
Leading coefficient a (T ≈ a·n²), read off an exactly constant D_P over the stated range:

| d | A (canonical) | A' (shifted) | Theorem 2 constant d+2 (*) |
|---|---|---|---|
| 3 | **1/2**, period 2, n = 3..80 | **1/8**, period 4, n = 3..80 | 5 |
| 4 | **2/3**, period 3, n = 4..40 | **1/2**, period 2, n = 5..40 | 6 |
| 5 | **1**, period 2, n = 3..24 | no exact pattern by n = 24; a ≈ 0.67–0.69 | 7 |

(*) from refs/code-context.md, (d+2)n² + n; not re-checked against the PDF.

d = 3 closed forms, asserted for every n = 3..80 (a conjecture beyond that):
`T(A) = ⌊(n² − 2n + 4)/2⌋`; `T(A') = ⌈n²/8 + 2n − 3⌉` for even n, and for odd n the same expression at
n − 1, plus 2. The pattern is exact from n = 3 on (no transient). At d = 4 only n = 3 (A) and n = 3, 4
(A') are off-pattern.

**Primes are not special.** All primes in the stable range (21 of them at d = 3) lie on the same class
polynomial as the composites with the same residue mod P: 0 exceptions. At d = 3, T(A') at odd n ≥ 5 is
T(n−1) + 2. Prime n at d = 3:

| n | 3 | 5 | 7 | 11 | 13 | 17 | 19 | 23 | 31 | 47 | 61 | 79 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| T(A) | 3 | 9 | 19 | 51 | 73 | 129 | 163 | 243 | 451 | 1059 | 1801 | 3043 |
| T(A') | 4 | 9 | 16 | 32 | 41 | 63 | 76 | 104 | 172 | 356 | 569 | 916 |
| T(A')/n² | .444 | .360 | .327 | .264 | .243 | .218 | .211 | .197 | .179 | .161 | .153 | .147 |

### Figure

![T(A), T(A') and the recursive set against n, for d = 3, 4, 5](growth-plots.png)

Dots mark primes. Row 1: T on log-log axes with ∝ n and ∝ n² guides. Row 2: T/n²: A and A' level off at
their exact limits (dashed) while the recursive set keeps falling. Row 3: the exact second-difference
test, a(n) = D_P(n)/2P², flat for every exactly-patterned series, against the 1/n decay that n log n
growth would give (dashed gray; anchored on A''s plateau). A' at d = 5 has no exact period by n = 24, so
its row-3 line is the noisy P = 6 estimate. Series colours are the dataviz palette's categorical slots
1–3; the validator passes light mode all-pairs (contrast WARN for the aqua recursive set, relieved by
direct labels and the tables here). Regenerate with `~/miniforge3/envs/sage/bin/python
sage/plot_growth.py` (matplotlib lives in the conda env `sage`, not in the default `python3`).

### Why eyeballing at n ≤ 20 would have misled (all three traps are visible in this data)
1. Naive log-log slope of T(A') at d = 3 is 1.56 on n ∈ [8, 20], but the doubling exponents
   log₂(T(2n)/T(n)) are 1.54, 1.67, 1.79 for n = 10, 20, 40: creeping up to 2, because
   T(A') = n²/8 + 2n − 3 and the linear term dominates until n ≈ 16.
2. T/n² falling steadily (.444 → .147 over the primes above) is not evidence of sub-quadratic growth: it
   converges to 1/8 like 1/8 + ~1.75/n.
3. Smooth fits separate poorly on the 7 primes up to 19 (A' at d = 3: RMS 0.25 rounds quadratic vs 0.48
   n log n). On the extended data, RMS residual (rounds) for primes n ≥ 5 at d = 3: A: quadratic 0.00,
   n log n 45, linear 226; A': 0.25, 11.3, 56. Constant D_P is the sharper test.

### Not asked, but it decides how much "A' is quadratic" means: all residue classes, d = 3
A and A' are two members of the family {v : Σv ≡ c (mod n)}, all of size n^(d-1). Scanned every c for
every n = 3..44: **every class percolates**. The best class is c = (n+3)/2 for every odd prime tested
(5..43), one step past A''s class (n+1)/2, and is only ~7% faster than A' (n = 43: 283 vs 304). Its time
is exactly quasi-quadratic with a = 1/8 (D₄ ≡ 4, n = 3..36), same as A'; the worst class has a = 1/2. So
every class is Θ(n²) with constant between 1/8 and 1/2: A' is not an unlucky shift.

### Contrast: the recursive set at n = 2^p is linear
d = 3, T = 5, 15, 37, 83, 177 for n = 4, 8, 16, 32, 64 (T/n = 1.25 … 2.77, tending to d; T/n² = .043
at n = 64 and falling like 1/n). Versus A' at the same n: 7, 21, 61, 189, 637, so the gap widens linearly
(1.4×, 1.4×, 1.6×, 2.3×, 3.6× from n = 4 to 64). These are the nim-sum sets {x : x₁⊕…⊕x_d = 0}, which are
not residue-class sets.

### What this means for the decision (my reading, not a theorem)
1. Don't try to prove A' (or A) is o(n²): the data say it is false, with no sign of a regime change
   through n = 80 at d = 3. If the (d+2)n² + n bound is for the canonical set (as code-context.md
   suggests; unverified), it is already tight for A up to the constant (a = 1/2, 2/3, 1 vs 5, 6, 7), so a
   sharper potential-function argument on A can only improve the constant.
2. So o(n²) for general n needs a different initial set. That favors the explicit-construction route; the
   potential-function / witness-tree machinery is then the tool for bounding T of whatever set is found.
   The two routes are not alternatives.
3. The only fast sets known are the XOR ones at n = 2^p. Primes have no digit structure to imitate, and
   the residue-class family is exhausted at d = 3, so primes need a genuinely new idea (e.g. code-context
   line of attack 2, padding/embedding into 2^p).

### Not established
- Nothing here says no optimal-size set has o(n²) time for prime n; m_d(n) itself is untouched. Only A, A'
  and the residue classes were examined.
- Extrapolation past n = 80 (d=3), 40 (d=4), 24 (d=5) is conjecture. A' at d = 5 has no exact formula
  yet; that likely needs n ≳ 40 at d = 5 (~10⁸ cells).
- Every T comes from `simulate.py`, validated against the brute-force simulator on small cases. Extra:
  24 prime-n rows (d=3 primes 11..31, d=4 primes 7, 11, 13, d=5 primes 5, 7) were re-derived with the
  pure-Python `hand_verify.percolate` on sets built from the literal layer definitions: all match.

### Suggested next experiments (not run)
(a) heuristic search (hill-climbing / annealing over percolating sets of size n^(d-1), objective T) at
n = 5, 7, 11, d = 3: the first direct evidence on whether T can fall far below n²/8 for primes, and
what such sets look like; (b) adapt the recursive set of the next power of 2 down to [n]^d and measure
T at primes; (c) exhaustive m_3(3) (4.7M sets, minutes) as one ground-truth value at a prime.

Reproduce: `python3 sage/analyze_growth.py` (seconds), `--residue-classes` adds ~100 s; the figure with
`~/miniforge3/envs/sage/bin/python sage/plot_growth.py`. The extended sweeps are the three
`sage/sweep.py` commands in the `analyze_growth.py` docstring.

## 2026-10-04 — Fast minimum percolating sets at d = 3: exact ground truth, search, structure, and an explicit family with T = 3(n−1)/2

### Headline finding

**There is an explicit infinite family of minimum percolating sets of [n]³ with T = 3(n−1)/2, exactly the lower
bound below, for n = 2^k − 3 (n = 5, 13, 29, 61, 125, 253, …).** These n are not powers of 2, and T is linear in n.

- Write n = 2m + 1 with centered coordinates u ∈ {−m..m}³. The set Aₙ is the central hexagon H = {u : u₁+u₂+u₃ = 0}
  (3m(m+1)+1 cells) together with a "face gadget" on each of the six faces u_i = ∓m. In the local frame
  (δ, a, b) = (u₁+m, m−u₂, m−u₃) of the apex corner (−m, m, m) the gadget lies on the face δ = 0 and, for m = 2^j − 2
  (m = 2, 6, 14, 30, 62, 126, …), is
  **P(m) = {(a, b) : for some ℓ ≥ 0, a ≡ b ≡ 2^ℓ − 1 (mod 2^(ℓ+1)) and a + b ≤ m − 2^(ℓ+1)}**,
  equivalently P(0) = ∅ and P(m) = {(2i, 2j) : i + j ≤ m₀} ∪ {(2i+1, 2j+1) : (i, j) ∈ P(m₀)}, m₀ = (m−2)/2. The other
  five apexes use the images under the symmetries of the cube. |P(m)| = m(m+1)/6, so |Aₙ| = 3m(m+1)+1 + m(m+1) = n².
- **Proved for every k** (hand proof in "Proof for every k" below, built on the structure theorem and lower bound further
  down; each step is also checked by computer, but nothing is formalised in Lean). Aₙ has n² cells, no two adjacent, and
  percolates in exactly 3(n−1)/2 rounds, the lower bound, so T(Aₙ) = m₃(n) for all n = 2^k − 3. Computer checks:
  `sage/gadget.py verify` simulates n = 5, 13, 29, 61, 125, 253 with two independent simulators (`minperc.py`,
  `simulate.py`; the Phase-1 brute-force `hand_verify.py` agrees up to n = 61), and the proof's local condition holds on
  the whole cube up to n = 1021 (`sage/gadget.py local`); `sage/test_gadget.py`. The pattern was found, not designed: the
  solver produced the n = 29 gadget on its own (unique, one second once the search is restricted to the faces), the
  recursion and closed form were read off it, n = 61, 125, 253 were predictions that held, and the proof then
  came from seeing that the gadget's odd–odd cells replay the next smaller gadget at double speed.
- At the same n, T of the paper's sets (exact simulation, `notes/family-comparison.csv`, figure `notes/family-T-vs-n.png`):

  | n | lower bound = Aₙ | best residue class | A′ | A |
  |---|---|---|---|---|
  | 5 | 6 | 8 | 9 | 9 |
  | 13 | 18 | 36 | 41 | 73 |
  | 29 | 42 | 140 | 153 | 393 |
  | 61 | 90 | 540 | 569 | 1801 |
  | 125 | 186 | not run | 2169 | 7689 |
  | 253 | 378 | not run | not run | not run |

  T(A′)/n² is 0.18, 0.15, 0.14 at n = 29, 61, 125, converging to 1/8 (2026-10-03 entry), while the family's T/n² is
  about 1.5/n, which falls to 0.

**What this says about Question 7** (is m_d(n) = o(n²) for d ≥ 3? d = 3 here). Since the construction is proved for every k,
m₃(n) = 3(n−1)/2 = Θ(n) along n = 2^k − 3, and the constant 3/2 of the paper's lower bound dn/2 + O(1) is attained
exactly. That is the "restricted infinite family" outcome of line of attack 4 in `refs/code-context.md`, for a family
disjoint from the powers of 2 (the paper has m_d(2^p) ≤ d·2^p) and containing primes (5, 13, 29, 61). It does **not**
answer general n: this mechanism exists only for n + 3 a power of 2 (checked up to n = 41, below), and the optimum is
still open at n = 8, 9, 11.

Best sets found by search for the small n (each re-verified by two independent simulators; sets stored in
`notes/best-sets-d3.json`, n = 29 is the family above):

| n | lower bound | best T found | status | best residue class | A' | recursive set |
|---|---|---|---|---|---|---|
| 3 | 3 | **3** | exact (brute force over all 4,686,825 9-sets) | 3 | 4 | |
| 4 | 4 | **4** | exact | 6 | 7 | 4 |
| 5 | 6 | **6** | exact | 8 | 9 | |
| 6 | 7 | **7** | exact | 11 | 14 | |
| 7 | 9 | **9** | exact | 13 | 16 | |
| 8 | 10 | 11 | open [10, 11] (the recursive set) | 18 | 21 | 11 |
| 9 | 12 | 14 | open [12, 14] (best D₃d-symmetric set) | 20 | 23 | |
| 11 | 15 | 17 | open [15, 17] | 27 | 32 | |
| 13 | 18 | **18** | exact | 36 | 41 | |
| 29 | 42 | **42** | exact (face-window search; the family) | 140 | 153 | |

"Exact" = a verified set attains the lower bound. So for the primes 5, 7, 13, 29 the optimum is known and equals 3(n−1)/2
(1.2n, 1.29n, 1.38n, 1.45n), against 8, 13, 36, 140 for the best residue class and 9, 16, 41, 153 for A′; at n = 11 the answer is in
[15, 17] against 27 and 32. The Θ(n²) of A, A′ and every residue class is a property of those sets, not of the problem.

### Ground truth: m₃(3) = 3, exactly

`sage/exhaustive_m3_3.py` simulates all C(27,9) = 4,686,825 subsets of [3]³ (18 s on 12 cores): **116 percolate**,
with times {3: 4 sets, 4: 64, 6: 48}; so **m₃(3) = 3**, attained by one symmetry class (the canonical set).
7 classes under the 48 cube symmetries. Only 12 of the 116 are Latin squares (every axis-parallel line has
exactly one point), so minimum sets are not Latin in general. All 116 satisfy the structure theorem below.

### Structure theorem and lower bound (new; proved, and checked)

For a percolating set of the minimum size n² the perimeter argument of Phase 1 is tight (initial perimeter
2d|A| = final perimeter 2d·n^(d−1), never increasing), which forces: A is independent; every cell outside A has
**exactly** d earlier-infected neighbours when infected; no two adjacent cells are infected in the same
round. Orienting each edge from earlier to later gives an **acyclic orientation with every in-degree in {0, d}**
whose sources are exactly A; T is its longest directed path; conversely every such orientation is a minimum
percolating set. Checked: 116/116 percolating 9-sets of [3]³; every percolating n-subset of [n]² for n = 3, 4, 5
(14, 130, 1615 sets; min T = n−1, so m₂(n) = n−1 of Theorem 2 comes out as the same bound); every set found.

*Lower bound, odd n.* A cell with in-degree d has out-degree deg − d, which is 0 only for the degree-d cells,
the corners; sources have out-degree deg ≥ d. So every maximal directed path ends at a corner. Infection time
strictly increases along edges, and the center cell is at Manhattan distance d(n−1)/2 from every corner, so
**T ≥ d(n−1)/2** (d = 3: 3(n−1)/2). `exact.c` proves the sharper ⌊3(n−1)/2⌋ for every n = 3..15, even n
included, by constraint propagation at the root node (no search), `sage/test_exact.py`.

Consequences for any set that meets the bound T = 3m (n = 2m+1): the center is a source, its six neighbours are
infected in round 1, and **label(v) ≤ Manhattan distance of v from the center** for every cell: the infection
never lags the octahedral ball around the center (it follows from propagation at height 3m; also checked
directly on the 11 optimal n = 7 sets found by annealing and on the n = 13 optimum).

### Tools (all validated against brute force; see "Reproduce")

- `sage/exact.c` + `search.exact`: complete search over level labelings t: cells → {0..H} (adjacent labels
  differ; t = 0 iff source; otherwise exactly 3 smaller-labelled neighbours, one of them t−1): domain
  propagation + DFS, with orbit symmetry, pinned sources, forbidden sources, randomised restarts. It
  reproduces the n = 3 set counts at every height (0, 4, 68, 68, 116 for H = 2..6) and agrees with brute
  force on six boxes, pinned cells and symmetric subspaces (`sage/test_exact.py`).
- `sage/anneal.c` + `search.search`: simulated annealing on the same labelings (orbit moves, pins, sound
  corner bound, automatic height descent). Everything it returns is re-verified; it only ever returns sets from
  the exhaustive n = 3 list (`sage/test_search.py`).
- `sage/minperc.py`: boxes of any shape, the tight-structure check, cube symmetries, orbits.
- `sage/hexagon.py`: D₃d-symmetric completions of the central hexagon (windowed, or `--face`: sources only on the six
  face triangles). `sage/gadget.py`: the explicit family, its closed form, the n = 13 triple family and the comparison
  table; `sage/test_gadget.py` (13 s) checks all of it, including that the solver's unique face-only completion at
  n = 5, 13, 29 is the construction.

### What the optimal sets look like

- **Not Latin squares, but near-Latin and highly varied.** At n = 5 there are at least 242 distinct optimal sets
  in 38 symmetry classes (found by annealing). After aligning the classes, only 6 of the 25 cells are sources in
  all 38: the center, the four other cells of one central-plane anti-diagonal, and one further cell.
- **The central diagonal hexagon.** For every optimum with D₃d symmetry (all coordinate permutations and the point
  reflection), the sources contain a large part of the plane H = {u : u₁+u₂+u₃ = 0} (centered coordinates): all of
  it at n = 3, 5, 13 and 29, a central part at n = 7, 9, 11 (19/37, 25/61, 55/91 cells). On the central plane the
  infection time is exactly |y + z|: a wave moving out from the anti-diagonal.
- **n = 13 (T = 18 = lower bound) is hexagon + 42 "fixers".** The 127 hexagon cells plus m(m+1) = 42 extra
  sources, so |A| = 3m(m+1)+1 + m(m+1) = (2m+1)². Cells with Σu > 0 on a face u_i = −m lack a "lower"
  neighbour, so the hexagon wave alone cannot infect them (each face has a triangle of T(m) = m(m+1)/2 such
  cells, 6 faces in all, counting Σu < 0 on the other three); the fixers are what repairs them.
- **The fixers form six identical gadgets, one at each of the six corners with |Σ| = m**, e.g. (−m, m, m). In the
  local frame of that corner, (δ, a, b) = (u₁+m, m−u₂, m−u₃), the D₃d-symmetric completions at n = 13 are
  **exactly** the C(9,3) = 84 sets given by a non-decreasing triple 0 ≤ x ≤ y ≤ z ≤ 6:
  `(z;0,0)`, `(x;0,4)`, `(x;4,0)`, `(y;0,2)`, `(y;2,0)`, `(y;1,1)`, `(y;2,2)`.
  An exhaustive enumeration with the exact solver gives exactly 84 and the rule reproduces exactly those sets
  (`sage/hexagon.py` states the rule; the comparison was run, all 84 verified: |A| = 169, T = 18).
  **The six apexes are independent**: at n = 13 all 84·84·6 = 42,336 sets with one apex's triple changed, and 4,000
  random six-tuples of triples, are valid optima (`sage/gadget.py family13`); the 84⁶ ≈ 3.5·10¹¹ combinations were not
  all tested. At n = 5 the independence is exact (next bullet).
- **At n = 5 the completions of the hexagon have exact product structure**: 729 = 3⁶ optimal sets contain it
  (no symmetry assumed), and they are precisely hexagon + one cell from each of six 3-cell half-edges
  (cells (−2,−2,c), c = 0..2, and the five other edges meeting the corners ±(2,2,2)). The six choices are
  independent. Symmetric completions: 3.
- **Which n have a hexagon completion?** (D₃d-symmetric, hexagon pinned, height 3m.) Found: n = 3 (the hexagon plus the
  two axis corners ±(1,1,1), T = 3), 5, 13 and 29. Refuted exhaustively with the sources restricted to a window around
  the apexes (any depth δ, a, b ≤ m − 2, a ≡ b mod 2): n = 7, 9, 11, 15, 19, 23, 27 (instantly, at the root of the search)
  and n = 17 (688 s); unfinished in that window at n = 21, 25 (300 s, 600 s) and n = 29 (1500 s). With the sources
  restricted to the six faces instead (`hexagon.py --face`, 0–16 s per n) a completion exists exactly at n = 5, 13, 29,
  unique each time, and the solver proves there is none at any other odd n from 7 to 41 (exhaustive within the face
  window; 41 is where exact.c's 62-level domains run out). So within this mechanism n + 3 must be a power of 2 (up to n = 41), and
  the recursion below gives a construction, proved to work, for every such n. (Counting alone, 6 | m(m+1) over six
  apexes, only excludes m ≡ 1 mod 3.)

### The face gadget and its recursion (the family)

The member (x, y, z) = (0, 0, 0) of the n = 13 family puts every fixer on the face triangle {δ = 0, a + b ≤ m − 1}, the
T(m) cells of the face u₁ = −m that the hexagon wave cannot reach. Restricting the sources to the six triangles turns
the search from hours into seconds and answers n = 29: **a hexagon completion exists, it is unique, and T = 42 =
3(n−1)/2.** Its gadget has 35 cells per apex, all on the face δ = 0: the 28 cells (a, b) with a, b even and a + b ≤ 12,
and the seven odd cells (1,1), (1,5), (1,9), (3,3), (5,1), (5,5), (9,1).

The seven odd cells are exactly the n = 13 gadget {(0,0), (0,2), (0,4), (1,1), (2,0), (2,2), (4,0)} in the coordinates
((a−1)/2, (b−1)/2), and the n = 13 gadget is itself the six even cells with a + b ≤ 4 plus (1,1), which is the single
cell of the n = 5 gadget {(0,0)} in those coordinates. That is the recursion of the headline (even cells with
a + b ≤ m − 2, plus the odd cells (2i+1, 2j+1) for (i, j) ∈ P(m₀), m₀ = (m − 2)/2), and the closed form follows by
unrolling it. Its size is what n² requires, identically: m₀(m₀+1)/6 + (m₀+1)(m₀+2)/2 = m(m+1)/6 for m = 2m₀ + 2. That identity
holds for every m₀, so counting does not restrict m₀; what does is that the recursion needs P(m₀) to exist, so m₀ must
itself be 2^j − 2 (there is no face-only completion at n = 7, 9, 11, …, hence no P(3), P(4), P(5), …).

What the infection looks like on Aₙ (checked for m = 2, 6, 14, 30, 62; labels are infection times):
- every cell off the six triangles is infected at round |u₁+u₂+u₃| exactly (the hexagon wave), and the six triangles
  carry the same pattern;
- on a triangle the labels are small: 0 at the sources and at most m/2 anywhere (7 at m = 14, 31 at m = 62);
- self-similar: for m = 2m₀ + 2 the triangle contains three copies of the m₀ triangle with identical labels (at the apex
  corner, and shifted to (0, m₀+2) and (m₀+2, 0)); the two lines a = m₀+1 and b = m₀+1 carry the wave labels m − a − b;
  the remaining T(m₀+1) cells form a middle inverted triangle.

### Proof for every k

Status: proved by hand below; each step is also checked by computer on finite cases (`sage/test_gadget.py`,
`sage/gadget.py local`); **not formalised in Lean**.

Setting: m = 2^j − 2 (j ≥ 2), n = 2m+1, Σ(u) = u₁+u₂+u₃; H, P(m), Aₙ as in the headline. Count: |H| = 3m²+3m+1 and
|P(m)| = (m₀+1)(m₀+2)/2 + |P(m₀)| = m(m+1)/6; the six gadgets and H are pairwise disjoint (gadget cells have Σ ≥ 2); so
|Aₙ| = 4m²+4m+1 = n².

*Certificate.* If L is a function on the cells with L = 0 exactly on A, and every cell with L(u) > 0 has at least 3
neighbours v with L(v) < L(u), then A percolates and u is infected by round L(u): induct on L(u), its three earlier
neighbours are infected by round L(u) − 1. So T(A) ≤ max L.

*Triangles.* Tri = {u : some u_i = −m and Σ(u) > 0} ∪ {u : some u_i = +m and Σ(u) < 0}: six disjoint copies of
Δ_m = {(a, b) : a, b ≥ 0, a + b ≤ m − 1} (for the face u₁ = −m: a = m−u₂, b = m−u₃; the line a + b = m, called
Hyp_m, is the hexagon on that face). A cell with Σ > 0 outside Tri has all coordinates > −m, so its three "lower"
neighbours u − e_i all exist; symmetrically for Σ < 0 with u + e_i.

**Lemma 1 (one triangle, in 2D).** Define ℓ_m on Δ_m ∪ Hyp_m for m = 2m₀+2 from ℓ_{m₀} (start: Hyp₀ = {(0,0)}, ℓ₀ = 0):
(e) ℓ_m = 0 where a and b are both even; (o) ℓ_m(2i+1, 2j+1) = 2·ℓ_{m₀}(i, j); (x) for a + b odd,
ℓ_m(a, b) = 1 + min ℓ_m over the existing neighbours (a±1, b) if a is even, or (a, b±1) if b is even (they are odd–odd).
Then, on Δ_m: (i) ℓ_m(a, b) ≤ m − a − b; (ii) every cell with ℓ_m > 0 has at least 3 in-plane neighbours
(a±1, b), (a, b±1) of smaller ℓ_m (a neighbour with a negative coordinate does not exist); (iii) ℓ_m = 0 exactly on P(m).
*Proof*, by induction on j (base m = 2: Δ₂ = {(0,0), (0,1), (1,0)} with ℓ₂ = 0, 1, 1). (iii) is the recursion for P.
(i): even–even 0 ≤ Σ; odd–odd: 2ℓ_{m₀}(i,j) ≤ 2(m₀−i−j) = m−a−b; mixed: ℓ ≤ 1 + ℓ(v₊) with v₊ = (a+1, b) or (a, b+1) odd–odd
(on Δ_m or Hyp_m) and Σ(v₊) = Σ − 1. (ii): a mixed cell with a even has neighbours (a, b±1) even–even or on Hyp_m
(they exist since b ≥ 1 and the sums are ≤ m): two neighbours with ℓ = 0 < ℓ, and the neighbour that attains the
minimum in (x) has ℓ − 1: three. An odd–odd cell w = (2i+1, 2j+1) with ℓ_m(w) > 0: by (ii) for m₀ at (i, j), at least
three neighbours w'_k of (i, j) have ℓ_{m₀}(w'_k) < ℓ_{m₀}(i, j); the odd–odd cell w_k = 2w'_k + (1,1) at distance 2 from
w then has ℓ_m(w_k) = 2ℓ_{m₀}(w'_k) ≤ ℓ_m(w) − 2, and the cell c_k midway between w and w_k is a neighbour of w, mixed, in
Δ_m, with w and w_k as its two odd–odd neighbours, so ℓ_m(c_k) ≤ 1 + ℓ_m(w_k) ≤ ℓ_m(w) − 1: three earlier neighbours. □

**Lemma 2 (the cube).** Let L(u) = |Σ(u)| off Tri and L = ℓ_m (in the triangle's coordinates) on Tri. Then L = 0 exactly
on Aₙ, max L = 3m, and every cell with L > 0 has at least 3 neighbours of smaller L.
*Proof.* L = 0 on H and, on Tri, exactly on the gadget cells (Lemma 1(iii)). A triangle cell: Lemma 1(ii); its in-face
neighbours are exactly the in-plane neighbours of the lemma, those across the hypotenuse lie in H (L = 0 = ℓ_m on Hyp_m),
the cube has nothing beyond the face edges, and the cell above is simply not used. A cell u ∉ Tri with s = Σ(u) > 0:
its three neighbours u − e_i exist and have Σ = s − 1; each lies in H (s = 1), or outside Tri with L = s − 1, or in Tri
with L = ℓ_m ≤ Σ = s − 1 by Lemma 1(i); so three neighbours have L ≤ s − 1 < L(u). The case Σ < 0 is the same under
u ↦ −u, which maps Aₙ and Tri to themselves. Finally L ≤ |Σ| ≤ 3m, with equality at the corners. □

**Theorem.** For n = 2^k − 3 (k ≥ 3), Aₙ percolates in [n]³, |Aₙ| = n², and T(Aₙ) = 3(n−1)/2. *Proof.* T ≤ max L = 3m
by the certificate; T ≥ 3m by the corner-sink bound above (odd n); |Aₙ| = n² is the minimum size (Theorem 1 of the
paper). Hence m₃(n) = 3(n−1)/2 for these n. □

Machine checks of the pieces (all exact integer computations): the 2D process on the triangle reproduces (e), (o), (x),
(i) and the maximum m/2 for every m = 2^j − 2 up to 1022 (a triangle of 522,753 cells); Lemma 2's local condition holds on the
full cube array for n = 5, 13, …, 253 (in the test suite) and 509, 1021 (`sage/gadget.py local`); two independent simulators
(and, to n = 61, the Phase-1 brute-force simulator) give T = 3(n−1)/2 for n = 5, …, 253; deleting any one gadget cell at
m = 6 or 14 leaves triangle cells never infected, so the checks are not vacuous.

### Padding / embedding (code-context.md, line of attack 2)

Restricting the recursive power-of-2 set R_c = {x : x₁⊕x₂⊕x₃ = c} of [N]³ to a sub-box [n]³ **breaks at the
first step and cannot be repaired by adding a few sources**:

- **Too small, and not infecting enough.** n = 5 inside N = 8: 8 parity variants × 64 sub-boxes = 16
  restrictions up to symmetry, keeping 12–19 of the 25 needed sources (≤ 76%); the four best infect only
  53.6–56.8% of the cube on their own. n = 7 inside N = 8: 8 restrictions up to symmetry keep 42–43 of the 49 needed and
  infect 26–43% alone (top four rows). n = 11 inside N = 16: 128 restrictions keep 72–91 of 121 (at most 75%), and the
  best four infect 41–42% alone.
- **Not extendable.** The best n = 5 restriction (19 kept, 6 to add) was tested **exhaustively**: all
  35,230,914 independent ways to add 6 sources (cells not adjacent to the 19) were simulated, **none
  percolates**. So no minimum percolating set of [5]³ contains that restriction. Pinned annealing finds no
  extension for the four largest restrictions at n = 5, 7 or 11 either, and for one of the best n = 7 restrictions
  (43 kept, c = 0) the exact solver proves that **no completion percolates in 13 rounds or fewer** (root propagation at
  heights 9–13; the lower bound is 9; height 14 undecided after 240 s). So even an extension, if one exists, would be
  much slower than the m₃(7) = 9 sets.
- **Even a perfect adaptation would not help at these sizes.** The recursive sets themselves take T = 11–15 at
  N = 8 and 26–37 at N = 16 (over parity variants), against m₃(7) = 9, m₃(5) = 6 and best-known 17, 18 at n = 11, 13:
  the direct optima are faster than anything the power-of-2 sets give at N.
- **The unequal-split variant of the recursion is blocked at n = 5.** Splitting [n] = a + b makes the even
  sub-boxes a³, ab², …; their size bounds add up to exactly n² for any a, b. But a box must admit a percolating
  set of its size bound (ab+bc+ca)/3 at all. Exhaustive table of small boxes (`embed.py boxes`; `-` none exists,
  `?` inconclusive): 2×3×3 **none**, 1×4×4 none, 1×3×6 none, 1×1×4 none; they exist for 1×3×3, 2×2×2, 2×2×5,
  2×3×6, 2×6×6, 3×3×3 (T = 3), 3×3×4 (6), 3×3×5 (4), 3×4×6 (6), 4×4×4 (T = 4), 6×6×6 (T = 7). So n = 5 = 2 + 3 needs
  2×3×3 and 5 = 1 + 4 needs 1×4×4: both fail.

### What did not work

- **Annealing does not scale past n = 7.** From random starts it finds T = 6 at n = 5 in seconds, T = 12 once at
  n = 7; seeded from the best residue class it reaches T = 9 at n = 7 but finds nothing below the class at n = 9
  (20) or n = 11 (27); at n = 9 it cannot even find a valid set from the radial start at height 16.
- **Plain DFS (and randomised restarts) cannot find optimal sets at n = 5 without symmetry or pins**, although
  solutions are plentiful; it is excellent for *proving* lower bounds and for symmetric subproblems.
- **Wide-window symmetric search does not scale.** Unconstrained D₃d search at n = 15, 17, 19 found nothing in 4 min
  each; with the hexagon pinned and the sources restricted to a window around the apexes (`sage/hexagon.py`) n = 13 is
  instant, but n = 17 takes 688 s to refute and n = 21, 25, 29 did not finish in 5–25 min. What fixed it was
  restricting the sources to the six faces (`--face`, the (0,0,0) member of the n = 13 family): 0–16 s for every odd
  n ≤ 41, and that is how n = 29 was found.
- Source-swap moves keep sets valid, but every valid single swap from the best residue class raises T by at least 2
  (n = 7: 13 → 15; n = 9: 20 → 22 or more), so the class is a local optimum under swaps.

### Not established

- Whether m₃(n) = ⌊3(n−1)/2⌋ for all n. Known exactly: n = 3…7 (brute force / search), 13, 29 (search) and every
  n = 2^k − 3 (the explicit family, proved). n = 8, 9, 11 are open (best 11, 14, 17). At n = 9 and 11 the best
  D₃d-symmetric optimum is 14 and 17 (exhaustive within D₃d: 13 and 16 are impossible there); an unsymmetrised or
  lower-symmetry optimum may be lower.
- That the face gadget is the only face-only completion (unique at n = 5, 13, 29 by exhaustive search, not proved in general),
  and that hexagon-plus-face-gadget sets need n + 3 a power of 2 (refuted exhaustively for every other odd n ≤ 41 only).
  The percolation of the family itself is proved for every k, by hand (not in Lean).
- General n. The family is sparse; nothing here gives o(n²) for, say, n = 100 or the prime 11 (best known T = 17 there).
- All of this is d = 3. The structure theorem and the corner-sink bound hold for every d (in-degrees {0, d},
  sinks are the degree-d corners, T ≥ d(n−1)/2 for odd n; at d = 2 it reproduces m₂(n) = n−1), but the solvers
  here are written for d = 3.
- Even n has no center cell; its optimal structure was not studied beyond n = 4, 6, 8.

### Suggested next experiments

(a) **Formalise in Lean**: the certificate lemma, Lemma 1 (a structural recursion on j over a 2D triangle), Lemma 2, and the
structure theorem with the corner-sink lower bound: all short and elementary, and the only thing here that would
otherwise rest on a hand proof. (b) **Other n**: hexagon-like completions without D₃d symmetry (S₃, C₃), other central
surfaces, even n; settle n = 8, 9, 11; and an interpolation lemma from n = 2^k − 3 to nearby n (the naive restriction of the
power-of-2 sets fails, see above, but these sets are very different, so it is not ruled out). The
proof shows what to vary: the hexagon wave handles everything but six triangles, and the triangle is a 2D 3-neighbour
problem, so any family of triangle solutions with "hypotenuse infected, ℓ ≤ distance to it" gives a cube. (c) **d ≥ 4**: the
structure theorem and T ≥ d(n−1)/2 hold; look for the analogue of the hexagon (the slice Σu = 0 plus fixers on its faces)
with solvers generalised to d = 4, 5.

### Reproduce

`python3 sage/exhaustive_m3_3.py` (18 s); `python3 sage/test_exact.py` (13 s), `python3 sage/test_search.py`
(30 s), `python3 sage/test_gadget.py` (13 s); `python3 sage/best_sets.py` (a few minutes; writes
`notes/best-sets-d3.json`); the family: `python3 sage/gadget.py verify 5 13 29 61 125 253` (about 1 min, two
simulators), `python3 sage/gadget.py local 5 13 29 61 125 253 509 1021` (20 s, the proof's local condition),
`python3 sage/gadget.py family13` (1 min), `python3 sage/hexagon.py 5 13 29 --face --count 200`, the scan
`python3 sage/hexagon.py 3 5 7 9 11 13 15 17 19 21 23 25 27 29 31 33 35 37 39 41 --face` (about 30 s),
`python3 sage/gadget.py table 5 13 29 61 125 253 --out notes/family-comparison.csv` (4 min) and the figures
`~/miniforge3/envs/sage/bin/python sage/plot_family.py`, `plot_best.py`; the window search
`python3 sage/hexagon.py 13 --seconds 60`; `python3 sage/embed.py restrict --n 5 7 11` and `embed.py boxes`; annealing
runs, e.g. `python3 sage/search.py 7 --start best-class --corner --temp 0.2`. C code is compiled on demand into the
system temp directory (`cc`, no other dependencies). Needs numpy only (matplotlib for the figures).
