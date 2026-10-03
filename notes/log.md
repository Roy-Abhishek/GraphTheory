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
