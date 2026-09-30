# Problem: Question 7 — Przykucki & Shelton, EJC 27(4) (2020), #P4.34

Source: "Smallest Percolating Sets in Bootstrap Percolation on Grids." DOI: 10.37236/9582.
**Use this file for the exact statements. Only open the PDF in refs/ when you need to double-check
wording or pull a proof detail — reading it costs a lot more tokens than reading this.**
Do not confuse with arXiv:1907.01940 (2019 preprint) — that version has different question numbers
and is missing the power-of-2 construction below. The EJC version (this one) is authoritative.

## Definitions

- Bootstrap percolation on graph G, threshold r: A_0 = A; A_t = A_{t-1} ∪ {u : |N(u) ∩ A_{t-1}| ≥ r}.
  Percolates if every vertex eventually infected.
- [n]^d: d-dim grid graph, vertex set {1,...,n}^d, u~v iff differ by 1 in exactly one coordinate.
- G_{d,r}(n): size of smallest percolating sets in r-neighbour bootstrap percolation on [n]^d.
- T(A): percolation time of set A (number of rounds to infect everything).
- m_d(n) := min{ T(A) : A percolates [n]^d, |A| = n^{d-1} }  — minimum percolation time
  achievable by an optimally-SIZED percolating set. **This is the target quantity.**

## Established results

- **Theorem 1.** G_{d,d}(n) = n^{d-1} for all n, d. Proved via a canonical set
  A_d = ⋃_{i=1}^d V_{in}, where V_k = {v ∈ [n]^d : Σv_i = k}, and "infection witness trees."
- **Theorem 2.** m_1(n) = ⌈n/2⌉, m_2(n) = n−1 exactly. For d ≥ 3:
  dn/2 + O(1) ≤ m_d(n) ≤ (d+2)n² + n.
- **Power-of-2 construction (published version only — not in 2019 preprint).** For n = 2^p:
  m_d(2^p) ≤ d·2^p = dn — LINEAR, not quadratic. Recursive: split [2^p]^d into 2^d subcubes
  ≅ [2^{p-1}]^d ("even"/"odd" by parity of subcube index). Infect even subcubes recursively
  (time ≤ d·2^{p-1} each, running in parallel), then odd subcubes infect outward in diagonal
  layers (another ≤ d·2^{p-1} steps). Base case p=1: the two smallest percolating sets of [2]^d
  are {even coordinate-sum} and {odd coordinate-sum} vertices.
- Authors do NOT believe canonical A_d is time-optimal in general; a shifted set
  A'_d = ⋃_{i=1}^d V_{in−⌊n/2⌋} empirically does better (n≤50 simulations), and percolation
  time "can be beaten significantly" for some n (credited to A. Nicholas Day) — suggesting the
  Ω(n) lower bound might be tight for ALL n, not just powers of 2.

## THE OPEN PROBLEM — Question 7

> Is m_d(n) = o(n²) for all d ≥ 3?

Authors "expect the answer to be positive." Open for general n; only resolved (as O(n), which is
stronger than o(n²)) for n = 2^p via the construction above.
Paper's own hint, stated immediately before posing the question: "the argument could most likely
be generalised to other values of n, e.g., to prime powers. However, it is not immediately obvious
to us how to make it work for general n."

**Not the target, but related — Question 8** (companion, same paper): exact value of m(𝕋_n^d)
(torus case) for d ≥ 3. Jeger & Zehmakan (Discrete Applied Mathematics, 262:116–126, 2019) already
showed m(𝕋_n^d) = n^{d-1} + O(n^{d-2}); only the lower-order term is still open. Background only.

## Proposed lines of attack (starting points, not a solution)

1. Generalize the recursive even/odd-subcube construction from base 2 to other bases (paper
   suggests prime powers first).
2. Padding/reduction: embed [n]^d into [N]^d for the next N with a known fast construction
   (e.g. next power of 2), run it there, adapt back down to [n]^d — check the adaptation doesn't
   reintroduce quadratic blowup.
3. Reuse existing machinery: perimeter argument (lower bounds) and infection-witness-tree /
   potential-function h(u)=Σu_i² argument (Theorem 2's upper bound) — likely need either a
   sharper witness-tree bound for a smarter initial set, or a fully explicit generalized
   construction.
4. Fallback honest partial result: o(n²) (or O(n)) for a restricted infinite family of n
   (e.g. all prime powers) + strong computational evidence for general n.

## References

- Przykucki, Shelton. Smallest Percolating Sets in Bootstrap Percolation on Grids. EJC 27(4)
  (2020), #P4.34. — PRIMARY SOURCE
- Jeger, Zehmakan. Dynamic monopolies in two-way bootstrap percolation. Discrete Applied
  Mathematics, 262:116–126, 2019.
- Benevides, Przykucki. On slowly percolating sets of minimal size in bootstrap percolation.
  EJC 20(2) (2013), #P46.
- Benevides, Przykucki. Maximum percolation time in two-dimensional bootstrap percolation.
  SIAM J. Discrete Math, 29:224–251, 2015.
- Morris. Minimal percolating sets in bootstrap percolation. EJC 16(1) (2009), #R2.
- Morrison, Noel. Extremal bounds for bootstrap percolation in the hypercube. J. Combin. Theory
  Ser. A, 156:61–84, 2018.
