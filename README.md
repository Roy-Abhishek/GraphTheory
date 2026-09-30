# Bootstrap Percolation on Grids — Question 7

MATH 179 (Graph Theory) final project. The goal is to work on Question 7 from
Przykucki & Shelton, *Smallest Percolating Sets in Bootstrap Percolation on Grids*,
EJC 27(4) (2020), #P4.34 ([DOI: 10.37236/9582](https://doi.org/10.37236/9582)).

## The problem

In *r*-neighbour bootstrap percolation on a graph *G*, a vertex becomes infected once at least
*r* of its neighbours are infected. An initial set percolates if every vertex eventually
becomes infected. On the grid [n]^d with r = d, the smallest percolating sets have exactly
n^(d−1) vertices (Theorem 1).

Let **m_d(n)** be the smallest percolation time achievable by a percolating set of that
minimum size.

> **Question 7.** Is m_d(n) = o(n²) for all d ≥ 3?

What is known:
- m_1(n) = ⌈n/2⌉ and m_2(n) = n − 1.
- For d ≥ 3: dn/2 + O(1) ≤ m_d(n) ≤ (d+2)n² + n.
- For n = 2^p, a recursive even/odd-subcube construction gives m_d(n) ≤ dn, so the answer
  is yes for powers of 2. The case of general n is open.

The authors expect the answer to be positive, and they suggest that the construction might
extend to prime powers.

## Approaches

1. Extend the recursive subcube construction from base 2 to other bases, starting with
   prime powers.
2. Pad [n]^d into [N]^d for an N where a fast construction is known, then adapt the result
   back to [n]^d.
3. Sharpen the infection-witness-tree and potential-function arguments from the paper.
4. Fallback: prove the result for an infinite family of n, and give computational evidence
   for general n.

## Repository layout

```
lean/    Lean 4 + Mathlib package (BootstrapPercolation)
sage/    SageMath experiments and simulations
notes/   working notes
refs/    problem statement and references (see refs/code-context.md)
```

## Building

```bash
cd lean && lake build
```

## Main reference

M. Przykucki, T. Shelton. Smallest Percolating Sets in Bootstrap Percolation on Grids.
*Electron. J. Combin.* 27(4) (2020), #P4.34. Use this published version, not the 2019 arXiv
preprint (arXiv:1907.01940), which numbers its questions differently and does not include
the power-of-2 construction.

Other references are listed in [refs/code-context.md](refs/code-context.md).
