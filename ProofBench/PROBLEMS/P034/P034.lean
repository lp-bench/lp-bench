import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.RangeCapturing

/- ==============================================================================
P034 — Shrinkability of axis-aligned strips
(Planken & Ueckerdt, arXiv:2310.19982, §1.2).

Shared definitions live in
`ProofBench.Mathlib.Combinatorics.Hypergraph.RangeCapturing`.
============================================================================== -/

open Finset

namespace RangeCapturing

/- The strip family `R_ST` is **shrinkable**: every hyperedge of `H(V,R_ST,m)`
contains a hyperedge of `H(V,R_ST,m-1)`. -/
theorem P034 (d : ℕ) : Shrinkable (stripFamily d) := by
  sorry

end RangeCapturing
