import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.RangeCapturing

open Finset

namespace RangeCapturing

/-- The family `R_ST` of axis-aligned strips in `ℝ^d` is shrinkable: for `m ≥ 1`, every
hyperedge of `H(V, R_ST, m)` contains a hyperedge of `H(V, R_ST, m-1)` (remark after
Lemma 3 of Planken–Ueckerdt, arXiv:2310.19982). -/
theorem P034 (d : ℕ) : Shrinkable (stripFamily d) := by
  sorry

end RangeCapturing
