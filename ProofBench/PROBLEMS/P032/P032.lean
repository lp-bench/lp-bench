import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.RangeCapturing

open Finset

namespace RangeCapturing

/-- Theorem 14 of Planken–Ueckerdt, arXiv:2310.19982: for every uniformity `m ≥ 1`, every
bottomless-rectangle hypergraph `H(V, R_BL, m)` has a `10`-shallow hitting set. -/
theorem P032 :
    ∀ m : ℕ, 1 ≤ m → HasUniformShallowHittingSets bottomlessRectangles m 10 := by
  sorry

end RangeCapturing
