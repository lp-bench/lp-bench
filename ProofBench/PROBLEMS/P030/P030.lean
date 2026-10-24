import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.RangeCapturing

open Finset

namespace RangeCapturing

/-- Theorem 26 of Planken–Ueckerdt, arXiv:2310.19982: unit-height rectangles admit
`63`-shallow hitting sets at every uniformity `m ≥ 1`, and `m_{R_UH}(k) ≤ 12k - 7`. -/
theorem P030 (k : ℕ) (hk : 1 ≤ k) :
    (∀ m : ℕ, 1 ≤ m → HasUniformShallowHittingSets unitHeightRectangles m 63) ∧
    polychromaticParameter unitHeightRectangles k ≤ 12 * k - 7 := by
  sorry

end RangeCapturing
