import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.RangeCapturing

open Finset

namespace RangeCapturing

/-- Theorem 25 of Planken–Ueckerdt, arXiv:2310.19982: for every uniformity `m ≥ 1`, every
hypergraph `H(V, R_BL ∪ R_TL, m)` of bottomless and topless rectangles has a `21`-shallow
hitting set. -/
theorem P033 :
    ∀ m : ℕ, 1 ≤ m →
      HasUniformShallowHittingSets (bottomlessRectangles ∪ toplessRectangles) m 21 := by
  sorry

end RangeCapturing
