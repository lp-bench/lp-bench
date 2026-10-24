import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.RangeCapturing

open Finset

namespace RangeCapturing

/-- The family `R_BL ∪ R_TL` of bottomless and topless rectangles in `ℝ²` is shrinkable
(remark after Lemma 3 of Planken–Ueckerdt, arXiv:2310.19982). -/
theorem P036 :
    Shrinkable (bottomlessRectangles ∪ toplessRectangles) := by
  sorry

end RangeCapturing
