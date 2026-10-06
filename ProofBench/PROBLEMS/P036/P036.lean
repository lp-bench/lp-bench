import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.RangeCapturing

/- ==============================================================================
P036 — Shrinkability of bottomless ∪ topless rectangles
(Planken & Ueckerdt, arXiv:2310.19982, §1.2).

============================================================================== -/

open Finset

namespace RangeCapturing

/- The family `R_BL ∪ R_TL` is **shrinkable**. -/
theorem P036 :
    Shrinkable (bottomlessRectangles ∪ toplessRectangles) := by
  sorry

end RangeCapturing
