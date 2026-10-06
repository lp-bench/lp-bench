import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.RangeCapturing

/- ==============================================================================
P030 — Polychromatic colorings for unit-height rectangles
(Planken & Ueckerdt, arXiv:2310.19982, Theorem 26).

Shared definitions live in
`ProofBench.Mathlib.Combinatorics.Hypergraph.RangeCapturing` (imported
above).  This sheet states the difficult result for `R_UH`.
============================================================================== -/

open Finset

namespace RangeCapturing

/- **Theorem 26** (polychromatic consequence).  For unit-height rectangles,
`m_{R_UH}(k) ≤ 12k - 7`.  (In the paper this is sharper than the `63`-shallow
hitting set alone gives, via `m_{R_UH}(k) ≤ 2·m_{R_BL∪R_TL}(k) - 1`.) -/
theorem P030 (k : ℕ) (hk : 1 ≤ k) :
    ∀ m : ℕ, HasUniformShallowHittingSets unitHeightRectangles m 63 ∧
    polychromaticParameter unitHeightRectangles k ≤ 12 * k - 7 := by
  sorry

end RangeCapturing
