import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.RangeCapturing
import ProofBench.PROBLEMS.P029.P029
import ProofBench.PROBLEMS.P035.P035

/- ==============================================================================
P032 — Shallow hitting sets for bottomless rectangles
(Planken & Ueckerdt, arXiv:2310.19982, Theorem 14).

Shared definitions live in
`ProofBench.Mathlib.Combinatorics.Hypergraph.RangeCapturing`.  The linear
polychromatic bound below combines this sheet's Theorem 14 with the reduction
Lemma 3 (P029) and bottomless shrinkability (P035).
============================================================================== -/

open Finset

namespace RangeCapturing

/-- **Theorem 14** (bottomless rectangles in `ℝ²`).  Every `H(V, R_BL, m)` admits
a `10`-shallow hitting set. -/
theorem P032 :
    ∀ m : ℕ, HasUniformShallowHittingSets bottomlessRectangles m 10 := by
  sorry

/-- `m_{R_BL}(k) ≤ 10(k-1)+1`: Theorem 14 + Lemma 3. -/
theorem bottomless_polychromatic (k : ℕ) (hk : 1 ≤ k) :
    polychromaticParameter bottomlessRectangles k ≤ 10 * (k - 1) + 1 :=
  lemma3_polychromaticParameter_le bottomlessRectangles 10 k hk
    P035 (fun m _ => P032 m)

end RangeCapturing
