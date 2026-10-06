import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.RangeCapturing
import ProofBench.PROBLEMS.P029.P029
import ProofBench.PROBLEMS.P036.P036

/- ==============================================================================
P033 — Shallow hitting sets for bottomless ∪ topless rectangles
(Planken & Ueckerdt, arXiv:2310.19982, Theorem 25).

Shared definitions live in
`ProofBench.Mathlib.Combinatorics.Hypergraph.RangeCapturing`.  The linear
polychromatic bound below combines this sheet's Theorem 25 with the reduction
Lemma 3 (P029) and shrinkability of `R_BL ∪ R_TL` (P036).
============================================================================== -/

open Finset

namespace RangeCapturing

/-- **Theorem 25** (bottomless ∪ topless rectangles in `ℝ²`).  Every
`H(V, R_BL ∪ R_TL, m)` admits a `21`-shallow hitting set. -/
theorem P033 :
    ∀ m : ℕ,
      HasUniformShallowHittingSets (bottomlessRectangles ∪ toplessRectangles) m 21 := by
  sorry

/-- `m_{R_BL∪R_TL}(k) ≤ 21(k-1)+1`: Theorem 25 + Lemma 3. -/
theorem bottomless_topless_polychromatic (k : ℕ) (hk : 1 ≤ k) :
    polychromaticParameter (bottomlessRectangles ∪ toplessRectangles) k
      ≤ 21 * (k - 1) + 1 :=
  lemma3_polychromaticParameter_le (bottomlessRectangles ∪ toplessRectangles) 21 k hk
    P036 (fun m _ => P033 m)

end RangeCapturing
