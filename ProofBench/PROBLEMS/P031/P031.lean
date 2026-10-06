import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.RangeCapturing
import ProofBench.PROBLEMS.P029.P029
import ProofBench.PROBLEMS.P034.P034

/- ==============================================================================
P031 — Shallow hitting sets for axis-aligned strips
(Planken & Ueckerdt, arXiv:2310.19982, Theorem 5).

Shared definitions live in
`ProofBench.Mathlib.Combinatorics.Hypergraph.RangeCapturing`.  The linear
polychromatic bound below is the mechanical payoff, combining this sheet's
Theorem 5 with the reduction Lemma 3 (P029) and strip shrinkability (P034).
============================================================================== -/

open Finset

namespace RangeCapturing

/- **Theorem 5** (axis-aligned strips in `ℝ^d`).  There is a constant `t = t(d)`
(the paper gives `t(d) = 3ed(1+o(1))`) such that for every uniformity `m`, every
strip hypergraph on a finite point set admits a `t`-shallow hitting set. -/
theorem P031 (d : ℕ) :
    ∃ t : ℕ, ∀ m : ℕ, HasUniformShallowHittingSets (stripFamily d) m t := by
  sorry

/-- `m_{R_ST}(k) = O_d(k)` for axis-aligned strips: Theorem 5 + Lemma 3. -/
theorem strips_polychromatic_linear (d : ℕ) :
    ∃ t : ℕ, ∀ k : ℕ, 1 ≤ k →
      polychromaticParameter (stripFamily d) k ≤ t * (k - 1) + 1 := by
  obtain ⟨t, ht⟩ := P031 d
  exact ⟨t, fun k hk =>
    lemma3_polychromaticParameter_le (stripFamily d) t k hk
      (P034 d) (fun m _ => ht m)⟩

end RangeCapturing
