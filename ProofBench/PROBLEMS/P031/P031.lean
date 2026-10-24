import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.RangeCapturing

open Finset

namespace RangeCapturing

/-- Theorem 5 of Planken–Ueckerdt, arXiv:2310.19982: for axis-aligned strips in `ℝ^d` there is
a constant `t = t(d)` such that, for every uniformity `m ≥ 1`, every `H(V, R_ST, m)` has a
`t`-shallow hitting set. -/
theorem P031 (d : ℕ) :
    ∃ t : ℕ, ∀ m : ℕ, 1 ≤ m → HasUniformShallowHittingSets (stripFamily d) m t := by
  sorry

end RangeCapturing
