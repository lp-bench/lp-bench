import ProofBench.Mathlib_Problems.Combinatorics.VanDerWaerden

open VanDerWaerden

/-- **Concavity of van der Waerden numbers** (Landman and Robertson).  For `k ≥ ℓ ≥ 2`, the
two-colour van der Waerden numbers satisfy `w(k, ℓ) ≥ w(k + 1, ℓ - 1)`. -/
theorem P115 {k ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hk : ℓ ≤ k) : VdWConcavity k ℓ := by
  sorry
