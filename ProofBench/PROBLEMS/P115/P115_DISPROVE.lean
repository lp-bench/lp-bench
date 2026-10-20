import ProofBench.Mathlib_Problems.Combinatorics.VanDerWaerden

open VanDerWaerden

/-- **Disprove version of P115.**  For some `k ≥ ℓ ≥ 2`, `w(k + 1, ℓ - 1) > w(k, ℓ)`. -/
theorem P115_disprove : ¬ ∀ k ℓ : ℕ, 2 ≤ ℓ → ℓ ≤ k → VdWConcavity k ℓ := by
  sorry
