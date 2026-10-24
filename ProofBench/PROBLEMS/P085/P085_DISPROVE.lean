import Mathlib.Analysis.Normed.Group.AddCircle

/-- Negation of the Lonely Runner Conjecture `P085`: nonzero integer speeds for
which every time leaves some runner strictly closer than `1/(k+1)` to the
stationary runner. -/
theorem P085_disprove : ∃ (k : ℕ) (_ : 1 ≤ k) (v : Fin k → ℤ),
    (∀ i, v i ≠ 0) ∧ ∀ t : ℝ,
      ∃ i, ‖((t * v i : ℝ) : UnitAddCircle)‖ < (1 : ℝ) / (k + 1) := by
  sorry
