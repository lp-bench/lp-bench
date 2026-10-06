import Mathlib.Analysis.Normed.Group.AddCircle

/-- The integer-speed Lonely Runner Conjecture: `k` nonzero speeds can
simultaneously be at least `1/(k+1)` from the stationary runner.
The norm on `UnitAddCircle` is distance to the nearest integer. -/
theorem P085 (k : ℕ) (hk : 1 ≤ k) (v : Fin k → ℤ) (hv : ∀ i, v i ≠ 0) :
    ∃ t : ℝ, ∀ i, (1 : ℝ) / (k + 1) ≤ ‖((t * v i : ℝ) : UnitAddCircle)‖ := by
  sorry
