import Mathlib.Analysis.Normed.Group.AddCircle

/-- The Lonely Runner Conjecture for integer speeds (Wills 1967, Cusick 1973; survey
Perarnau–Serra, arXiv:2409.20160): `k` nonzero speeds can simultaneously be at
least `1/(k+1)` from the stationary runner. The norm on `UnitAddCircle` is the
distance to the nearest integer. -/
theorem P085 (k : ℕ) (hk : 1 ≤ k) (v : Fin k → ℤ) (hv : ∀ i, v i ≠ 0) :
    ∃ t : ℝ, ∀ i, (1 : ℝ) / (k + 1) ≤ ‖((t * v i : ℝ) : UnitAddCircle)‖ := by
  sorry
