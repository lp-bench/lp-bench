import ProofBench.Mathlib_Problems.Combinatorics.Words.Pattern

open Pattern

/-- Disproof polarity: some avoidable pattern is not `5`-avoidable.  Every avoidable binary
pattern and every doubled pattern is known to be `3`-avoidable. -/
theorem P075_disprove :
    ¬ ∀ (m : ℕ) (p : List (Fin m)), IsAvoidable p → IsKAvoidable p 5 := by
  sorry
