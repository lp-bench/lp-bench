import ProofBench.Mathlib_Problems.Combinatorics.Words.Pattern

open Pattern

/-- **Bounded avoidability index of patterns** (Currie's question, WORDS 2003; Currie 2005):
every avoidable pattern is `5`-avoidable.  The bound `5` cannot be lowered: Clark (2006)
found a pattern that is `5`-avoidable but not `4`-avoidable. -/
theorem P075 :
    ∀ (m : ℕ) (p : List (Fin m)), IsAvoidable p → IsKAvoidable p 5 := by
  sorry
