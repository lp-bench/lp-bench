import ProofBench.Mathlib_Problems.Combinatorics.Words.Pattern

open Pattern

/-- **Bounded avoidability index of patterns** (Currie's question, WORDS 2003): every
avoidable pattern is `5`-avoidable — equivalently, no pattern is `6`-avoidable but not
`5`-avoidable.  Avoidable patterns are characterised by Zimin's theorem; every avoidable
binary pattern is `3`-avoidable (Cassaigne, Roth), every doubled pattern is
`3`-avoidable (Ochem), and Clark exhibited a pattern of avoidability index exactly `5`,
so `5` cannot be lowered.  Whether the index is bounded at all is open. -/
theorem P075 :
    ∀ (m : ℕ) (p : List (Fin m)), IsAvoidable p → IsKAvoidable p 5 := by
  sorry
