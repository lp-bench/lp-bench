import ProofBench.Mathlib_Problems.Combinatorics.Matroid.Intersection

/-- **Disprove version of P113.**  Some two tame matroids on a common countable ground set do
not satisfy intersection. -/
theorem P113_disprove :
    ¬ ∀ (α : Type) (M N : Matroid α), M.E = N.E → M.E.Countable → M.Tame → N.Tame →
      M.SatisfiesIntersection N := by
  sorry
