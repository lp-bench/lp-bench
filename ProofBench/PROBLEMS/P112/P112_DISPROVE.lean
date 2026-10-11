import ProofBench.Mathlib_Problems.Combinatorics.Matroid.Intersection

/-- **Disprove version of P112.**  Some two tame matroids on a common ground set do not
satisfy intersection. -/
theorem P112_disprove :
    ¬ ∀ (α : Type) (M N : Matroid α), M.E = N.E → M.Tame → N.Tame →
      M.SatisfiesIntersection N := by
  sorry
