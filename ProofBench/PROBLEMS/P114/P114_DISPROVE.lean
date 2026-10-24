import ProofBench.Mathlib_Problems.Combinatorics.Matroid.Intersection

/-- **Disprove version of P114.**  Some two finitary matroids on a common ground set do
not satisfy intersection. -/
theorem P114_disprove :
    ¬ ∀ (α : Type) (M N : Matroid α) [M.Finitary] [N.Finitary], M.E = N.E →
      M.SatisfiesIntersection N := by
  sorry
