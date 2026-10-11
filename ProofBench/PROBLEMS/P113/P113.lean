import ProofBench.Mathlib_Problems.Combinatorics.Matroid.Intersection

/-- **Matroid intersection for tame matroids on a countable ground set.**  Any two tame
matroids on a common countable ground set satisfy intersection. -/
theorem P113 {α : Type*} (M N : Matroid α) (hE : M.E = N.E) (hc : M.E.Countable)
    (hM : M.Tame) (hN : N.Tame) : M.SatisfiesIntersection N := by
  sorry
