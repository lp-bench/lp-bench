import ProofBench.Mathlib_Problems.Combinatorics.Matroid.Intersection

/-- **Matroid intersection for tame matroids.**  Any two tame matroids on a common ground set
satisfy intersection. -/
theorem P112 {α : Type*} (M N : Matroid α) (hE : M.E = N.E) (hM : M.Tame) (hN : N.Tame) :
    M.SatisfiesIntersection N := by
  sorry
