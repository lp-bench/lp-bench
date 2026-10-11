import ProofBench.Mathlib_Problems.Combinatorics.Matroid.Intersection

/-- **Nash-Williams' matroid intersection conjecture.**  Any two finitary matroids on a common
ground set satisfy intersection. -/
theorem P114 {α : Type*} (M N : Matroid α) [M.Finitary] [N.Finitary] (hE : M.E = N.E) :
    M.SatisfiesIntersection N := by
  sorry
