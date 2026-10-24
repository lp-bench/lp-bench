import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.EdgeColoring

open Multigraph

universe u v

/-- **The Berge–Fulkerson conjecture** (Fulkerson 1971): every bridgeless cubic
multigraph (loopless and `3`-regular) has six perfect matchings that together
cover every edge exactly twice. -/
theorem P064 :
    ∀ (V : Type u) (E : Type v) [Fintype E] [DecidableEq V] [DecidableEq E]
      (M : Multigraph V E),
      (∀ e, ¬M.IsLoop e) → M.IsRegular 3 → M.Bridgeless →
      ∃ P : Fin 6 → Finset E, (∀ i, M.IsPerfectMatchingSet (P i)) ∧
        ∀ e : E, (Finset.univ.filter fun i => e ∈ P i).card = 2 := by
  sorry
