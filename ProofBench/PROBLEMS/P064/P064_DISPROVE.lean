import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.EdgeColoring

open Multigraph

universe u v

/-- Disproof polarity of the Berge–Fulkerson conjecture: some bridgeless
cubic multigraph has no six perfect matchings covering every edge exactly
twice. -/
theorem P064_disprove :
    ¬ ∀ (V : Type u) (E : Type v) [Fintype E] [DecidableEq V] [DecidableEq E]
        (M : Multigraph V E),
        (∀ e, ¬M.IsLoop e) → M.IsRegular 3 → M.Bridgeless →
        ∃ P : Fin 6 → Finset E, (∀ i, M.IsPerfectMatchingSet (P i)) ∧
          ∀ e : E, (Finset.univ.filter fun i => e ∈ P i).card = 2 := by
  sorry
