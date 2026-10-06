import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Reconstruction

universe u v

open SimpleGraph

/-- Negation of `P080`: two non-isomorphic finite simple graphs on at least three vertices
with the same deck. -/
theorem P080_disprove :
    ¬ (∀ {V : Type u} {V' : Type v} [Fintype V] (G : SimpleGraph V) (G' : SimpleGraph V'),
      3 ≤ Fintype.card V → G.SameDeck G' → Nonempty (G ≃g G')) := by
  sorry
