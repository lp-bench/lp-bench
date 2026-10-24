import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Reconstruction

universe u v

open SimpleGraph

/-- **The reconstruction conjecture** (Kelly 1957, Ulam 1960): two finite simple graphs on at
least three vertices with the same deck (`SimpleGraph.SameDeck`: a bijection of the vertex sets
pairing each vertex-deleted subgraph with an isomorphic one) are isomorphic. -/
theorem P080 : ∀ {V : Type u} {V' : Type v} [Fintype V] (G : SimpleGraph V) (G' : SimpleGraph V'),
    3 ≤ Fintype.card V → G.SameDeck G' → Nonempty (G ≃g G') := by
  sorry
