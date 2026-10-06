import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Reconstruction

universe u v

open SimpleGraph

/-- **The reconstruction conjecture** (Kelly 1957, Ulam 1960).  Two finite simple graphs on at
least three vertices with the same deck — a bijection between their vertex sets pairing
every vertex-deleted subgraph `G - v` with an isomorphic vertex-deleted subgraph of the other
graph (multiplicities retained, the card isomorphisms independent of each other) — are
isomorphic. -/
theorem P080 : ∀ {V : Type u} {V' : Type v} [Fintype V] (G : SimpleGraph V) (G' : SimpleGraph V'),
    3 ≤ Fintype.card V → G.SameDeck G' → Nonempty (G ≃g G') := by
  sorry
