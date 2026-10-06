import Mathlib.Combinatorics.SimpleGraph.Basic

/-- Erdős–Rényi–Sós: a nonempty finite graph in which every two distinct
vertices have exactly one common neighbour has a universal vertex. -/
theorem P092 {V : Type*} [Finite V] [Nonempty V] (G : SimpleGraph V)
    (h : ∀ u v, u ≠ v → ∃! w, G.Adj u w ∧ G.Adj v w) :
    ∃ c, ∀ v, v ≠ c → G.Adj c v := by
  sorry
