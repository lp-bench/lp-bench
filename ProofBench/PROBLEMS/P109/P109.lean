import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Interval.Finset.Nat

open SimpleGraph Finset

/-- **Two Vertices of Equal Degree.** Two vertices of a finite simple graph on at least two
vertices have the same degree. -/
theorem P109 {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : 2 ≤ Fintype.card V) :
    ∃ u v, u ≠ v ∧ G.degree u = G.degree v := by
  sorry
