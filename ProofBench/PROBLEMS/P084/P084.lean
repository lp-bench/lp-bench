import Mathlib.Combinatorics.SimpleGraph.Acyclic

open SimpleGraph

/-- Cayley's formula: there are `n^(n-2)` unrooted labelled trees on `n`
vertices. The one-vertex tree is included, with natural subtraction. -/
theorem P084 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {G : SimpleGraph (Fin n) // G.IsTree} = n ^ (n - 2) := by
  sorry
