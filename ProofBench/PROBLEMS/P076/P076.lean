import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-- **Conway's 99-graph problem** (Conway, "Five $1,000 problems", 2014): there is a strongly
regular graph with parameters `(99, 14, 1, 2)`, i.e. a `14`-regular graph on `99` vertices in
which adjacent vertices have exactly one common neighbour and non-adjacent vertices exactly
two.  Open. -/
theorem P076 :
    ∃ (G : SimpleGraph (Fin 99)) (_ : DecidableRel G.Adj), G.IsSRGWith 99 14 1 2 := by
  sorry
