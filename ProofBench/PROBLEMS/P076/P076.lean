import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-- **Conway's 99-graph problem**: is there a strongly regular graph with parameters
`(99, 14, 1, 2)` — a `14`-regular graph on `99` vertices in which adjacent vertices
have exactly one common neighbour and non-adjacent vertices exactly two?  The
parameters pass every known feasibility condition (eigenvalues `3` and `-4` with
multiplicities `54` and `44`, the Krein and absolute bounds); each vertex neighbourhood
would be a perfect matching `7 K₂`, so every edge lies in a unique triangle.  Conway
offered `$1000` for a resolution; the problem is open. -/
theorem P076 :
    ∃ (G : SimpleGraph (Fin 99)) (_ : DecidableRel G.Adj), G.IsSRGWith 99 14 1 2 := by
  sorry
