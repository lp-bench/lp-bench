import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-- **The 57-regular Moore graph problem** (Hoffman–Singleton): is there a Moore graph
of degree `57`, i.e. a `57`-regular graph of diameter `2` and girth `5`?  Such a graph
would have `1 + 57 + 57 · 56 = 3250` vertices and would be strongly regular with
parameters `(3250, 57, 0, 1)`: adjacent vertices have no common neighbour and
non-adjacent vertices exactly one (`P077_LB_2`, `P077_UB_2`).  Hoffman and Singleton
showed that Moore graphs of diameter `2` exist only for degrees `2`, `3`, `7` and
possibly `57`; the pentagon, the Petersen graph and the Hoffman–Singleton graph realise
the first three, and the case `57` is open. -/
theorem P077 :
    ∃ (G : SimpleGraph (Fin 3250)) (_ : DecidableRel G.Adj), G.IsSRGWith 3250 57 0 1 := by
  sorry
