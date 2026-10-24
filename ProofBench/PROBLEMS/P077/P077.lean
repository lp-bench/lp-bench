import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-- **The 57-regular Moore graph problem** (Hoffman–Singleton 1960): there is a strongly regular
graph with parameters `(3250, 57, 0, 1)`, i.e. a Moore graph of degree `57` and diameter `2`
(a `57`-regular graph of diameter `2` and girth `5`).  Such Moore graphs exist for degrees `2`,
`3` and `7`, and only `57` remains open. -/
theorem P077 :
    ∃ (G : SimpleGraph (Fin 3250)) (_ : DecidableRel G.Adj), G.IsSRGWith 3250 57 0 1 := by
  sorry
