import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-- Disproof polarity of Conway's 99-graph problem: no strongly regular graph with
parameters `(99, 14, 1, 2)` exists.  The parameters pass all known feasibility conditions. -/
theorem P076_disprove :
    ¬ ∃ (G : SimpleGraph (Fin 99)) (_ : DecidableRel G.Adj), G.IsSRGWith 99 14 1 2 := by
  sorry
