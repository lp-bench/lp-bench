import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-- Disproof polarity of the 57-regular Moore graph problem: no strongly regular graph
with parameters `(3250, 57, 0, 1)` exists.  The automorphism group of such a graph would
have order at most `375` (Mačaj–Širáň 2010). -/
theorem P077_disprove :
    ¬ ∃ (G : SimpleGraph (Fin 3250)) (_ : DecidableRel G.Adj), G.IsSRGWith 3250 57 0 1 := by
  sorry
