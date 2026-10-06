import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Pebbling

open SimpleGraph SimpleGraph.Pebbling

universe u v

/-- Disproof polarity: finite connected factors whose Cartesian product
has pebbling number greater than the proposed bound. -/
theorem P082_disprove : ∃ (V : Type u) (W : Type v) (_ : Fintype V) (_ : Fintype W)
    (_ : DecidableEq V) (_ : DecidableEq W) (G : SimpleGraph V) (H : SimpleGraph W),
    G.Connected ∧ H.Connected ∧
      pebblingNumber G * pebblingNumber H < pebblingNumber (G □ H) := by
  sorry
