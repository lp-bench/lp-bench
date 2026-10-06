import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Pebbling

open SimpleGraph SimpleGraph.Pebbling

universe u v

/-- **Graham's graph-pebbling product conjecture.** The pebbling number of
a Cartesian product is at most the product of the pebbling numbers. -/
theorem P082 : ∀ {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W),
    G.Connected → H.Connected →
      pebblingNumber (G □ H) ≤ pebblingNumber G * pebblingNumber H := by
  sorry
