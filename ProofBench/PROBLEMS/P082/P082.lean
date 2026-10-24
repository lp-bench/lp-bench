import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Pebbling

open SimpleGraph SimpleGraph.Pebbling

universe u v

/-- **Graham's graph-pebbling product conjecture** (stated in Chung 1989): for finite connected
graphs `G` and `H`, the pebbling number of the Cartesian product `G □ H` is at most the
product of the pebbling numbers. -/
theorem P082 : ∀ {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W),
    G.Connected → H.Connected →
      pebblingNumber (G □ H) ≤ pebblingNumber G * pebblingNumber H := by
  sorry
