import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Bounded

/-- **The Kahn–Kalai counterexample to Borsuk's conjecture** (Kahn–Kalai 1993):
some finite set of positive diameter in `ℝ^1325` cannot be split into `1326`
parts of smaller diameter, that is, every colouring with `1326` colours has a
monochromatic pair at distance equal to the diameter. -/
theorem P065 :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 1325)),
      0 < Metric.diam (S : Set (EuclideanSpace ℝ (Fin 1325))) ∧
        ∀ c : S → Fin 1326, ∃ x y : S, c x = c y ∧
          dist x y = Metric.diam (S : Set (EuclideanSpace ℝ (Fin 1325))) := by
  sorry
