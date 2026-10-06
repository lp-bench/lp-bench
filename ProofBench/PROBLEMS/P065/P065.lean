import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Bounded

/-- **The Kahn–Kalai counterexample to Borsuk's conjecture** (1993).  Borsuk
conjectured that every bounded set in `d`-dimensional Euclidean space can be
covered by `d + 1` subsets of strictly smaller diameter.  The Kahn–Kalai
construction on balanced bipartitions of a `52`-element set yields a finite
set in the affine span of the cut vectors — dimension
`choose 52 2 - 1 = 1325` — on which every colouring with `1326` colours has
a monochromatic pair at the full diameter, so the colour classes cannot all
have smaller diameter.  Finiteness makes the set automatically bounded. -/
theorem P065 :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 1325)),
      0 < Metric.diam (S : Set (EuclideanSpace ℝ (Fin 1325))) ∧
        ∀ c : S → Fin 1326, ∃ x y : S, c x = c y ∧
          dist x y = Metric.diam (S : Set (EuclideanSpace ℝ (Fin 1325))) := by
  sorry
