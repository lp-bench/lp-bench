import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.CycleDoubleCover
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected

open Multigraph

/-- A `2`-connected, properly `3`-edge-coloured cubic graph on `n` vertices
has at least `2 ^ (n / 2 - 1)` circuit double covers. -/
theorem P055 {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : Multigraph V E)
    (hSimple : G.IsSimple)
    (hCubic : G.toSimpleGraph.IsRegularOfDegree 3)
    (hG : G.toSimpleGraph.IsVertexConnected 2) (c : G.ProperThreeEdgeColoring) :
    2 ^ (Fintype.card V / 2 - 1) ≤ G.circuitDoubleCovers.card := by
  sorry
