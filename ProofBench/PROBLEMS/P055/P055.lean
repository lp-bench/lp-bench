import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.CycleDoubleCover
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected

open Multigraph

/-- A simple `2`-connected cubic graph on `n` vertices with a proper
`3`-edge-colouring has at least `2 ^ (n / 2 - 1)` circuit double covers.
Theorem 1.7 of Hušek–Šámal, arXiv:2607.24724. -/
theorem P055 {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : Multigraph V E)
    (hSimple : G.IsSimple)
    (hCubic : G.toSimpleGraph.IsRegularOfDegree 3)
    (hG : G.toSimpleGraph.IsVertexConnected 2) (c : G.ProperThreeEdgeColoring) :
    2 ^ (Fintype.card V / 2 - 1) ≤ G.circuitDoubleCovers.card := by
  sorry
