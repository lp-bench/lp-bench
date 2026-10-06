import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Hypercube
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

open SimpleGraph Function

/-- Every properly edge-coloured nonempty finite subgraph `G` of a hypercube
contains a rainbow copy of every tree with at most `δ(G)` edges.
Copies preserve edges, but need not preserve nonedges. -/
theorem P086 {V W C : Type*} [Fintype V] [Nonempty V] [Fintype W]
    (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (ι : G →g H n) (hι : Injective ι) (c : G.lineGraph.Coloring C)
    (T : SimpleGraph W) [DecidableRel T.Adj]
    (hT : T.IsTree) (hsize : T.edgeFinset.card ≤ G.minDegree) :
    ∃ f : T →g G, Injective f ∧ Injective (c ∘ f.mapEdgeSet) := by
  sorry
