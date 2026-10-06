import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.LineGraph

open SimpleGraph

variable {V : Type}

/-- The edge chromatic number `χ′(G)`: the chromatic number of the line graph
of `G`.  The line graph is Mathlib's `SimpleGraph.lineGraph` (vertices are the
edges of `G`; two distinct edges are adjacent iff they share an endpoint). -/
noncomputable def edgeChromaticNumber (G : SimpleGraph V) : ℕ∞ :=
  G.lineGraph.chromaticNumber

/-- **Vizing's theorem** (1964) -/
theorem P011 [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeChromaticNumber G ≤ G.maxDegree + 1 := sorry
