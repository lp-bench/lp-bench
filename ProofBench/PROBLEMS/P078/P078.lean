import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

universe u

/-- **The Borodin–Kostochka conjecture** (Borodin–Kostochka 1977): every finite simple graph
with maximum degree `Δ ≥ 9` satisfies `χ(G) ≤ max (Δ − 1) ω(G)`, where `ω(G)` is the clique
number.  Reed (1999) proved it for `Δ ≥ 10¹⁴`. -/
theorem P078 : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    9 ≤ G.maxDegree → G.chromaticNumber ≤ max (G.maxDegree - 1) G.cliqueNum := by
  sorry
