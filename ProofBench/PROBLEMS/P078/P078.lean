import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

universe u

/-- **The Borodin–Kostochka conjecture** (1977): every finite simple graph with maximum
degree `Δ ≥ 9` satisfies `χ(G) ≤ max (Δ − 1) ω(G)`, where `ω(G)` is the clique number.
Brooks' theorem gives `χ(G) ≤ max Δ ω(G)` for `Δ ≥ 3`; the conjecture sharpens the
degree term by one once `Δ ≥ 9`, the threshold below which the Catlin graphs
(complements of cycles with all vertices multiplied) are counterexamples.  Reed proved
it for `Δ ≥ 10¹⁴`, and it is known for claw-free graphs; the threshold `9` is open. -/
theorem P078 : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    9 ≤ G.maxDegree → G.chromaticNumber ≤ max (G.maxDegree - 1) G.cliqueNum := by
  sorry
