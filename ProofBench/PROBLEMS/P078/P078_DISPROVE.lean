import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

universe u

/-- Disproof polarity of the Borodin–Kostochka conjecture: some finite graph with
maximum degree at least `9` has chromatic number exceeding `max (Δ − 1) ω`.  The
conjecture holds for `Δ ≥ 10¹⁴` (Reed 1999) and for claw-free graphs. -/
theorem P078_disprove :
    ¬ ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      9 ≤ G.maxDegree → G.chromaticNumber ≤ max (G.maxDegree - 1) G.cliqueNum := by
  sorry
