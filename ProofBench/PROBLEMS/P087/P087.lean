import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.CycleDoubleCover
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

open Multigraph

/-- Galvin's theorem: a finite loopless bipartite multigraph of maximum
degree at most `d` can be edge-coloured from any lists of at least `d` colours. -/
theorem P087 {V E C : Type*} [Finite V] [Fintype E]
    [DecidableEq V] (d : ℕ) (M : Multigraph V E)
    (hloop : ∀ e, ¬M.IsLoop e) (hbi : M.toSimpleGraph.Colorable 2)
    (hdegree : ∀ v, (M.incidenceFinset v).card ≤ d)
    (L : E → Finset C) (hL : ∀ e, d ≤ (L e).card) :
    ∃ c : E → C, (∀ e, c e ∈ L e) ∧
      ∀ v, Set.InjOn c ↑(M.incidenceFinset v) := by
  sorry
