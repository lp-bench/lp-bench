import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.AverageDegree
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected

open SimpleGraph

universe u

/-- Disproof polarity of Mader's connectivity conjecture: some graph of
average degree at least `3 * k - 1` has no `(k + 1)`-connected subgraph. -/
theorem P063_disprove :
    ¬ ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (k : ℕ), 1 ≤ k → (3 * k - 1 : ℚ) ≤ G.averageDegree →
        ∃ s : Set V, (G.induce s).IsVertexConnected (k + 1) := by
  sorry
