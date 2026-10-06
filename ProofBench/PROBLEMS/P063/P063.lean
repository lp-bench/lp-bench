import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.AverageDegree
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected

open SimpleGraph

universe u

/-- **Mader's connectivity conjecture** (1979): every finite simple graph of
average degree at least `3 * k - 1` contains a `(k + 1)`-connected subgraph.
The subgraph may be taken induced, since adding edges preserves vertex
connectivity.  Open for almost half a century; if true, the bound is sharp
for every value of the core connectivity. -/
theorem P063 :
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
      1 ≤ k → (3 * k - 1 : ℚ) ≤ G.averageDegree →
      ∃ s : Set V, (G.induce s).IsVertexConnected (k + 1) := by
  sorry
