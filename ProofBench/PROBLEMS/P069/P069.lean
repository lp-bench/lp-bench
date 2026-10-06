import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.TokenGraph

open TokenGraph

universe u

/-- **The token-graph spectral-gap theorem.**  The algebraic connectivity of
the `k`-token graph equals that of the original graph. -/
theorem P069 (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (hk₀ : 1 ≤ k) (hkV : k < Fintype.card V) :
    algebraicConnectivity (tokenGraph G k) = algebraicConnectivity G := by
  sorry
