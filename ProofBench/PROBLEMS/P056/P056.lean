import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.CycleDoubleCover
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Multigraph

universe u v

/-- There are `c > 0` and `n₀` such that every simple `3`-connected cubic graph
of girth at least `16` on `n ≥ n₀` vertices has at least `2 ^ (c n)` circuit
double covers. Theorem 1.8 of Hušek–Šámal, arXiv:2607.24724. -/
theorem P056 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {V : Type u} {E : Type v} [Fintype V] [Fintype E]
        [DecidableEq V] [DecidableEq E] (G : Multigraph V E),
        G.IsSimple → G.toSimpleGraph.IsRegularOfDegree 3 →
          G.toSimpleGraph.IsVertexConnected 3 → G.HasGirthAtLeast 16 →
            n₀ ≤ Fintype.card V →
              (2 : ℝ) ^ (c * Fintype.card V) ≤ G.circuitDoubleCovers.card := by
  sorry
