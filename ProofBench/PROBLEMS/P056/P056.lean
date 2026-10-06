import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.CycleDoubleCover
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Multigraph

universe u v

/-- A `3`-connected cubic graph of girth at least `16` on `n` vertices has
`2 ^ Ω(n)` circuit double covers (Hušek–Šámal, Theorem 1.8): one exponential
rate works for every sufficiently large such graph.  Unlike `P055`, no
`3`-edge-colorability is assumed, so this covers high-girth snarks — the
historically presumed hard case of the cycle double cover conjecture. -/
theorem P056 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {V : Type u} {E : Type v} [Fintype V] [Fintype E]
        [DecidableEq V] [DecidableEq E] (G : Multigraph V E),
        G.IsSimple → G.toSimpleGraph.IsRegularOfDegree 3 →
          G.toSimpleGraph.IsVertexConnected 3 → G.HasGirthAtLeast 16 →
            n₀ ≤ Fintype.card V →
              (2 : ℝ) ^ (c * Fintype.card V) ≤ G.circuitDoubleCovers.card := by
  sorry
