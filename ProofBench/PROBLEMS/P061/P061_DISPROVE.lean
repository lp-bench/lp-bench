import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.EdgeColoring

open Multigraph

universe u v

/-- Disproof polarity of Seymour's exact conjecture: some `d`-regular oddly
`d`-edge-connected planar loopless multigraph is not `d`-edge-colourable. -/
theorem P061_disprove :
    ¬ ∀ (d : ℕ) (V : Type u) (E : Type v) [Fintype V] [Fintype E]
        [DecidableEq V] (M : Multigraph V E),
        (∀ e, ¬M.IsLoop e) → M.IsRegular d → M.OddlyEdgeConnected d →
          M.IsPlanar → M.EdgeColorable d := by
  sorry
