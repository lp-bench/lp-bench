import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.EdgeColoring

open Multigraph

universe u v

/-- **Seymour's exact edge-colouring conjecture for planar multigraphs**
(Seymour, about 1973; Proc. London Math. Soc. 1979): every `d`-regular planar
loopless multigraph in which every odd vertex set is crossed by at least `d`
edges is `d`-edge-colourable.  Known for `d ≤ 8`, open for every `d ≥ 9`. -/
theorem P061 :
    ∀ (d : ℕ) (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] (M : Multigraph V E),
      (∀ e, ¬M.IsLoop e) → M.IsRegular d → M.OddlyEdgeConnected d →
        M.IsPlanar → M.EdgeColorable d := by
  sorry
