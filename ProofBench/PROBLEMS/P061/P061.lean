import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.EdgeColoring

open Multigraph

universe u v

/-- **Seymour's exact edge-colouring conjecture for planar multigraphs**
(1970s): every `d`-regular planar multigraph without loops in which every
odd vertex set is crossed by at least `d` edges is `d`-edge-colourable.
The case `d = 3` is equivalent to the Four Colour Theorem (Tait); the cases
`d = 4, 5` are due to Guenin, `d = 6` to Dvořák–Kawarabayashi–Král', and
`d = 7, 8` to Chudnovsky–Edwards–Kawarabayashi–Seymour; the conjecture is
open for every `d ≥ 9`. -/
theorem P061 :
    ∀ (d : ℕ) (V : Type u) (E : Type v) [Fintype V] [Fintype E]
      [DecidableEq V] (M : Multigraph V E),
      (∀ e, ¬M.IsLoop e) → M.IsRegular d → M.OddlyEdgeConnected d →
        M.IsPlanar → M.EdgeColorable d := by
  sorry
