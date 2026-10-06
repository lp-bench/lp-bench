import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.Flow

open Multigraph

universe u v

/-- **Tutte's 5-flow conjecture** (1954): every bridgeless multigraph has a
nowhere-zero 5-flow, stated here in the equivalent group-valued form with
values in `ZMod 5` (by Tutte's theorem, only the order of the group
matters).  Jaeger proved the 8-flow theorem and Seymour the 6-flow theorem;
5 would be best possible, as the Petersen graph has no nowhere-zero
4-flow. -/
theorem P062 :
    ∀ (V : Type u) (E : Type v) [Fintype E] [DecidableEq V]
      (M : Multigraph V E),
      M.Bridgeless → ∃ f : E → ZMod 5, M.IsNowhereZeroFlow f := by
  sorry
