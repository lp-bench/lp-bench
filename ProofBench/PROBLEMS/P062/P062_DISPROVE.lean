import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.Flow

open Multigraph

universe u v

/-- Disproof polarity of Tutte's 5-flow conjecture: some bridgeless
multigraph has no nowhere-zero `ZMod 5`-flow. -/
theorem P062_disprove :
    ¬ ∀ (V : Type u) (E : Type v) [Fintype E] [DecidableEq V]
        (M : Multigraph V E),
        M.Bridgeless → ∃ f : E → ZMod 5, M.IsNowhereZeroFlow f := by
  sorry
