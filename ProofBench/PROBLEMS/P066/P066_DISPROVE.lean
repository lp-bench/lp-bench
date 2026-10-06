/-
Prove-or-disprove companion for the tangle-decider conjecture.  A
counterexample must have order at least four: orders at most three are
known to be induced by vertex sets.  The finite-reduction theorem encoded
in `P066_UB_1` further implies that a counterexample of any fixed order has
one on a connected graph whose size is bounded solely by that order.
-/
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Tangle

open SimpleGraph

universe u

/-- Disproof polarity: some finite graph has a tangle that no vertex set
decides by majority vote. -/
theorem P066_disprove :
    ¬ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (k : ℕ) (τ : G.Tangle k),
      ∃ X : Finset V, τ.IsDecidedBy X := by
  sorry
