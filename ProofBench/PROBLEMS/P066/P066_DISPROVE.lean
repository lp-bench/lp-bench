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
