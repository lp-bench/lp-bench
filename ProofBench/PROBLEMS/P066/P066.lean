import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Tangle

open SimpleGraph

universe u

/-- **The tangle-decider conjecture** (Diestel–Hundertmark–Lemanczyk 2019):
every tangle in a finite graph is decided by majority vote by a set of
vertices. -/
theorem P066 :
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (k : ℕ) (τ : G.Tangle k),
      ∃ X : Finset V, τ.IsDecidedBy X := by
  sorry
