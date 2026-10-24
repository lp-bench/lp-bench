import ProofBench.PROBLEMS.P010.P010

universe u

/-- **Disprove version of P010**: some countable graph has no unfriendly partition. -/
theorem P010_disprove :
    ¬ ∀ (V : Type u) [Countable V] (G : SimpleGraph V), UPConj G := sorry
