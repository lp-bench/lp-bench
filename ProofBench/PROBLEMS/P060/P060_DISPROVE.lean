import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Toughness

open SimpleGraph

universe u

/-- For every `t > 0` there is a `t`-tough non-Hamiltonian graph on at least
three vertices: the negation of Chvátal's toughness conjecture (Chvátal 1973). -/
theorem P060_disprove :
    ¬ ∃ t : ℝ, 0 < t ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        3 ≤ Fintype.card V → G.IsTough t → G.IsHamiltonian := by
  sorry
