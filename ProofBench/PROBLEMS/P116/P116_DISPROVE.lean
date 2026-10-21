import ProofBench.PROBLEMS.P116.P116

/-- **Disprove version of P116.**  The negation of the shrinking-bracket
family: for some `r`, no pair `d₁ d₂` within `(4 - √2) * 0.96^r` of each other
eventually brackets `ramseyNumber t` between `d₁^t` and `d₂^t`.

The underlying growth-rate question is open, so this statement's truth value
is genuinely unknown: proving it refutes the conjecture. -/
theorem P116_disprove :
    ¬ ∀ r : ℕ, ∃ d₁ d₂ : ℝ, 0 ≤ d₁ ∧ 0 ≤ d₂ ∧ |d₁ - d₂| ≤ (4 - √2) * (0.96 : ℝ) ^ r ∧
      ∃ T, ∀ t ≥ T, d₁ ^ t ≤ ramseyNumber t ∧ ramseyNumber t ≤ d₂ ^ t := by
  sorry
