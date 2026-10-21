import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.RamseyNumber

def RamseyBracket : Prop :=
  ∀ (r : ℕ), ∃ d₁ d₂ : ℝ,
  0 ≤ d₁ ∧ 0 ≤ d₂ ∧ |d₁ - d₂| ≤ (4 - √2) * (0.96 : ℝ)^r ∧
    ∃ T, ∀ t ≥ T, d₁ ^ t ≤ ramseyNumber t ∧ ramseyNumber t ≤ d₂ ^ t

theorem P116 : RamseyBracket := sorry
