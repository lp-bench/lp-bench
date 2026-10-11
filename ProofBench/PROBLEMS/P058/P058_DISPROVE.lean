import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.ChipFiring.Rank

/-- **Disprove version of P058.**  For some connected finite multigraph of genus `g` and some
nonnegative `r`, `d` with `ρ(g, r, d) ≥ 0`, no divisor of degree at most `d` has rank exactly
`r`. -/
theorem P058_disprove :
    ¬ ∀ G : CFGraph, graph_connected G → ∀ r d : ℤ, 0 ≤ r → 0 ≤ d →
      0 ≤ brillNoetherNumber (genus G) r d → ∃ D : CFDiv G, divisorRankEq G D r ∧ deg D ≤ d := by
  sorry
