import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.ChipFiring.Rank

/-- For some connected finite loopless multigraph of genus `g` and some `r, d ≥ 0` with
`ρ(g, r, d) ≥ 0`, no divisor of degree at most `d` has rank exactly `r`: the negation of
Baker's Brill–Noether existence conjecture (Conjecture 3.9 of Baker 2008). -/
theorem P058_disprove :
    ¬ ∀ G : CFGraph, graph_connected G → ∀ r d : ℤ, 0 ≤ r → 0 ≤ d →
      0 ≤ brillNoetherNumber (genus G) r d → ∃ D : CFDiv G, divisorRankEq G D r ∧ deg D ≤ d := by
  sorry
