import ProofBench.Mathlib_Problems.Combinatorics.MetricGraph.Rank

/-- If `r, d ≥ 0` and `ρ(g, r, d) ≥ 0`, then every connected metric graph of genus
`g` has a divisor of rank exactly `r` and degree at most `d`. Brill–Noether
existence for metric graphs, Baker (2008). -/
theorem P059 (G : MetricGraph) (_hConnected : G.Connected) (r d : ℤ)
    (_hr : 0 ≤ r) (_hd : 0 ≤ d)
    (_hρ : 0 ≤ brillNoetherNumber G.genus r d) :
    ∃ D : MetricDiv G, metricDivisorRankEq G D r ∧ metricDegree D ≤ d := by
  sorry
