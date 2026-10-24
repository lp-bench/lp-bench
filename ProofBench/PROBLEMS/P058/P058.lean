import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.ChipFiring.Rank

/-- If `r, d ≥ 0` and the Brill–Noether number `ρ(g, r, d)` is nonnegative, then
every connected finite loopless multigraph of genus `g` has a divisor of rank
exactly `r` and degree at most `d`. Baker's Brill–Noether existence conjecture,
Conjecture 3.9 of Baker (2008). -/
theorem P058 (G : CFGraph) (_hConnected : graph_connected G) (r d : ℤ)
    (_hr : 0 ≤ r) (_hd : 0 ≤ d)
    (_hρ : 0 ≤ brillNoetherNumber (genus G) r d) :
    ∃ D : CFDiv G, divisorRankEq G D r ∧ deg D ≤ d := by
  sorry
