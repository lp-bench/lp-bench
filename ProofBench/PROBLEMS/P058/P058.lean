import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.ChipFiring.Rank

/-- **The Brill--Noether existence conjecture for finite graphs.**  If `r` and
`d` are nonnegative and the Brill--Noether number `ρ(g,r,d)` is nonnegative,
then every connected finite multigraph of genus `g` has a divisor of rank
exactly `r` and degree at most `d`. -/
theorem P058 (G : CFGraph) (_hConnected : graph_connected G) (r d : ℤ)
    (_hr : 0 ≤ r) (_hd : 0 ≤ d)
    (_hρ : 0 ≤ brillNoetherNumber (genus G) r d) :
    ∃ D : CFDiv G, divisorRankEq G D r ∧ deg D ≤ d := by
  sorry
