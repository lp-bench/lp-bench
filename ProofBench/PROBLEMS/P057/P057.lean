import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.ChipFiring

/-- Every finite connected loopless multigraph of genus `g` has an effective
divisor of degree at most `⌊(g + 3) / 2⌋` whose firing class can put a chip on
any prescribed vertex (rank at least one). Baker's gonality conjecture,
Conjecture 3.10 of Baker (2008). -/
theorem P057 (G : CFGraph) (_hConnected : graph_connected G) :
    ∃ D : CFDiv G,
      effective D ∧ deg D ≤ (genus G + 3) / 2 ∧
        ∀ q : G.V, ∃ E : CFDiv G,
          effective E ∧ linear_equiv G D E ∧ 1 ≤ E q := by
  sorry
