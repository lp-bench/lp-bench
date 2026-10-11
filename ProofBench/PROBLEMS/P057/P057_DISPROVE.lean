import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.ChipFiring

/-- **Disprove version of P057.**  Some finite connected multigraph of cycle rank `g` has no
effective divisor of degree at most `⌊(g + 3) / 2⌋` from whose firing class a chip can be
moved to every vertex. -/
theorem P057_disprove :
    ¬ ∀ G : CFGraph, graph_connected G →
      ∃ D : CFDiv G, effective D ∧ deg D ≤ (genus G + 3) / 2 ∧
        ∀ q : G.V, ∃ E : CFDiv G, effective E ∧ linear_equiv G D E ∧ 1 ≤ E q := by
  sorry
