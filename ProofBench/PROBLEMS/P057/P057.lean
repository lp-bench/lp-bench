import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.ChipFiring

/-- **The divisorial gonality conjecture for finite graphs.**  Every finite
connected multigraph of cycle rank `g` has an effective divisor of degree at
most `⌊(g + 3) / 2⌋` and rank at least one, expressed directly by the
ability to move a chip to any prescribed vertex within its firing class. -/
theorem P057 (G : CFGraph) (_hConnected : graph_connected G) :
    ∃ D : CFDiv G,
      effective D ∧ deg D ≤ (genus G + 3) / 2 ∧
        ∀ q : G.V, ∃ E : CFDiv G,
          effective E ∧ linear_equiv G D E ∧ 1 ≤ E q := by
  sorry
