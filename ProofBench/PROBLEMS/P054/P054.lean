import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.CycleDoubleCover

universe u v

/-- Every finite bridgeless multigraph has a cycle double cover: the cycle
double cover conjecture of Szekeres (1973) and Seymour (1979). -/
theorem P054 {V : Type u} {E : Type v}
    [DecidableEq V] [DecidableEq E] [Finite V] [Fintype E]
    (G : Multigraph V E) (hG : G.Bridgeless) : Nonempty G.CycleDoubleCover := by
  sorry
