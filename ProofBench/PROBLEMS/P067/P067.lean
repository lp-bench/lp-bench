import ProofBench.Mathlib_Problems.Topology.TwoComplexEmbedding

open FiniteTwoComplex

/-- **Carmesin–Lichev: embedding homologically trivial two-complexes in
exponential time.** For some `c`, a deterministic algorithm decides in time
`2 ^ n ^ c` whether a finite two-dimensional simplicial complex with trivial
integral first homology embeds in three-dimensional Euclidean space. -/
theorem P067 : ∃ c, EmbeddabilityInTime fun n ↦ 2 ^ n ^ c := by
  sorry
