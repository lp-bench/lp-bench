import ProofBench.Mathlib_Problems.Topology.TwoComplexEmbedding

open FiniteTwoComplex

/-- For some `c`, a deterministic Turing machine decides in time `2 ^ n ^ c`
whether a finite two-dimensional simplicial complex with trivial integral first
homology embeds in three-dimensional Euclidean space (Carmesin–Lichev 2022, with
the sphere recognition results of Ivanov and Schleimer). -/
theorem P067 : ∃ c, EmbeddabilityInTime fun n ↦ 2 ^ n ^ c := by
  sorry
