import ProofBench.Mathlib_Problems.Combinatorics.Digraph.CaccettaHaggkvist

/-- Disproof polarity of P003: for some `r ≥ 1`, a finite nonempty digraph on `n`
vertices with all out-degrees at least `r` has no directed cycle of length at most
`⌈n / r⌉`. -/
theorem P003_disprove :
    ∃ (r : ℕ) (W : Type) (_ : Fintype W) (_ : Nonempty W) (D : Digraph W), 0 < r ∧
      (∀ v, r ≤ D.outDegree v) ∧
        ∀ k, 0 < k → k ≤ Fintype.card W ⌈/⌉ r → ∀ c : Fin k → W, ¬ D.IsCycle c := sorry
