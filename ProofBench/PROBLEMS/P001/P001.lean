import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Minor

variable {V : Type*} [Fintype V]

open SimpleGraph

noncomputable def hadwigerNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact Nat.findGreatest (fun r =>
  Nonempty (Minor (completeGraph (Fin r)) G)) (Fintype.card V)

/- Hadwiger's Conjecture for `G`: the chromatic number is at most the
Hadwiger number. -/
def HadwigerConj (G : SimpleGraph V) : Prop :=
  G.chromaticNumber ≤ (hadwigerNumber G : ℕ∞)

/- **Hadwiger's Conjecture**: every finite graph satisfies
`χ(G) ≤ h(G)`. -/
theorem P001 (G : SimpleGraph V) : HadwigerConj G := sorry
