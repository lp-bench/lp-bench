import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Minor

universe u

variable {V : Type*} [Fintype V]

open SimpleGraph

/-- The Hadwiger number `h(G)`: the largest `r ≤ |V|` such that the complete graph
`K_r` is a minor of `G` (the bound `r ≤ |V|` is no restriction). -/
noncomputable def hadwigerNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact Nat.findGreatest (fun r =>
  Nonempty (Minor (completeGraph (Fin r)) G)) (Fintype.card V)

/-- Hadwiger's Conjecture for `G`: the chromatic number is at most the
Hadwiger number. -/
def HadwigerConj (G : SimpleGraph V) : Prop :=
  G.chromaticNumber ≤ (hadwigerNumber G : ℕ∞)

/-- **Refuting Hadwiger's Conjecture** (Hadwiger 1943; disproved in OpenAI's math
release, October 2026): some finite simple graph has chromatic number strictly
larger than its Hadwiger number. -/
theorem P001 :
    ¬ ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), HadwigerConj G := sorry
