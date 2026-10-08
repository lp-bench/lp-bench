import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Minor

universe u

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

/-- **Refuting Hadwiger's Conjecture.**  Hadwiger's Conjecture (1943) asserted
`χ(G) ≤ h(G)` for every finite graph.  It was disproved in October 2026
(OpenAI math release, Lean-checked).  Show that some finite simple graph has
chromatic number strictly exceeding its Hadwiger number. -/
theorem P001 :
    ¬ ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), HadwigerConj G := sorry
