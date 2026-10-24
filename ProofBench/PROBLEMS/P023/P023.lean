import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Ubiquity.Defs

open SimpleGraph

/- Do not modify above this line. -/

/-- There is a countable, locally finite graph (every vertex has finitely many neighbours) that is
not ubiquitous, refuting Andreae's ubiquity conjecture (Carmesin, arXiv:2210.02711). -/
theorem P023 :
    ∃ (W : Type) (_ : Countable W) (H : SimpleGraph W),
      (∀ v, (H.neighborSet v).Finite) ∧ ¬ IsUbiquitous H := by
  sorry
