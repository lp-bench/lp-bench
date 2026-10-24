import ProofBench.PROBLEMS.P009.P009

open Finset

/-- **Disprove version of P009**: for some type `U`, some union-closed family `F` of
finite subsets of `U`, other than `∅` and `{∅}`, has no element of density at least `1/2`. -/
theorem P009_disprove :
    ¬ ∀ (U : Type) [DecidableEq U] (F : Finset (Finset U)), UnionClosedConj F := by
  sorry
