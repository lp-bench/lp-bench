import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Finset.Card

/-!
# Union-Closed Sets Conjecture
In any finite union-closed family of sets, there exists an element that
belongs to at least half of the sets.
-/

open Finset

variable {U : Type} [DecidableEq U] (F : Finset (Finset U))

/- The density of element x in family F. -/
def density (x : U) : ℚ :=
  ((F.filter fun s => x ∈ s).card) / (max 1 F.card)

/- F is union-closed if the union of any two members is in F. -/
def IsUnionClosed : Prop :=
  ∀ ⦃s t : Finset U⦄, s ∈ F → t ∈ F → s ∪ t ∈ F

/- The Union-Closed Sets (Frankl) Conjecture for the family `F`: if `F` is
nondegenerate and union-closed, it has a Frankl element.  Stated about the
family `F` (a section variable), so that `P009` auto-generalizes over every
universe `U` and every family `F`, mirroring the `RyserConjecture H` shape of
P008. -/
def UnionClosedConj : Prop :=
  IsUnionClosed F →
  F ≠ ∅ ∧ F ≠ {∅} →
  ∃ x, density F x ≥ (1 / 2 : ℚ)

theorem P009 : UnionClosedConj F := sorry
