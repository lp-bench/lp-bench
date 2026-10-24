import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Finset.Card

open Finset

variable {U : Type} [DecidableEq U] (F : Finset (Finset U))

/-- The density of `x` in `F`: the number of members of `F` containing `x`, divided
by `|F|` (by `1` when `F` is empty, a case the conjecture excludes). -/
def density (x : U) : ℚ :=
  ((F.filter fun s => x ∈ s).card) / (max 1 F.card)

/-- `F` is union-closed if the union of any two members is in `F`. -/
def IsUnionClosed : Prop :=
  ∀ ⦃s t : Finset U⦄, s ∈ F → t ∈ F → s ∪ t ∈ F

/-- The union-closed sets (Frankl) conjecture for the family `F`: if `F` is
union-closed and neither `∅` nor `{∅}`, some element has density at least `1/2`. -/
def UnionClosedConj : Prop :=
  IsUnionClosed F →
  F ≠ ∅ ∧ F ≠ {∅} →
  ∃ x, density F x ≥ (1 / 2 : ℚ)

/-- **Frankl's union-closed sets conjecture** (Frankl 1979): every finite union-closed
family of finite sets other than `∅` and `{∅}` has an element that belongs to at least
half of its members. -/
theorem P009 : UnionClosedConj F := sorry
