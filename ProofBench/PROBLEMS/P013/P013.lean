import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Basic

open Finset

namespace BeckFiala

/-- A signing assigns one of the two integers `-1` and `1` to each point. -/
def IsSigning {V : Type*} (χ : V → ℤ) : Prop :=
  ∀ v, χ v = -1 ∨ χ v = 1

/-- A signing of discrepancy at most `D` on every member of a set system. -/
def HasDiscrepancyAtMost {V I : Type*} (A : I → Finset V) (D : ℤ) : Prop :=
  ∃ χ : V → ℤ, IsSigning χ ∧ ∀ i, |∑ v ∈ A i, χ v| ≤ D

end BeckFiala

open Classical in
/-- Beck–Fiala: if each point lies in at most `t ≥ 1` sets, there is a
signing whose discrepancy on every set is at most `2t - 1`. -/
theorem P013 {V I : Type*} [Finite V] [Fintype I] (A : I → Finset V)
    (t : ℕ) (ht : 1 ≤ t)
    (hdegree : ∀ v, #{i | v ∈ A i} ≤ t) :
    BeckFiala.HasDiscrepancyAtMost A (2 * (t : ℤ) - 1) := by
  sorry
