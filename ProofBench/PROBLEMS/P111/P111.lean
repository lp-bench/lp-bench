import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Interval.Finset.Nat

open Finset

/-- **A Consecutive Pair Among n + 1 Numbers from [2n].** Any `n + 1` numbers from `{1, …, 2n}`
include two consecutive ones. -/
theorem P111 (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 (2 * n)) (hcard : n + 1 ≤ S.card) :
    ∃ a ∈ S, a + 1 ∈ S := by
  sorry
