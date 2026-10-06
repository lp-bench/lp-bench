import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Antichain

/-- Sperner: an inclusion antichain has at most as many members as a middle
layer of the Boolean lattice. -/
theorem P090 {α : Type*} [Fintype α] (𝒜 : Finset (Finset α))
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    𝒜.card ≤ (Fintype.card α).choose (Fintype.card α / 2) := by
  sorry
