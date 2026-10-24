import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic

/-- Bollobás 1965: disjoint pairs of r- and s-element sets that intersect across
every pair of distinct indices number at most `choose (r + s) r`. -/
theorem P091 {ι α : Type*} [Fintype ι] (r s : ℕ) (A B : ι → Finset α)
    (hA : ∀ i, (A i).card = r) (hB : ∀ i, (B i).card = s)
    (hdis : ∀ i, Disjoint (A i) (B i))
    (hcross : ∀ i j, i ≠ j → ¬ Disjoint (A i) (B j)) :
    Fintype.card ι ≤ (r + s).choose r := by
  sorry
