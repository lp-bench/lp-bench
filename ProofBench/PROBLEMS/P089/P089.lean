import Mathlib.Order.Fin.Basic

/-- Erdős–Szekeres: sufficiently many distinct terms force a long strictly
increasing or strictly decreasing subsequence. -/
theorem P089 {α : Type*} [LinearOrder α] (r s n : ℕ)
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hn : (r - 1) * (s - 1) < n)
    (a : Fin n → α) (ha : Function.Injective a) :
    (∃ f : Fin r ↪o Fin n, StrictMono (a ∘ f)) ∨
      ∃ f : Fin s ↪o Fin n, StrictAnti (a ∘ f) := by
  sorry
