import Mathlib.Order.Fin.Basic

/-- Erdős–Szekeres 1935: more than `(r-1)(s-1)` distinct terms force a strictly
increasing subsequence of length `r` or a strictly decreasing one of length `s`. -/
theorem P089 {α : Type*} [LinearOrder α] (r s n : ℕ)
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hn : (r - 1) * (s - 1) < n)
    (a : Fin n → α) (ha : Function.Injective a) :
    (∃ f : Fin r ↪o Fin n, StrictMono (a ∘ f)) ∨
      ∃ f : Fin s ↪o Fin n, StrictAnti (a ∘ f) := by
  sorry
