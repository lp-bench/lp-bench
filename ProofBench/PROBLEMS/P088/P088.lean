import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Choose.Basic

open SimpleGraph

/-- Erdős–Szekeres 1935: `choose(r+s-2,r-1)` vertices force an `r`-clique
or an independent set of size `s`. -/
theorem P088 {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (h : (r + s - 2).choose (r - 1) ≤ Fintype.card V) :
    (∃ t : Finset V, G.IsNClique r t) ∨
      ∃ t : Finset V, Gᶜ.IsNClique s t := by
  sorry
