import ProofBench.Mathlib_Problems.Combinatorics.Superpermutation
import Mathlib.Data.Nat.Factorial.Basic

open Nat

/-- **The anonymous lower bound for superpermutations** (4chan, 2011; written up by
Houston–Pantone–Vatter, 2018): every superpermutation on `n` symbols has length at least
`n! + (n - 1)! + (n - 2)! + n - 3`.  This improves the Ashlock–Tillotson bound
`n! + (n - 1)! + n - 2` and is tight for `n ≤ 4` (lengths `1, 3, 9, 33`).  The
statement needs no hypothesis on `n`: in natural-number arithmetic the bound is `0`
for `n = 0` and `1` for `n = 1`. -/
theorem P072 :
    ∀ (n : ℕ) (w : List (Fin n)), IsSuperpermutation n w →
      n ! + (n - 1)! + (n - 2)! + n - 3 ≤ w.length := by
  sorry
