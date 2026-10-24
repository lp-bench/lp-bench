import ProofBench.Mathlib_Problems.Combinatorics.Superpermutation
import Mathlib.Data.Nat.Factorial.Basic

open Nat

/-- Every superpermutation on `n` symbols has length at least
`n! + (n - 1)! + (n - 2)! + n - 3` (anonymous 4chan post, 2011; written up by
Houston–Pantone–Vatter, 2018). No hypothesis on `n` is needed: with natural-number
subtraction the bound is `0` for `n = 0` and `1` for `n = 1`. -/
theorem P072 :
    ∀ (n : ℕ) (w : List (Fin n)), IsSuperpermutation n w →
      n ! + (n - 1)! + (n - 2)! + n - 3 ≤ w.length := by
  sorry
