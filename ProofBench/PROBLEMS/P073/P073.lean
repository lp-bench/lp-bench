import ProofBench.Mathlib_Problems.Combinatorics.LatinSquare

/-- **The Alon–Tarsi conjecture** (1992): for every even `n`, the numbers of even and
odd Latin squares of order `n` differ.  (For odd `n ≥ 3` they are equal, by swapping
two rows.)  Known for `n = p + 1` (Drisko) and `n = p - 1` (Glynn) with `p` an odd
prime, so for all even `n ≤ 24`; the smallest open case is `n = 26`.  By Huang–Rota
the conjecture implies Rota's basis conjecture in even dimension over fields of
characteristic zero, and via the Alon–Tarsi polynomial method it implies the
Dinitz conjecture for even `n`. -/
theorem P073 :
    ∀ n : ℕ, Even n →
      (Finset.univ.filter fun L : LatinSquare n => L.sign = 1).card ≠
        (Finset.univ.filter fun L : LatinSquare n => L.sign = -1).card := by
  sorry
