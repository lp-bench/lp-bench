import ProofBench.Mathlib_Problems.Combinatorics.LatinSquare

/-- **The Alon–Tarsi conjecture** (Alon–Tarsi 1992): for every even `n`, the numbers of even
and odd Latin squares of order `n` differ.  Known for `n = p ± 1` with `p` an odd prime
(Drisko 1997, Glynn 2010), hence for all even `n ≤ 24`. -/
theorem P073 :
    ∀ n : ℕ, Even n →
      (Finset.univ.filter fun L : LatinSquare n => L.sign = 1).card ≠
        (Finset.univ.filter fun L : LatinSquare n => L.sign = -1).card := by
  sorry
