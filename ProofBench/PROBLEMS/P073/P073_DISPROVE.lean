import ProofBench.Mathlib_Problems.Combinatorics.LatinSquare

/-- Disproof polarity of the Alon–Tarsi conjecture: some even order has equally many
even and odd Latin squares.  The conjecture is known for every even order `n ≤ 24`. -/
theorem P073_disprove :
    ¬ ∀ n : ℕ, Even n →
      (Finset.univ.filter fun L : LatinSquare n => L.sign = 1).card ≠
        (Finset.univ.filter fun L : LatinSquare n => L.sign = -1).card := by
  sorry
