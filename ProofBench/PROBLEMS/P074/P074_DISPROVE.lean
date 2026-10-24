import ProofBench.Mathlib_Problems.NumberTheory.Collatz

/-- Disproof polarity of the Collatz conjecture: some positive integer never reaches `1`.
The conjecture is verified for all `n < 2 ^ 68` (Barina 2020). -/
theorem P074_disprove : ¬ ∀ n : ℕ, 0 < n → CollatzReachesOne n := by
  sorry
