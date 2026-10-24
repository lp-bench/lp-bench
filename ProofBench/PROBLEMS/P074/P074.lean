import ProofBench.Mathlib_Problems.NumberTheory.Collatz

/-- **The Collatz conjecture** (Collatz 1937; see Lagarias 1985): iterating the Collatz map
from any positive integer eventually reaches `1`.  Verified for all `n < 2 ^ 68`
(Barina 2020). -/
theorem P074 : ∀ n : ℕ, 0 < n → CollatzReachesOne n := by
  sorry
