import ProofBench.Mathlib_Problems.NumberTheory.Collatz

/-- **The Collatz conjecture** (`3n + 1` problem, Collatz 1937): iterating the map
`n ↦ n / 2` (`n` even), `n ↦ 3 n + 1` (`n` odd) from any positive integer eventually
reaches `1`.  Verified for all `n < 2 ^ 68` (Barina 2020); Tao (2019) showed that
almost all orbits attain almost bounded values; any nontrivial cycle would be
enormous (Eliahou 1993).  Equivalent to the conjunction of "no orbit diverges" and
"the only cycle is `1 → 4 → 2 → 1`". -/
theorem P074 : ∀ n : ℕ, 0 < n → CollatzReachesOne n := by
  sorry
