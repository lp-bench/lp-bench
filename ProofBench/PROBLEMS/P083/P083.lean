import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Pebbling
import Mathlib.Combinatorics.SimpleGraph.Hasse

open SimpleGraph SimpleGraph.Pebbling

/-- The path on `n + 1` vertices has pebbling number `2^n` (classical; see Hurlbert,
arXiv:1101.5641, Section 2). -/
theorem P083 (n : ℕ) : pebblingNumber (pathGraph (n + 1)) = 2 ^ n := by
  sorry
