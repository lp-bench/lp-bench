import ProofBench.Mathlib_Problems.Combinatorics.Digraph.CaccettaHaggkvist

/-- The Caccetta–Häggkvist conjecture for every minimum out-degree `r ≥ 1`. -/
def CaccettaHaggkvistConj : Prop := ∀ r, 0 < r → CaccettaHaggkvistFor r

/-- **The Caccetta–Häggkvist conjecture** (1978).  Every finite digraph on `n`
vertices in which every vertex has out-degree at least `r ≥ 1` contains a directed
cycle of length at most `⌈n / r⌉`.  Known for `r ≤ 5` (Caccetta–Häggkvist for
`r = 2`, Hamidoune for `r = 3`, Hoàng–Reed for `r = 4, 5`); open from `r = 6` on. -/
theorem P003 : CaccettaHaggkvistConj := sorry
