import ProofBench.Mathlib_Problems.Combinatorics.Digraph.CaccettaHaggkvist

/-- The Caccetta–Häggkvist conjecture for every minimum out-degree `r ≥ 1`. -/
def CaccettaHaggkvistConj : Prop := ∀ r, 0 < r → CaccettaHaggkvistFor r

/-- **The Caccetta–Häggkvist conjecture** (Caccetta–Häggkvist 1978): for every `r ≥ 1`,
every finite digraph on `n` vertices in which every vertex has out-degree at least `r`
contains a directed cycle of length at most `⌈n / r⌉`. -/
theorem P003 : CaccettaHaggkvistConj := sorry
