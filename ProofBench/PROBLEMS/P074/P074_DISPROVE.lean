/-
Prove-or-disprove companion — DISPROVE polarity for P074 (the Collatz
conjecture).

`P074` (in `P074.lean`) and `P074_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

The conjecture is OPEN since 1937.  A disproof must exhibit a positive
integer whose orbit never reaches `1`: either a divergent orbit or a
nontrivial cycle.  Constraints on any counterexample: the conjecture is
verified for all `n < 2 ^ 68` (Barina 2020); a nontrivial cycle must have
length at least `17 087 915` (Eliahou 1993, since improved); by Tao (2019)
almost all orbits attain almost bounded values, so a divergent orbit is a
density-zero phenomenon.  No counterexample can be certified by finite
computation, so a disproof would have to be structural.

Evaluation note: a submitted proof of either polarity must be type-checked
in isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts
as an axiom).
-/
import ProofBench.Mathlib_Problems.NumberTheory.Collatz

/-- Disproof polarity of the Collatz conjecture: some positive integer never reaches
`1`. -/
theorem P074_disprove : ¬ ∀ n : ℕ, 0 < n → CollatzReachesOne n := by
  sorry
