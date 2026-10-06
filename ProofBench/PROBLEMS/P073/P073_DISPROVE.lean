/-
Prove-or-disprove companion — DISPROVE polarity for P073 (the Alon–Tarsi
conjecture).

`P073` (in `P073.lean`) and `P073_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

The conjecture is OPEN since 1992.  A disproof must exhibit an even `n` with
equally many even and odd Latin squares of order `n`.  Constraints on any
counterexample: the conjecture holds for `n = p + 1` (Drisko 1997) and
`n = p - 1` (Glynn 2010), `p` an odd prime, hence for every even `n ≤ 24`;
the smallest open case is `n = 26`, where the number of Latin squares is far
beyond enumeration.  A counterexample would leave Rota's basis conjecture
(P024) in that dimension without its Huang–Rota route.

Evaluation note: a submitted proof of either polarity must be type-checked
in isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts
as an axiom).
-/
import ProofBench.Mathlib_Problems.Combinatorics.LatinSquare

/-- Disproof polarity of the Alon–Tarsi conjecture: some even order has equally many
even and odd Latin squares. -/
theorem P073_disprove :
    ¬ ∀ n : ℕ, Even n →
      (Finset.univ.filter fun L : LatinSquare n => L.sign = 1).card ≠
        (Finset.univ.filter fun L : LatinSquare n => L.sign = -1).card := by
  sorry
