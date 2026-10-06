/-
Prove-or-disprove companion — DISPROVE polarity for P001 (Hadwiger's
Conjecture, universal form).

`P001` (in `P001.lean`) and `P001_disprove` (below) form a
polarity pair in the prove-or-disprove evaluation format: a model answers the
problem by giving a sorry-free proof of either one.

Hadwiger's Conjecture (1943) is a famous OPEN problem in its universal form
(it is known only for clique numbers up to 6), so the truth value of this
polarity is genuinely unknown: a sorry-free proof of `P001_disprove`
would refute Hadwiger's Conjecture.

Evaluation note: a submitted proof of either polarity must be type-checked in
isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts as an
axiom).  Importing `P001.lean` here is sound — `¬P` is not derivable from the
axiom `P` — but harness-level isolation per target is still the safe protocol.
-/
import ProofBench.PROBLEMS.P001.P001

universe u

open SimpleGraph

/-- **Disprove version of P001.**  The negation of the universal Hadwiger
Conjecture: some finite simple graph `G` has chromatic number strictly
exceeding its Hadwiger number.

Hadwiger's Conjecture is open, so this statement's truth value is genuinely
unknown: proving it refutes the conjecture. -/
theorem P001_disprove :
    ¬ ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
        G.chromaticNumber ≤ (hadwigerNumber G : ℕ∞) := by
  sorry
