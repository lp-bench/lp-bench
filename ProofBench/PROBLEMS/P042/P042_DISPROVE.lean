/-
Prove-or-disprove companion — DISPROVE polarity for P042 (the Riemann
Hypothesis).

`P042` (in `P042.lean`) and `P042_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

The Riemann Hypothesis is a famous OPEN problem, so the truth value of this
polarity is genuinely unknown: a sorry-free proof of `P042_disprove` would
exhibit a nontrivial zero off the critical line.

Evaluation note: a submitted proof of either polarity must be type-checked in
isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts as an
axiom).  Importing `P042.lean` here is sound — `¬P` is not derivable from the
axiom `P` — but harness-level isolation per target is still the safe
protocol.
-/
import ProofBench.PROBLEMS.P042.P042

/-- **Disprove version of P042.**  The negation of the Riemann Hypothesis:
some nontrivial zero of the Riemann zeta function lies off the critical
line. -/
theorem P042_disprove : ¬ RiemannHypothesis := by
  sorry
