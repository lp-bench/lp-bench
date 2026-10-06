/-
Prove-or-disprove companion — DISPROVE polarity for P003 (diagonal Ramsey
numbers: shrinking two-sided exponential brackets).

`P003` (in `P003.lean`) and `P003_disprove` (below) form a
polarity pair in the prove-or-disprove evaluation format: a model answers the
problem by giving a sorry-free proof of either one.

As `r → ∞` the allowed gap `(4 - √2) * 0.96^r` tends to `0`, so the full family
is essentially the existence of the limit of `R(t)^{1/t}` — a famous OPEN
problem of Erdős.  The truth value of this polarity is therefore genuinely
unknown: a sorry-free proof of `P003_disprove` would refute the
conjecture that arbitrarily tight exponential brackets exist.

Evaluation note: a submitted proof of either polarity must be type-checked in
isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts as an
axiom).  Importing `P003.lean` here is sound — `¬P` is not derivable from the
axiom `P` — but harness-level isolation per target is still the safe protocol.
-/
import ProofBench.PROBLEMS.P003.P003

/-- **Disprove version of P003.**  The negation of the shrinking-bracket
family: for some `r`, no pair `d₁ d₂` within `(4 - √2) * 0.96^r` of each other
eventually brackets `ramseyNumber t` between `d₁^t` and `d₂^t`.

The underlying growth-rate question is open, so this statement's truth value
is genuinely unknown: proving it refutes the conjecture. -/
theorem P003_disprove :
    ¬ ∀ r : ℕ, ∃ d₁ d₂ : ℝ, 0 ≤ d₁ ∧ 0 ≤ d₂ ∧ |d₁ - d₂| ≤ (4 - √2) * (0.96 : ℝ) ^ r ∧
      ∃ T, ∀ t ≥ T, d₁ ^ t ≤ ramseyNumber t ∧ ramseyNumber t ≤ d₂ ^ t := by
  sorry
