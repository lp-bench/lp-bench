/-
Prove-or-disprove companion — DISPROVE polarity for P075 (bounded
avoidability index of patterns).

`P075` (in `P075.lean`) and `P075_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

The question is OPEN (Currie, WORDS 2003, Question 1.1.03.3).  A disproof
must exhibit an avoidable pattern that is not `5`-avoidable, i.e. one of
avoidability index at least `6`.  Constraints: the avoidability index of
an avoidable pattern is finite (definition), every avoidable binary pattern
has index at most `3`, every doubled pattern has index at most `3` (Ochem
2016), and Clark's pattern `abvacwbaxbcycdazdcd` has index exactly `5` and
admits no known generalisation; deciding `k`-avoidability of a given
pattern is itself not known to be decidable, so a disproof needs a genuinely
new construction.

Evaluation note: a submitted proof of either polarity must be type-checked
in isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts
as an axiom).
-/
import ProofBench.Mathlib_Problems.Combinatorics.Words.Pattern

open Pattern

/-- Disproof polarity: some avoidable pattern is not `5`-avoidable. -/
theorem P075_disprove :
    ¬ ∀ (m : ℕ) (p : List (Fin m)), IsAvoidable p → IsKAvoidable p 5 := by
  sorry
