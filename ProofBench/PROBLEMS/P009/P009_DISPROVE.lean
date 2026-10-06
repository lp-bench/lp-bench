/-
Prove-or-disprove companion — DISPROVE polarity for P009 (union-closed sets
conjecture / Frankl).

`P009` (in `P009.lean`) and `P009_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

The union-closed sets (Frankl) conjecture is OPEN: the best known general
density bound is the constant `(3 - √5)/2 ≈ 0.38` (Gilmer 2022 and
successors), short of the conjectured `1/2`.  The polarity is therefore
genuinely unknown — a sorry-free proof of this disprove version amounts to
refuting the conjecture by exhibiting a nondegenerate union-closed family in
which every ground element has density below `1/2`.

The statement below is the negation of `P009` with its section variables
(`U` and the `DecidableEq` instance) universally quantified, so that the
pair of polarities exactly partitions the truth values of the challenge.

Evaluation note: a submitted proof of either polarity must be type-checked in
isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts as an
axiom).  Importing `P009.lean` here is sound — `¬P` is not derivable from the
axiom `P` — but harness-level isolation per target is still the safe protocol.
-/
import ProofBench.PROBLEMS.P009.P009

open Finset

/-- **Disprove version of P009.**  The negation of the union-closed sets
conjecture: for some finite universe `U` and some nondegenerate union-closed
family `F` over `U`, no ground element of `F` has density at least `1/2`.

The prove polarity is an open conjecture, so it is genuinely unknown which of
the two polarities is provable; establishing this one would refute Frankl's
conjecture. -/
theorem P009_disprove :
    ¬ ∀ (U : Type) [DecidableEq U] (F : Finset (Finset U)), UnionClosedConj F := by
  sorry
