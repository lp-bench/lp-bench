/-
Prove-or-disprove companion — DISPROVE polarity for P008 (Ryser's hypergraph
conjecture, universal statement).

`P008` (in `P008.lean`) and `P008_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

Ryser's conjecture (`τ ≤ (r - 1)·ν` for `r`-partite `r`-uniform hypergraphs)
is a theorem for `r = 2` (König) and `r = 3` (Aharoni 2001), but OPEN for all
`r ≥ 4`.  The polarity of this universal version is therefore genuinely
unknown — a sorry-free proof of this disprove version amounts to refuting the
conjecture, and a counterexample for any single `r ≥ 4` would suffice.

The statement below is the negation of `RyserConjecture` (the statement
`P008` proves), so that the pair of polarities exactly partitions the truth
values of the challenge.

Evaluation note: a submitted proof of either polarity must be type-checked in
isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts as an
axiom).  Importing `P008.lean` here is sound — `¬P` is not derivable from the
axiom `P` — but harness-level isolation per target is still the safe protocol.
-/
import ProofBench.PROBLEMS.P008.P008

universe u

/-- **Disprove version of P008.**  The negation of Ryser's hypergraph
conjecture in its universal form: for some vertex type, some `r ≥ 2`, and
some `r`-partite `r`-uniform hypergraph, the cover number exceeds `(r - 1)`
times the matching number.

The prove polarity is an open conjecture (open for every `r ≥ 4`), so it is
genuinely unknown which of the two polarities is provable; establishing this
one — e.g. via a counterexample for a single `r` — would refute the
conjecture. -/
theorem P008_disprove : ¬ RyserConjecture.{u} := by
  sorry
