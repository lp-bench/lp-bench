/-
Prove-or-disprove companion — DISPROVE polarity for P006 (α-well-quasi-ordering
of finite graphs under the minor relation).

`P006` (in `P006.lean`) and `P006_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

Whether the finite simple graphs form a *better*-quasi-order under the minor
relation is an OPEN problem: Robertson–Seymour gives well-quasi-ordering
(level `0` of the Nash–Williams hierarchy), and the challenge's finite-level
ladder is only conjectured beyond that.  The polarity is therefore genuinely
unknown — a sorry-free proof of this disprove version would exhibit a level
`r` at which the ladder fails and refute the finite-level BQO strengthening
of the graph minor theorem.

The statement below is the negation of `P006` verbatim: for some `r`, the
corresponding rung (planar graphs at level `r / 2` for even `r`, all finite
graphs at level `r / 2` for odd `r`) is not `α`-well-quasi-ordered.

Evaluation note: a submitted proof of either polarity must be type-checked in
isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts as an
axiom).  Importing `P006.lean` here is sound — `¬P` is not derivable from the
axiom `P` — but harness-level isolation per target is still the safe protocol.
-/
import ProofBench.PROBLEMS.P006.P006

/-- **Disprove version of P006.**  The negation of the interleaved
`α`-WQO ladder: at some level `r`, finite planar graphs (`r` even) or all
finite graphs (`r` odd) fail to be `(r / 2)`-well-quasi-ordered under minors.

The prove polarity is an open conjecture (levels `r ≥ 2` are open), so it is
genuinely unknown which of the two polarities is provable; establishing this
one would refute the finite-level BQO conjecture for graph minors. -/
theorem P006_disprove :
    ¬ ∀ r,
      if r % 2 = 0
      then IsAlphaWQO PlanarGraph.MinorLE (r / 2)
      else IsAlphaWQO FiniteGraph.MinorLE (r / 2) := by
  sorry
