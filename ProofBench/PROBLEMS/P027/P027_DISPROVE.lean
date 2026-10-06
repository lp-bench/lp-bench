/-
Prove-or-disprove companion — DISPROVE polarity for P027 (Seymour's Second
Neighbourhood Conjecture).

`P027` (in `P027.lean`) and `P027_disprove` (below) form a polarity pair in the
prove-or-disprove evaluation format: a model answers the problem by giving a
sorry-free proof of either one.

Seymour's Second Neighbourhood Conjecture is a famous OPEN problem, so the truth
value of this polarity is genuinely unknown: a sorry-free proof of
`P027_disprove` would refute the conjecture.

Evaluation note: a submitted proof of either polarity must be type-checked in
isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts as an
axiom).  Importing `P027.lean` here is sound — `¬P` is not derivable from the
axiom `P` — but harness-level isolation per target is still the safe protocol.
-/
import ProofBench.PROBLEMS.P027.P027

open OrientedGraph

/-- **Disprove version of P027.**  The negation of Seymour's Second
Neighbourhood Conjecture: some finite oriented graph has, at every vertex, a
second out-neighbourhood strictly smaller than its first.

The conjecture is open, so this statement's truth value is genuinely unknown:
proving it refutes the conjecture. -/
theorem P027_disprove :
    ¬ ∀ (V : Type) [Finite V] (G : OrientedGraph V),
        ∃ v, (G.outNeighborhood v).ncard ≤ (G.secondOutNeighborhood v).ncard := by
  sorry
