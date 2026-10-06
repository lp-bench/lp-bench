/-
Prove-or-disprove companion — DISPROVE polarity for P005 (Erdős–Hajnal
Conjecture for paths, universal form).

`P005` (in `P005.lean`) and `P005_disprove` (below) form a
polarity pair in the prove-or-disprove evaluation format: a model answers the
problem by giving a sorry-free proof of either one.

The Erdős–Hajnal Conjecture for all paths is OPEN (it is known only for short
paths, e.g. `P₄` and `P₅`), so the truth value of this polarity is genuinely
unknown: a sorry-free proof of `P005_disprove` would refute the
Erdős–Hajnal Conjecture for some path.

Evaluation note: a submitted proof of either polarity must be type-checked in
isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts as an
axiom).  Importing `P005.lean` here is sound — `¬P` is not derivable from the
axiom `P` — but harness-level isolation per target is still the safe protocol.
-/
import ProofBench.PROBLEMS.P005.P005

open SimpleGraph

/-- **Disprove version of P005.**  The negation of the universal Erdős–Hajnal
Conjecture for paths: for some `r`, no constant `c > 0` guarantees that every
finite `P_r`-free graph has a clique or independent set of polynomial size
`|V|^c`.

The conjecture is open for long paths, so this statement's truth value is
genuinely unknown: proving it refutes the conjecture. -/
theorem P005_disprove :
    ¬ ∀ r : ℕ, ErdosHajnalConjectureFor (pathGraph r) := by
  sorry
