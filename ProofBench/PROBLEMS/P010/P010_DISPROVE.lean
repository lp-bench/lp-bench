/-
Prove-or-disprove companion — DISPROVE polarity for P010 (Unfriendly
Partition Conjecture, countable).

`P010` (in `P010.lean`) and `P010_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

The truth value is genuinely open: the known counterexamples to unrestricted
unfriendly partitions (Shelah–Milner 1990) are uncountable, so they do not
settle this polarity.  A sorry-free proof below would exhibit a countable
graph with no unfriendly partition and refute the Cowan–Emerson conjecture.

Evaluation note: a submitted proof of either polarity must be type-checked in
isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts as an
axiom).  Importing `P010.lean` here is sound — `¬P` is not derivable from the
axiom `P` — but harness-level isolation per target is still the safe
protocol.
-/
import ProofBench.PROBLEMS.P010.P010

universe u

/- **Disprove version of P010.**  Some countable graph has no unfriendly
partition.  Genuinely open: proving this refutes the conjecture. -/
theorem P010_disprove :
    ¬ ∀ (V : Type u) [Countable V] (G : SimpleGraph V), UPConj G := sorry
