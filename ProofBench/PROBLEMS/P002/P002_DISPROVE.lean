/-
Prove-or-disprove companion — DISPROVE polarity for P002 (Rota's Conjecture:
excluded minors of GF(pᵐ)-representable matroids).

`P002` (in `P002.lean`) and `P002_disprove` (below) form a
polarity pair in the prove-or-disprove evaluation format: a model answers the
problem by giving a sorry-free proof of either one.

Rota's Conjecture is a known theorem (Geelen–Gerards–Whittle, announced 2014),
so this polarity is deliberately false and is expected to be unprovable.  It
is exposed so the benchmark can be run in prove-or-disprove mode without
revealing the answer in the problem statement.

Evaluation note: a submitted proof of either polarity must be type-checked in
isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts as an
axiom).  Importing `P002.lean` here is sound — `¬P` is not derivable from the
axiom `P` — but harness-level isolation per target is still the safe protocol.
-/
import ProofBench.PROBLEMS.P002.P002

universe u

open Function Matroid

/-- **Disprove version of P002.**  The negation of Rota's Conjecture: for some
prime power `r = pᵐ`, no complete finite list of excluded minors for
GF(pᵐ)-representability exists.

Rota's Conjecture is a proved theorem, so this statement is expected to be
false. -/
theorem P002_disprove :
    ¬ ∀ (r p m : ℕ) [Fact p.Prime], 0 < m → r = p ^ m →
        ∃ L : Set (Matroid ℕ), CompleteExcludedMinorList.{u} p m L := by
  sorry
