/-
Prove-or-disprove companion — DISPROVE polarity for P024 (Rota's Basis
Conjecture, universal form).

`P024` (in `P024.lean`) and `P024_disprove` (below) form a polarity pair
in the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

The full universal conjecture is open, so this polarity is genuinely unknown: a
sorry-free proof of `P024_disprove` would refute Rota's basis
conjecture.

Evaluation note: a submitted proof of either polarity must be type-checked in
isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts as an
axiom).  Importing `P024.lean` here is sound — `¬P` is not derivable from the
axiom `P` — but harness-level isolation per target is still the safe protocol.
-/
import ProofBench.PROBLEMS.P024.P024


open Function Matroid

variable {α : Type}

/-- **Disprove version of P024.**  The negation of the universal Rota basis
conjecture: for some `n` and some rank-`n` matroid with `n` pairwise disjoint
bases, no system of `n` pairwise disjoint rainbow bases (each meeting every
original basis in a singleton) exists. -/
theorem P024_disprove :
    ¬ ∀ (n : ℕ), ∀ {M : Matroid α} (_ : M.eRank = (n : ℕ∞)) {B : Fin n → Set α},
      IsFamilyOfDisjointBases M B →
      ∃ C : Fin n → Set α, IsFamilyOfDisjointBases M C ∧
        ∀ (i j : Fin n), (B i ∩ C j).ncard = 1 := sorry
