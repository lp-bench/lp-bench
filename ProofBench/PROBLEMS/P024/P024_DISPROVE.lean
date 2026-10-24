import ProofBench.PROBLEMS.P024.P024

open Function Matroid

/-- **Disprove version of P024.**  The negation of the universal Rota basis
conjecture: for some type `α`, some `n` and some rank-`n` matroid on `α` with `n`
pairwise disjoint bases, no system of `n` pairwise disjoint rainbow bases (each
meeting every original basis in a singleton) exists. -/
theorem P024_disprove :
    ¬ ∀ (α : Type) (n : ℕ), ∀ {M : Matroid α} (_ : M.eRank = (n : ℕ∞)) {B : Fin n → Set α},
      IsFamilyOfDisjointBases M B →
      ∃ C : Fin n → Set α, IsFamilyOfDisjointBases M C ∧
        ∀ (i j : Fin n), (B i ∩ C j).ncard = 1 := sorry
