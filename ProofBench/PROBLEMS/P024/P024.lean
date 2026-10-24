import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Set.Card

open Function Matroid

variable {α : Type}

/-- `IsFamilyOfDisjointBases M B` witnesses that `B : Fin n → Set α` is a family
of pairwise-disjoint bases of `M`. -/
def IsFamilyOfDisjointBases (M : Matroid α) (B : Fin n → Set α) : Prop :=
  (∀ i, M.IsBase (B i)) ∧ (Pairwise (Disjoint on B))

/-- Rota's basis conjecture (Huang–Rota 1994, Conjecture 4): for `n` pairwise disjoint bases
`B i` of a rank-`n` matroid `M`, there are `n` pairwise disjoint bases `C j` of `M` with
`|B i ∩ C j| = 1` for all `i, j`. -/
theorem P024 : ∀ (n : ℕ), ∀ {M : Matroid α} (hrank : M.eRank = (n : ℕ∞)) {B : Fin n → Set α},
    IsFamilyOfDisjointBases M B →
    ∃ C : Fin n → Set α, IsFamilyOfDisjointBases M C ∧
      ∀ (i j : Fin n), (B i ∩ C j).ncard = 1 := sorry
