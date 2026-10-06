import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Set.Card


/-!
# Rota's Basis Conjecture — Universal Statement

For every `n` and every rank-`n` matroid `M`, given `n` pairwise disjoint bases
`B₁, …, Bₙ`, their union can be repartitioned into `n` pairwise disjoint
*rainbow* bases `C₁, …, Cₙ` — each `Cⱼ` meeting every `Bᵢ` in exactly one
element.

Status. The original conjecture (Huang–Rota) is open in general. The *scaled
weakening* — the form previously posed as an open challenge — is resolved:
Bucić, Kwan, Pokrovskiy and Sudakov proved the "halfway" bound. Ported here
because that resolution makes it a settled benchmark problem rather than an open
challenge. (See `DATABASE/tex/P024.tex` for the references.)
-/

open Function Matroid

variable {α : Type}

/-- `IsFamilyOfDisjointBases M B` witnesses that `B : Fin n → Set α` is a family
of pairwise-disjoint bases of `M`. -/
def IsFamilyOfDisjointBases (M : Matroid α) (B : Fin n → Set α) : Prop :=
  (∀ i, M.IsBase (B i)) ∧ (Pairwise (Disjoint on B))

/-- **Rota's basis conjecture (universal).** For every `n`, given `n` pairwise
disjoint bases of a rank-`n` matroid `M`, there exist `n` pairwise disjoint
rainbow bases: a family `C` of disjoint bases of `M` with `|Bᵢ ∩ Cⱼ| = 1` for
all `i, j`. -/
theorem P024 : ∀ (n : ℕ), ∀ {M : Matroid α} (hrank : M.eRank = (n : ℕ∞)) {B : Fin n → Set α},
    IsFamilyOfDisjointBases M B →
    ∃ C : Fin n → Set α, IsFamilyOfDisjointBases M C ∧
      ∀ (i j : Fin n), (B i ∩ C j).ncard = 1 := sorry
