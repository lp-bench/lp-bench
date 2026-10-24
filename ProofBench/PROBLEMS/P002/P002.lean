import Matroid.Representation.Basic
import Matroid.Minor.Iso
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Finite.GaloisField

open Function Matroid

universe u

variable {α : Type u}

/-- A matroid is GF(pᵐ)-representable if it can be represented over the
Galois field of order `p^m`. -/
def IsGFRepresentable
    (p m : ℕ) [Fact p.Prime] (M : Matroid α) : Prop :=
  ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (GaloisField p m) W),
    Nonempty (M.Rep (GaloisField p m) W)

/-- N is an excluded minor for the property P if N does not have P,
but every proper minor of N does. -/
def IsExcludedMinorFor (P : Matroid α → Prop) (M : Matroid α) : Prop :=
  ¬ P M ∧ ∀ N : Matroid α, N <m M → P N

/-- `L` is a complete list of excluded minors for GF(pᵐ)-representability: a finite
set of pairwise non-isomorphic finite excluded minors such that every finite
non-representable matroid has a minor isomorphic to a member of `L`. Members of
`L` have ground sets in `ℕ`; other matroids are compared with them up to isomorphism. -/
def CompleteExcludedMinorList (p m : ℕ) [Fact p.Prime]
    (L : Set (Matroid ℕ)) : Prop :=
  L.Finite ∧
    (∀ N ∈ L, N.Finite ∧ IsExcludedMinorFor (IsGFRepresentable p m) N) ∧
      (∀ N₁ ∈ L, ∀ N₂ ∈ L, N₁ ≠ N₂ → IsEmpty (N₁ ≂ N₂)) ∧
        (∀ {β : Type u} (M : Matroid β), M.Finite →
          ¬ IsGFRepresentable p m M → ∃ N ∈ L, Nonempty (N ≤i M))

/-- Rota's Conjecture for the prime power `pᵐ`: a complete finite list of
excluded minors for GF(pᵐ)-representability exists. -/
def RotaConj (p m : ℕ) [Fact p.Prime] : Prop :=
  ∃ L : Set (Matroid ℕ), CompleteExcludedMinorList.{u} p m L

/-- **Rota's conjecture** (Rota 1971; proof announced by Geelen–Gerards–Whittle, 2014):
for every prime power `r = pᵐ` with `m > 0`, a complete finite list of excluded minors
for GF(pᵐ)-representability exists. -/
theorem P002 (r p m : ℕ) [Fact p.Prime] (hm : 0 < m) (hr : r = p ^ m) :
    RotaConj p m := sorry
