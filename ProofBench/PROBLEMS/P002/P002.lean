import Matroid.Representation.Basic
import Matroid.Minor.Iso
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Excluded Minors of GF(pᵐ)-representable Matroids

For every prime power `r = pᵐ`, characterize the excluded minors for
representability over the finite field `GF(pᵐ)`.

For `r = 2` (binary matroids), the only excluded minor is `U₂,₄` (Tutte 1958).
For `r = 3` (ternary matroids), the excluded minors are `U₂,₅`, `U₃,₅`, `F₇`,
and `F₇*` (Reid; Bixby; Seymour).

This universal version asserts that a complete finite excluded-minor list
exists for EVERY prime-power field size — that is, Rota's conjecture, proved
by Geelen, Gerards, and Whittle.
-/

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

/-
`L` is a complete list of excluded minors for GF(pᵐ)-representability:

* `L` is finite;
* every member of `L` is a finite matroid which is an excluded minor for
  GF(pᵐ)-representability;
* no two distinct members of `L` are isomorphic; and
* every finite matroid that is not GF(pᵐ)-representable has a minor
  isomorphic to a member of `L` (`≤i` is the iso-minor relation).

Members of `L` are matroids with ground sets in `ℕ`; matroids over an
arbitrary type are compared against `L` up to isomorphism.
-/
def CompleteExcludedMinorList (p m : ℕ) [Fact p.Prime]
    (L : Set (Matroid ℕ)) : Prop :=
  L.Finite ∧
    (∀ N ∈ L, N.Finite ∧ IsExcludedMinorFor (IsGFRepresentable p m) N) ∧
      (∀ N₁ ∈ L, ∀ N₂ ∈ L, N₁ ≠ N₂ → IsEmpty (N₁ ≂ N₂)) ∧
        (∀ {β : Type u} (M : Matroid β), M.Finite →
          ¬ IsGFRepresentable p m M → ∃ N ∈ L, Nonempty (N ≤i M))

/- Rota's Conjecture for the prime power `pᵐ`: a complete finite list of
excluded minors for GF(pᵐ)-representability exists. -/
def RotaConj (p m : ℕ) [Fact p.Prime] : Prop :=
  ∃ L : Set (Matroid ℕ), CompleteExcludedMinorList.{u} p m L

/-
The universal challenge: for every field size `r` that is a prime
power (witnessed by some prime `p` and positive exponent `m` with
`r = pᵐ`), a complete finite list of excluded minors for
GF(pᵐ)-representability exists. This is Rota's conjecture. (already proven by Geelen)
-/
theorem P002 (r p m : ℕ) [Fact p.Prime] (hm : 0 < m) (hr : r = p ^ m) :
    RotaConj p m := sorry
