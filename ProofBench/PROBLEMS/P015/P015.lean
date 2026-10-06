import Matroid.Representation.Basic
import Mathlib.Data.Complex.Basic

open Function Matroid

variable {α : Type*} (M : Matroid α) (X : Set α)

/- Complex-representable matroid -/
def IsComplexRepresentable (M : Matroid α) : Prop :=
  ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W),
    Nonempty (M.Rep ℂ W)

structure FlatsInDirectSum (F₁ F₂ : Set α) where
  flat₁ := M.IsFlat F₁
  flat₂ := M.IsFlat F₂
  flat_union := M.IsFlat (F₁ ∪ F₂)
  rank_cond := M.eRk (F₁ ∪ F₂) = M.eRk F₁ + M.eRk F₂

lemma IsPoint.nonempty (h : IsPoint M X) : X.Nonempty := by
  unfold IsPoint at h
  by_contra h_c
  push Not at h_c
  subst h_c
  simp at h

theorem isPoint_iff_singleton [Simple M] {P : Set α} :
    IsPoint M P ↔ ∃ p ∈ M.E, P = {p} := by
  constructor
  · intro h
    obtain ⟨ p, h₁ , h₂ ⟩ := isPoint_iff_exists_eq_closure_isNonloop.mp h
    use p
    have hp : p ∈ M.E := by aesop_mat
    simp_all
  · intro ⟨p, hp⟩
    rw [isPoint_iff_exists_eq_closure_isNonloop]
    use p
    constructor
    · simp only [ Simple.isNonloop_of_mem _ hp.1 ]
    · simp_all

variable {ι : Type*} [Fintype ι]

def directSumOfSubsets (flats : ι → Set α)
    (h_disj : Pairwise (Disjoint on fun i ↦ flats i))
    := Matroid.disjointSigma (fun i ↦ M.restrict (flats i))
    (by simpa [Matroid.restrict] using h_disj)

/- A rank-k flat with exactly k points (elementary flat) -/
structure IsElementaryFlat (F : Set α) where
  isFlat : M.IsFlat F
  pointCount : Nat.card {p // IsPoint M p ∧ p ⊆ F} = M.eRk F

def HasTwoPointLine := ∃ (L : Set α), IsElementaryFlat M L ∧ M.IsLine L

/- A family of matroids, one for each possible ground set type. -/
def MatroidFamily := ∀ (α : Type), Set (Matroid α)

/- A matroid family is minor-closed if for all M in the family, for all N,
  if N is isomorphic to a minor of M, then N is also in the family. -/
def IsMinorClosed (ℳ : MatroidFamily) : Prop :=
  ∀ (α β : Type) (M : Matroid α) (N : Matroid β),
    M ∈ ℳ α → IsoMinor N M → N ∈ ℳ β

structure OrdinaryFlat where
  (carrier : Set α)
  (isFlat : M.IsFlat carrier)
  (pt : Set α)
  (hyperplane : Set α)
  (isPoint : IsPoint M pt)
  (hyper_rank : M.eRk hyperplane = M.eRk carrier - 1)
  (directSum : FlatsInDirectSum M pt hyperplane)
  (eq : carrier = pt ∪ hyperplane)


/-
Every rank-4 complex-representable matroid has a two-point line.
-/
/- The family of all complex-representable matroids. -/
def ComplexRepresentableFamily : MatroidFamily :=
  fun α => {M : Matroid α | IsComplexRepresentable M}

theorem P015 {k : ℕ} (hk : 2 ≤ k) {α : Type} (M : Matroid α)
    (hM : IsComplexRepresentable M) (hrank : M.eRank ≥ 4 * (k - 1)) :
    ∃ F : OrdinaryFlat M, M.eRk F.carrier = k := by
  sorry



-- UNUSED
/-
def isElem_iff_Ord [Simple M] (F : Set α) :
IsElementaryFlat M F ≃ IsOrdinaryFlat M F := by sorry


/- Ordinary Flat - Structure with explicit point and hyperplane -/
structure IsOrdinaryFlat (F : Set α) where
  isFlat : M.IsFlat F
  pt : Set α
  hyperplane : Set α
  isPoint : IsPoint M pt
  hyper_rank : M.eRk hyperplane = (M.eRk F - 1)
  directSum : FlatsInDirectSum M pt hyperplane
  eq : F = pt ∪ hyperplane

lemma IsElementaryFlat_iff_directsum_pts (F : Set α) :
  IsElementaryFlat M F <-> ∃ (pts : Fin k → Set α) (h_disj : Pairwise (Disjoint on pts)),
    (∀ i, IsPoint M (pts i)) ∧
    M.restrict F = directSumOfSubsets M pts h_disj := by

    sorry

theorem directSumOfFlats_eq_restrict (flats : ι → Set α)
    (h_flat : ∀ i, M.IsFlat (flats i))
    (h_disj : Pairwise (Disjoint on flats))
    (h_rank : M.eRk (⋃ i, flats i) = ∑ i, M.eRk (flats i)) :
    directSumOfSubsets M flats h_disj = M.restrict (⋃ i, flats i) := by
  unfold directSumOfSubsets
  ext I
  · sorry
  · sorry

def FlatDirectSum (F₁ F₂ : Set α) (_ : FlatsInDirectSum M F₁ F₂) : Set α :=
  F₁ ∪ F₂

-/
