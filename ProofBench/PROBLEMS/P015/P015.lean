import Matroid.Representation.Basic
import Mathlib.Data.Complex.Basic

open Function Matroid

variable {α : Type*} (M : Matroid α) (X : Set α)

/-- `M` is complex-representable: it has a representation in some complex vector space. -/
def IsComplexRepresentable (M : Matroid α) : Prop :=
  ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W),
    Nonempty (M.Rep ℂ W)

/-- `F₁` and `F₂` are flats of `M` in direct sum: their union is a flat whose rank is the sum
of their ranks. -/
structure FlatsInDirectSum (F₁ F₂ : Set α) : Prop where
  flat₁ : M.IsFlat F₁
  flat₂ : M.IsFlat F₂
  flat_union : M.IsFlat (F₁ ∪ F₂)
  rank_cond : M.eRk (F₁ ∪ F₂) = M.eRk F₁ + M.eRk F₂

/-- A point of `M` is nonempty. -/
lemma IsPoint.nonempty (h : IsPoint M X) : X.Nonempty := by
  unfold IsPoint at h
  by_contra h_c
  push Not at h_c
  subst h_c
  simp at h

/-- In a simple matroid the points are exactly the singletons of ground-set elements. -/
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

/-- The direct sum of the restrictions of `M` to a pairwise disjoint family of sets. -/
def directSumOfSubsets (flats : ι → Set α)
    (h_disj : Pairwise (Disjoint on fun i ↦ flats i))
    := Matroid.disjointSigma (fun i ↦ M.restrict (flats i))
    (by simpa [Matroid.restrict] using h_disj)

/-- An elementary flat: a flat whose number of points equals its rank. -/
structure IsElementaryFlat (F : Set α) where
  isFlat : M.IsFlat F
  pointCount : Nat.card {p // IsPoint M p ∧ p ⊆ F} = M.eRk F

/-- `M` has a two-point line: a line containing exactly two points. -/
def HasTwoPointLine := ∃ (L : Set α), IsElementaryFlat M L ∧ M.IsLine L

/-- A family of matroids: a set of matroids on each ground type. -/
def MatroidFamily := ∀ (α : Type), Set (Matroid α)

/-- A matroid family is minor-closed if it contains every matroid isomorphic to a minor of one
of its members. -/
def IsMinorClosed (ℳ : MatroidFamily) : Prop :=
  ∀ (α β : Type) (M : Matroid α) (N : Matroid β),
    M ∈ ℳ α → IsoMinor N M → N ∈ ℳ β

/-- An ordinary flat of `M`: a flat `carrier = pt ∪ hyperplane`, where `pt` is a point, the
flats `pt` and `hyperplane` are in direct sum, and `hyperplane` has rank one less than `carrier`. -/
structure OrdinaryFlat where
  (carrier : Set α)
  (isFlat : M.IsFlat carrier)
  (pt : Set α)
  (hyperplane : Set α)
  (isPoint : IsPoint M pt)
  (hyper_rank : M.eRk hyperplane = M.eRk carrier - 1)
  (directSum : FlatsInDirectSum M pt hyperplane)
  (eq : carrier = pt ∪ hyperplane)

/-- The family of all complex-representable matroids. -/
def ComplexRepresentableFamily : MatroidFamily :=
  fun α => {M : Matroid α | IsComplexRepresentable M}

/-- Every complex-representable matroid of rank at least `4(k - 1)`, `k ≥ 2`, has an ordinary
flat of rank `k` (Geelen–Kroeker, arXiv:2212.03307). -/
theorem P015 {k : ℕ} (hk : 2 ≤ k) {α : Type} (M : Matroid α) [M.Finite]
    (hM : IsComplexRepresentable M) (hrank : M.eRank ≥ 4 * (k - 1)) :
    ∃ F : OrdinaryFlat M, M.eRk F.carrier = k := by
  sorry
