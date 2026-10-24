import Mathlib.Data.Fintype.Card

namespace MarkedHypergraphHelly

attribute [local instance] Classical.dec

/-- An edge of the complete `r`-uniform hypergraph on `V`. -/
abbrev UniformEdge (V : Type*) (r : ℕ) :=
  {e : Finset V // e.card = r}

/--
A 2-extreme marked `r`-uniform clique: every `r`-set is an edge and has two
distinguished boundary vertices belonging to that edge.
-/
structure TwoExtremeMarkedClique (V : Type*) (r : ℕ) where
  boundary : UniformEdge V r → Finset V
  boundary_subset : ∀ e, boundary e ⊆ e.1
  boundary_card : ∀ e, (boundary e).card = 2

namespace TwoExtremeMarkedClique

variable {V : Type*} {r : ℕ}

/--
The rank function orders `U` injectively and puts every vertex of each edge
inside `U` between that edge's two boundary vertices.  A rank function
injective on `U` is the same as a linear order on `U`.
-/
def AgreesWithOn (H : TwoExtremeMarkedClique V r) (U : Finset V)
    (rank : V → ℕ) : Prop :=
  Set.InjOn rank (U : Set V) ∧
    ∀ e : UniformEdge V r, e.1 ⊆ U →
      ∃ lo hi : V,
        H.boundary e = {lo, hi} ∧ rank lo < rank hi ∧
          ∀ v ∈ e.1, rank lo ≤ rank v ∧ rank v ≤ rank hi

/-- A subset admits an agreeing linear order. -/
def HasAgreeingOrderOn (H : TwoExtremeMarkedClique V r) (U : Finset V) : Prop :=
  ∃ rank : V → ℕ, H.AgreesWithOn U rank

/-- An agreeing order on `U` restricts to every subset of `U`. -/
theorem HasAgreeingOrderOn.mono {H : TwoExtremeMarkedClique V r}
    {U W : Finset V} (hU : H.HasAgreeingOrderOn U) (hWU : W ⊆ U) :
    H.HasAgreeingOrderOn W := by
  rcases hU with ⟨rank, hinj, hagree⟩
  refine ⟨rank, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hinj (hWU hx) (hWU hy) hxy
  · intro e heW
    exact hagree e (heW.trans hWU)

/-- A global agreeing order restricts to every local vertex set. -/
theorem local_agreeingOrder_of_global [Fintype V]
    (H : TwoExtremeMarkedClique V r)
    (hglobal : H.HasAgreeingOrderOn Finset.univ) (U : Finset V) :
    H.HasAgreeingOrderOn U :=
  hglobal.mono (Finset.subset_univ U)

/-- Every vertex set of the given size has an agreeing order. -/
def HasLocalAgreeingOrders [Fintype V]
    (H : TwoExtremeMarkedClique V r) (size : ℕ) : Prop :=
  ∀ U : Finset V, U.card = size → H.HasAgreeingOrderOn U

/-- A global agreeing order gives agreeing orders on all sets of any size. -/
theorem hasLocalAgreeingOrders_of_global [Fintype V]
    (H : TwoExtremeMarkedClique V r)
    (hglobal : H.HasAgreeingOrderOn Finset.univ) (size : ℕ) :
    H.HasLocalAgreeingOrders size := by
  intro U _hU
  exact H.local_agreeingOrder_of_global hglobal U

end TwoExtremeMarkedClique

/--
Sharpness: some marked `r`-clique on `2r-2` vertices has agreeing orders on
all `(2r-3)`-sets but no global agreeing order.
-/
def HasSharpExample (r : ℕ) : Prop :=
  ∃ H : TwoExtremeMarkedClique (Fin (2 * r - 2)) r,
    H.HasLocalAgreeingOrders (2 * r - 3) ∧
      ¬ H.HasAgreeingOrderOn Finset.univ

/--
For `r ≥ 3`, a 2-extreme marked `r`-uniform clique on at least `2r-2`
vertices has a global agreeing order exactly when every `2r-2` vertex subset
has one, and `2r-2` cannot be lowered.
Theorem 1 of Biró–Lehel–Tóth, arXiv:2209.14258.
-/
theorem P051 (r : ℕ) (hr : 3 ≤ r) :
    (∀ (V : Type) [Fintype V],
      2 * r - 2 ≤ Fintype.card V →
        ∀ H : TwoExtremeMarkedClique V r,
          H.HasAgreeingOrderOn Finset.univ ↔
            H.HasLocalAgreeingOrders (2 * r - 2)) ∧
      HasSharpExample r := by
  sorry

end MarkedHypergraphHelly
