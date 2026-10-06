import Mathlib.Data.Fintype.Card

/- Paper: Helly-type theorems for the ordering of the vertices of a hypergraph
(Biró–Lehel–Tóth, arXiv:2209.14258).  Statement adopted 2026-09-08 from the `P090`
formalisation of branch `vb/Folders`, which adds the sharpness clause of Theorem 1. -/

/-!
# Helly-type theorems for ordering marked hypergraphs

This file formalizes Theorem 1 of the paper by Csaba Biro, Jeno Lehel, and
Geza Toth, including the assertion that the Helly number `2r-2` is sharp.

## Dependency map

* Section 2: complete `r`-uniform hypergraphs with two boundary vertices in
  each edge, and agreeing linear orders.
* Theorem 4: the Helly implication for `r = 3`, proved using the equivalence
  relation determined by a chosen vertex.
* Lemma 5: for `r ≥ 4` and at least `2r-3` vertices, an agreeing order is
  unique up to reversal.
* Lemma 6: under the local `2r-2` hypothesis there are exactly two extremal
  vertices.
* The observation following Lemma 6: extremal vertices occur at the ends of
  every local agreeing order.
* Theorem 7: induction after deleting an extremal vertex proves the global
  agreeing order for `r ≥ 4`.
* The explicit construction on `2r-2` vertices in Theorem 7 proves that the
  number `2r-2` cannot be lowered.

An order on a finite subset `U` is represented by an injective rank function
`V → ℕ` on `U`.  This avoids introducing an arbitrary global order on vertices
outside `U` while remaining equivalent to a finite linear ordering.
-/

namespace MarkedHypergraphHelly

attribute [local instance] Classical.dec

/-! ## Marked complete uniform hypergraphs -/

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
between that edge's two marked boundary vertices.
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

/-- The local hypothesis appearing in Theorem 1. -/
def HasLocalAgreeingOrders [Fintype V]
    (H : TwoExtremeMarkedClique V r) (size : ℕ) : Prop :=
  ∀ U : Finset V, U.card = size → H.HasAgreeingOrderOn U

theorem hasLocalAgreeingOrders_of_global [Fintype V]
    (H : TwoExtremeMarkedClique V r)
    (hglobal : H.HasAgreeingOrderOn Finset.univ) (size : ℕ) :
    H.HasLocalAgreeingOrders size := by
  intro U _hU
  exact H.local_agreeingOrder_of_global hglobal U

end TwoExtremeMarkedClique

/-! ## Sharp Helly statement -/

/-- The counterexample clause asserting sharpness of the Helly number. -/
def HasSharpExample (r : ℕ) : Prop :=
  ∃ H : TwoExtremeMarkedClique (Fin (2 * r - 2)) r,
    H.HasLocalAgreeingOrders (2 * r - 3) ∧
      ¬ H.HasAgreeingOrderOn Finset.univ

/-! ## Main theorem -/

/--
**Theorem 1.** For `r ≥ 3`, a 2-extreme marked `r`-uniform clique on at least
`2r-2` vertices has a global agreeing order exactly when every `2r-2` vertex
subset has one.  Moreover, `2r-2` is the smallest possible Helly number.
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
