import Mathlib.Combinatorics.SimpleGraph.Circulant
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected


universe u

variable {V : Type u} [Fintype V]

/-- The connectivity hypothesis used in Tutte's Wheel Theorem:
`3`-vertex-connectivity in the sense of the shared library definition
`SimpleGraph.IsVertexConnected` (more than `3` vertices, and still connected
after removing any set of fewer than `3` vertices). -/
abbrev IsThreeConnected (G : SimpleGraph V) : Prop :=
  G.IsVertexConnected 3

/-- `G` is a wheel `W n`: a cycle on `n` rim vertices, `n ≥ 3`, plus one hub
adjacent to every rim vertex.  With this indexing, `W 3` is isomorphic to
`K4`, matching the usual graph-theory convention. -/
def IsWheelGraph (G : SimpleGraph V) : Prop :=
  ∃ hub : V, ∃ n : ℕ, 3 ≤ n ∧
    (∃ rim : {v : V // v ≠ hub} ≃ Fin n,
      (∀ v : V, v ≠ hub → G.Adj hub v) ∧
      ∀ a b : {v : V // v ≠ hub},
        G.Adj a.val b.val ↔ (SimpleGraph.cycleGraph n).Adj (rim a) (rim b))

/-- The triangle `cycleGraph 3` joins every pair of distinct vertices. -/
lemma cycleGraph_three_adj (i j : Fin 3) :
    (SimpleGraph.cycleGraph 3).Adj i j ↔ i ≠ j := by
  revert i j
  decide

/-- The nonzero elements of `Fin 4`, enumerated as `Fin 3`. -/
def finFourNeZeroEquiv : {w : Fin 4 // w ≠ 0} ≃ Fin 3 where
  toFun w := ⟨w.1.1 - 1, by
    have h4 := w.1.isLt
    have h0 : w.1.1 ≠ 0 := fun hc => w.2 (Fin.ext hc)
    omega⟩
  invFun i := ⟨⟨i.1 + 1, by omega⟩, fun hc => Nat.succ_ne_zero i.1 (congrArg Fin.val hc)⟩
  left_inv w := by
    have h0 : w.1.1 ≠ 0 := fun hc => w.2 (Fin.ext hc)
    apply Subtype.ext
    apply Fin.ext
    simp
    omega
  right_inv i := by
    apply Fin.ext
    simp

open SimpleGraph in
omit [Fintype V] in
/-- Any graph isomorphic to `K₄` is a wheel: `K₄ = W₃`, with any vertex as
hub and the remaining triangle as rim. -/
theorem isWheelGraph_of_iso_completeGraph [DecidableEq V] {G : SimpleGraph V}
    (e : G ≃g completeGraph (Fin 4)) : IsWheelGraph G := by
  refine ⟨e.toEquiv.symm 0, 3, le_refl 3,
    (e.toEquiv.subtypeEquiv fun x =>
      not_congr (Equiv.eq_symm_apply e.toEquiv)).trans finFourNeZeroEquiv,
    ?_, ?_⟩
  · intro v hv
    apply e.map_adj_iff.mp
    have h0 : e (e.toEquiv.symm 0) = (0 : Fin 4) := e.toEquiv.apply_symm_apply 0
    rw [h0]
    show (0 : Fin 4) ≠ e v
    exact fun hc => hv ((Equiv.eq_symm_apply e.toEquiv).mpr hc.symm)
  · intro a b
    rw [cycleGraph_three_adj]
    constructor
    · intro hadj hc
      exact G.ne_of_adj hadj (congrArg Subtype.val ((Equiv.injective _) hc))
    · intro hne
      have hab : (a : V) ≠ (b : V) := by
        intro hc
        exact hne (congrArg _ (Subtype.ext hc))
      have : (completeGraph (Fin 4)).Adj (e ↑a) (e ↑b) := by
        simp only [completeGraph_eq_top, top_adj]
        exact fun hc => hab (e.toEquiv.injective (by simpa using hc))
      exact e.map_adj_iff.mp this

/-- Delete the edge `{u, v}` from `G`. -/
def DeleteEdge (G : SimpleGraph V) (u v : V) : SimpleGraph V :=
  G.deleteEdges {s(u, v)}

omit [Fintype V] in
/-- Adjacency after deleting one edge. -/
theorem deleteEdge_adj_iff (G : SimpleGraph V) (u v x y : V) :
    (DeleteEdge G u v).Adj x y ↔ G.Adj x y ∧ s(x, y) ≠ s(u, v) := by
  simp only [DeleteEdge, SimpleGraph.deleteEdges_adj,
    Set.mem_singleton_iff, ne_eq]

omit [Fintype V] in
/-- The deleted edge is absent. -/
theorem deleteEdge_not_adj (G : SimpleGraph V) (u v : V) :
    ¬ (DeleteEdge G u v).Adj u v := by
  simp [deleteEdge_adj_iff]

/-- The equivalence relation that identifies the two endpoints of an edge. -/
def contractionRelation (e : Sym2 V) (a b : V) : Prop :=
  a = b ∨ (a ∈ e ∧ b ∈ e)

/-- The setoid used for edge contraction. -/
def contractionSetoid (e : Sym2 V) : Setoid V where
  r := contractionRelation e
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro a b h
      rcases h with rfl | ⟨ha, hb⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hb, ha⟩
    trans := by
      intro a b c h1 h2
      rcases h1 with rfl | ⟨ha, hb⟩
      · exact h2
      · rcases h2 with rfl | ⟨_, hc⟩
        · exact Or.inr ⟨ha, hb⟩
        · exact Or.inr ⟨ha, hc⟩
  }

/-- Vertex type after contracting edge `e`. -/
def ContractedV (e : Sym2 V) : Type u :=
  Quotient (contractionSetoid e)

noncomputable instance contractedVDecidableEq (e : Sym2 V) :
    DecidableEq (ContractedV e) :=
  Classical.decEq _

noncomputable instance contractedVFintype (e : Sym2 V) :
    Fintype (ContractedV e) :=
  Fintype.ofSurjective (Quotient.mk (contractionSetoid e))
    Quotient.mk_surjective

/-- Contract edge `e` in `G`.  Parallel edges created by contraction are
automatically collapsed because the result is a `SimpleGraph`; loops are
discarded by the `x ≠ y` condition. -/
def SimpleGraph.contractEdge (G : SimpleGraph V) (e : Sym2 V) :
    SimpleGraph (ContractedV e) where
  Adj x y :=
    x ≠ y ∧
      ∃ u v : V,
        Quotient.mk (contractionSetoid e) u = x ∧
        Quotient.mk (contractionSetoid e) v = y ∧
        G.Adj u v
  symm := ⟨by
    rintro x y ⟨hne, u, v, rfl, rfl, huv⟩
    exact ⟨hne.symm, v, u, rfl, rfl, huv.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The precise edge conclusion of Tutte's Wheel Theorem for endpoints `u v`:
`u v` is an edge and either deleting it or contracting it leaves a
3-connected graph. -/
def GoodTutteReductionEdge (G : SimpleGraph V) (u v : V) : Prop :=
  u ≠ v ∧ G.Adj u v ∧
    (IsThreeConnected (DeleteEdge G u v) ∨
      IsThreeConnected (G.contractEdge s(u, v)))

/-- **Tutte's Wheel Theorem** (1961), in the form used in proofs of
Kuratowski's Theorem: every 3-connected graph that is not a wheel has an edge
whose deletion or contraction is again 3-connected. -/
theorem P020 (G : SimpleGraph V)
    (h_three_connected : IsThreeConnected G)
    (h_not_wheel : ¬ IsWheelGraph G) :
    ∃ u v : V, GoodTutteReductionEdge G u v := sorry
