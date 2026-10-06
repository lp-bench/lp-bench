/-
Copyright (c) 2025 ProofBench participants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProofBench participants
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Order.Filter.Defs
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected

public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.Connected
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Maps
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Paths
public import Mathlib.Order.Filter.Finite

/-! # Minors -/

@[expose] public section

open Function
open scoped Finset

variable {V W X Y : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph X}
  {J : SimpleGraph Y} {v v₁ v₂ : V} {w w₁ w₂ : W} {k l : ℕ}

namespace SimpleGraph

/- The data witnessing that `H` is a minor of `G`, as simple graphs. -/
structure Minor (H : SimpleGraph W) (G : SimpleGraph V) where
  /- The branch sets of the minor. Seeing the minor as a quotient graph,
  `branchSet w` is exactly the fiber of `w` under the quotient map. -/
  branchSet : W → Set V
  /- The branch sets are pairwise disjoint. -/
  pairwise_disjoint_branchSet : Pairwise fun w₁ w₂ ↦ Disjoint (branchSet w₁) (branchSet w₂)
  /- Each branch set is connected (in particular nonempty). -/
  connectedOn_branchSet (w : W) : G.ConnectedOn (branchSet w)
  /- Adjacency in the minor induce adjacency between some points
  of the corresponding branch set. -/
  exists_mem_branchSet_of_adj ⦃w₁ w₂ : W⦄ :
    H.Adj w₁ w₂ → ∃ v₁ ∈ branchSet w₁, ∃ v₂ ∈ branchSet w₂, G.Adj v₁ v₂

namespace Minor

variable {M N : Minor H G}

lemma branchSet_injective : Injective (branchSet : Minor H G → W → Set V) := by
  rintro ⟨M⟩ ⟨N⟩; congr!

instance : PartialOrder (Minor H G) := .lift branchSet branchSet_injective

/-- The support of a minor is the union of its branch sets. -/
def support (M : Minor H G) : Set V := ⋃ w, M.branchSet w

/-- Two minors are said to be disjoint if their branch sets are disjoint. -/
protected def Disjoint (M : Minor H G) (N : Minor I G) : Prop :=
  ∀ w x, Disjoint (M.branchSet w) (N.branchSet x)

instance [IsEmpty W] : Subsingleton (Minor H G) := branchSet_injective.subsingleton

@[simp] lemma branchSet_nonempty (M : Minor H G) (w : W) : (M.branchSet w).Nonempty := by
  simpa using (M.connectedOn_branchSet w).nonempty

lemma nonempty [Nonempty W] (M : Minor H G) : Nonempty V :=
  (M.branchSet_nonempty <| Classical.arbitrary _).to_type

@[simp] lemma preconnectedOn_branchSet (M : Minor H G) (w : W) :
    G.PreconnectedOn (M.branchSet w) := (M.connectedOn_branchSet w).preconnectedOn

/-- A minor is said to be finite if every branch set is finite. -/
protected def Finite (M : Minor H G) : Prop := ∀ w, (M.branchSet w).Finite

open scoped Classical in
/-- A witness that two branch sets are adjacent.

The following properties hold:
* `M.branchSetWitness w₁ w₂` is adjacent to `M.branchSetWitness w₂ w₁`
if `w₁` and `w₂` are adjacent
* `M.branchSetWitness w₁ w₂ ∈ M.branchSet w₁` always
-/
noncomputable def branchSetWitness (M : Minor H G) (w₁ w₂ : W) : V :=
  if hw : H.Adj w₁ w₂ then
    if WellOrderingRel w₁ w₂ then
      (M.exists_mem_branchSet_of_adj hw).choose
    else
      (M.exists_mem_branchSet_of_adj hw.symm).choose_spec.2.choose
  else
    (M.branchSet_nonempty w₁).choose

/-- A subgraph is a minor. -/
def ofInjective (f : H →g G) (hf : Injective f) : Minor H G where
  branchSet w := {f w}
  pairwise_disjoint_branchSet := by simpa
  connectedOn_branchSet := by simp
  exists_mem_branchSet_of_adj _ _ := by simpa using f.map_adj

/-- An induced subgraph is a minor. -/
abbrev ofEmbedding (f : H ↪g G) : Minor H G := .ofInjective f.toHom f.injective

/-- Isomorphic graphs are minors of each other. -/
abbrev ofIso (f : H ≃g G) : Minor H G := .ofInjective f.toHom f.injective

/-- A subgraph is a minor. -/
protected abbrev subgraph (H' : H.Subgraph) : Minor H'.coe H :=
  .ofInjective H'.hom Subtype.val_injective

/-- The empty graph is a minor of all graphs. -/
def ofIsEmpty [IsEmpty W] : H.Minor G where
  branchSet := isEmptyElim
  pairwise_disjoint_branchSet := by simp
  connectedOn_branchSet := by simp
  exists_mem_branchSet_of_adj := by simp

variable (H G) in
/-- Any graph is a minor of its box product with any other graph. -/
@[simps!]
protected def boxProdLeft (v : V) : H.Minor (H □ G) := .ofEmbedding (boxProdLeft _ _ v)

/-- Two vertices belonging to adjacent branch sets are connected by a path lying wholly in those two
branch sets. -/
lemma reachableOn_branchSet_union_branchSet_of_adj (M : Minor H G) (hw : H.Adj w₁ w₂)
    (hv₁ : v₁ ∈ M.branchSet w₁) (hv₂ : v₂ ∈ M.branchSet w₂) :
    G.ReachableOn (M.branchSet w₁ ∪ M.branchSet w₂) v₁ v₂ := by
  obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ := M.exists_mem_branchSet_of_adj hw
  obtain ⟨p₁⟩ := M.preconnectedOn_branchSet w₁ hv₁ hu₁
  obtain ⟨p₂⟩ := M.preconnectedOn_branchSet w₂ hu₂ hv₂
  exact ⟨p₁.append <| hu.toWalk.append p₂, by simp +contextual [or_imp, *]⟩

/-- Two vertices belonging to reachable branch sets are connected by a path lying wholly in the
union of the branch sets the path goes through. -/
lemma reachableOn_biUnion_branchSet (M : Minor H G) {s : Set W} (hw : H.ReachableOn s w₁ w₂)
    (hv₁ : v₁ ∈ M.branchSet w₁) (hv₂ : v₂ ∈ M.branchSet w₂) :
    G.ReachableOn (⋃ w ∈ s, M.branchSet w) v₁ v₂ := by
  have ⟨p, hp⟩ := hw
  induction p generalizing v₁ with
  | @nil w₁ =>
    exact (M.preconnectedOn_branchSet w₁ hv₁ hv₂).mono <| Set.subset_iUnion₂ _ <| hp <| by simp
  | @cons w₁ w₁' w₂ hw' p ih =>
    obtain ⟨v₁', hv₁'⟩ := M.branchSet_nonempty w₁'
    refine ((M.reachableOn_branchSet_union_branchSet_of_adj hw' hv₁ hv₁').mono ?_).trans <|
      ih ⟨p, fun w hw ↦ hp <| by simp [hw]⟩ hv₁' hv₂ (fun w hw ↦ hp <| by simp [hw])
    apply Set.union_subset <;>
      exact Set.subset_iUnion₂ (s := fun w _ ↦ M.branchSet w) _ <| hp <| by simp

/-- If `I` is a minor of `H` and `H` is a minor of `G`, then `I` is a minor of `G`. -/
@[simps]
def comp (M : Minor H G) (N : Minor I H) : Minor I G where
  branchSet x := ⋃ w ∈ N.branchSet x, M.branchSet w
  pairwise_disjoint_branchSet x y hxy := by
    simp only [Set.disjoint_iUnion_right, Set.disjoint_iUnion_left]
    refine fun w₁ hw₁ w₂ hw₂ ↦ M.pairwise_disjoint_branchSet ?_
    rintro rfl
    exact Set.disjoint_left.1 (N.pairwise_disjoint_branchSet hxy) hw₂ hw₁
  connectedOn_branchSet x :=  by
    simp only [ConnectedOn, Set.nonempty_iUnion, branchSet_nonempty, exists_prop, and_true,
      PreconnectedOn, Set.mem_iUnion, forall_exists_index, and_imp]
    refine ⟨N.branchSet_nonempty x, fun v₁ w₁ hw₁ hv₁ v₂ w₂ hw₂ hv₂ ↦ ?_⟩
    exact M.reachableOn_biUnion_branchSet (N.preconnectedOn_branchSet _ hw₁ hw₂) hv₁ hv₂
  exists_mem_branchSet_of_adj x₁ x₂ hx :=
    let ⟨w₁, hw₁, w₂, hw₂, hw⟩ := N.exists_mem_branchSet_of_adj hx
    let ⟨v₁, hv₁, v₂, hv₂, hv⟩ := M.exists_mem_branchSet_of_adj hw
    ⟨v₁, Set.mem_biUnion hw₁ hv₁, v₂, Set.mem_biUnion hw₂ hv₂, hv⟩

open scoped Set.Notation in
/-- If a minor `H` of `G` lies wholly within a set `s`, then `H` is also a minor of `G[s]`. -/
@[simps]
protected def induce (M : H.Minor G) (s : Set V) (hM : ∀ w, M.branchSet w ⊆ s) :
    H.Minor G[s] where
  branchSet w := s ↓∩ M.branchSet w
  pairwise_disjoint_branchSet _w₁ _w₂ hw := (M.pairwise_disjoint_branchSet hw).preimage _
  connectedOn_branchSet _w := (M.connectedOn_branchSet _).induce <| hM _
  exists_mem_branchSet_of_adj _w₁ _w₂ hw :=
    let ⟨v₁, hv₁, v₂, hv₂, hv⟩ := M.exists_mem_branchSet_of_adj hw
    ⟨⟨v₁, hM _ hv₁⟩, hv₁, ⟨v₂, hM _ hv₂⟩, hv₂, hv⟩

/-- Disjoint minors can be put together. -/
def boxProdEmptyGraph {ι : Type*} (M : ι → Minor H G)
    (h : Pairwise fun i j ↦ (M i).Disjoint (M j)) : Minor (H □ .emptyGraph ι) G where
  branchSet v := (M v.2).branchSet v.1
  pairwise_disjoint_branchSet := by
    simp only [Pairwise, ne_eq, Prod.forall, Prod.mk.injEq, not_and]
    intro w₁ i w₂ j hij
    obtain rfl | hij := eq_or_ne i j
    · exact (M _).pairwise_disjoint_branchSet (by simpa using hij)
    · exact h hij _ _
  connectedOn_branchSet w := (M _).connectedOn_branchSet _
  exists_mem_branchSet_of_adj := by
    simpa using fun w₁ i w₂ hw ↦ (M _).exists_mem_branchSet_of_adj hw

/-- Disjoint minors can be put together. -/
protected def sum (M : Minor H G) (N : Minor I G) (hMN : M.Disjoint N) :
    Minor (H ⊕g I) G where
  branchSet
  | .inl w => M.branchSet w
  | .inr x => N.branchSet x
  pairwise_disjoint_branchSet
  | .inl w₁, .inl w₂, hw => M.pairwise_disjoint_branchSet (by simpa using hw)
  | .inl w, .inr x, _ => hMN _ _
  | .inr x, .inl w, _ => (hMN _ _).symm
  | .inr x₁, .inr x₂, hx => N.pairwise_disjoint_branchSet (by simpa using hx)
  connectedOn_branchSet
  | .inl w => M.connectedOn_branchSet _
  | .inr x => N.connectedOn_branchSet _
  exists_mem_branchSet_of_adj
  | .inl u, .inl v, huv => by simpa using M.exists_mem_branchSet_of_adj huv
  | .inl u, .inr v, huv => by simp at huv
  | .inr u, .inl v, huv => by simp at huv
  | .inr u, .inr v, huv => by simpa using N.exists_mem_branchSet_of_adj huv

/-- Minors with the same branch sets can be put together. -/
protected def sup {H₁ H₂ : SimpleGraph W} (M₁ : Minor H₁ G) (M₂ : Minor H₂ G)
    (h : M₁.branchSet = M₂.branchSet) : Minor (H₁ ⊔ H₂) G where
  __ := M₁
  exists_mem_branchSet_of_adj
  | w₁, w₂, .inl hw => M₁.exists_mem_branchSet_of_adj hw
  | w₁, w₂, .inr hw => by simpa [h] using M₂.exists_mem_branchSet_of_adj hw

end Minor

/-- A graph `H` is a minor of a graph `G` if one can collapse a bunch of points together and remove
a bunch of edges from `G` and get `H`, i.e. more conceptually if `H` is a subquotient of `G`. -/
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop := Nonempty (Minor H G)

/-! ### 2-connected minors -/

namespace Minor

/-- A minor is preserved under edge deletion. -/
@[simps]
protected def deleteEdges (M : H.Minor G) (s : Set (Sym2 W)) (t : Set (Sym2 V))
    (hst : ∀ w₁ w₂, ∀ v₁ ∈ M.branchSet w₁, ∀ v₂ ∈ M.branchSet w₂, s(v₁, v₂) ∈ t →
      w₁ ≠ w₂ ∧ s(w₁, w₂) ∈ s) :
    (H.deleteEdges s).Minor (G.deleteEdges t) where
  branchSet := M.branchSet
  pairwise_disjoint_branchSet := M.pairwise_disjoint_branchSet
  connectedOn_branchSet w :=
    (M.connectedOn_branchSet _).deleteEdges fun v₁ hv₁ v₂ hv₂ hv ↦ (hst _ _ _ hv₁ _ hv₂ hv).1 rfl
  exists_mem_branchSet_of_adj w₁ w₂ hw := by
    obtain ⟨v₁, hv₁, v₂, hv₂, hv⟩ := M.exists_mem_branchSet_of_adj (deleteEdges_le _ hw)
    simp only [deleteEdges_adj] at hw ⊢
    exact ⟨v₁, hv₁, v₂, hv₂, hv, fun hv' ↦ hw.2 (hst _ _ _ hv₁ _ hv₂ hv').2⟩
end Minor
end SimpleGraph
