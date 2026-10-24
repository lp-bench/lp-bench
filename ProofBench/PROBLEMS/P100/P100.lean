import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Card

namespace TutteDecomposition

universe u

/-- A separation of `G`: the two sides cover the vertex set, no edge joins their private
parts, and both private parts are nonempty. -/
structure Separation {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) where
  A : Finset V
  B : Finset V
  union_eq : A ∪ B = Finset.univ
  no_edge : ∀ u ∈ A \ B, ∀ v ∈ B \ A, ¬ G.Adj u v
  left_nonempty : (A \ B).Nonempty
  right_nonempty : (B \ A).Nonempty

namespace Separation

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The separator of a separation, the intersection of its two sides. -/
def separator (s : Separation G) : Finset V := s.A ∩ s.B

/-- The order of a separation is the size of its separator. -/
def order (s : Separation G) : ℕ := s.separator.card

/-- The separation with its two sides exchanged. -/
def flip (s : Separation G) : Separation G where
  A := s.B
  B := s.A
  union_eq := by rw [Finset.union_comm]; exact s.union_eq
  no_edge u hu v hv h := s.no_edge v hv u hu h.symm
  left_nonempty := s.right_nonempty
  right_nonempty := s.left_nonempty

/-- Two separations are nested if one side of the first is contained in a side of the
second, after possibly exchanging the two sides of either of them. -/
def Nested (s t : Separation G) : Prop :=
  (s.A ⊆ t.A ∧ t.B ⊆ s.B) ∨ (t.A ⊆ s.A ∧ s.B ⊆ t.B) ∨
    (s.A ⊆ t.B ∧ t.A ⊆ s.B) ∨ (s.B ⊆ t.A ∧ t.B ⊆ s.A)

/-- A separation is totally nested if it is nested with every 2-separation of `G`. -/
def TotallyNested (s : Separation G) : Prop :=
  ∀ t : Separation G, t.order = 2 → s.Nested t

end Separation

/-- `G` is `k`-connected: it has more than `k` vertices and no separation of order less
than `k`. -/
def IsKConnected {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ) :
    Prop :=
  k < Fintype.card V ∧ ∀ s : Separation G, k ≤ s.order

/-- A tree-decomposition of `G`: bags indexed by the nodes of a tree, covering every
vertex and every edge, with the nodes holding a fixed vertex spanning a subtree. -/
structure TreeDecomp {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Type u) where
  tree : SimpleGraph W
  isTree : tree.IsTree
  bag : W → Finset V
  cover_vertex : ∀ v : V, ∃ w, v ∈ bag w
  cover_edge : ∀ ⦃u v : V⦄, G.Adj u v → ∃ w, u ∈ bag w ∧ v ∈ bag w
  connected_nodes : ∀ v : V, (tree.induce {w | v ∈ bag w}).Connected

namespace TreeDecomp

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {W : Type u}
  (D : TreeDecomp G W)

/-- The adhesion set of an edge of the decomposition tree. -/
def adhesion (t t' : W) : Finset V := D.bag t ∩ D.bag t'

/-- The nodes lying on the `t`-side of the edge `t t'` of the decomposition tree. -/
def side (t t' : W) : Set W :=
  {w | (D.tree.deleteEdges {s(t, t')}).Reachable w t}

/-- The union of the bags at a set of nodes. -/
def bagUnion (S : Set W) : Set V := {v | ∃ w ∈ S, v ∈ D.bag w}

/-- The edge `t t'` of the decomposition tree induces the separation `s`: the sides of `s`
are the unions of the bags on the two sides of that edge. -/
def Induces (t t' : W) (s : Separation G) : Prop :=
  (↑s.A = D.bagUnion (D.side t t') ∧ ↑s.B = D.bagUnion (D.side t' t)) ∨
    (↑s.A = D.bagUnion (D.side t' t) ∧ ↑s.B = D.bagUnion (D.side t t'))

/-- The torso at a node: its bag, carrying the edges of `G` and, in addition, an edge
between any two vertices sharing another bag adjacent to it — that is, every adhesion set
at that node completed to a clique. -/
def torso (t : W) : SimpleGraph (D.bag t) where
  Adj a b := a ≠ b ∧ (G.Adj a b ∨
    ∃ t', D.tree.Adj t t' ∧ (a : V) ∈ D.bag t' ∧ (b : V) ∈ D.bag t')
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp (fun hadj => hadj.symm)
    fun ⟨t', h1, h2, h3⟩ => ⟨t', h1, h3, h2⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end TreeDecomp

/-- The parts occurring in the Tutte-decomposition: the triconnected components are the
3-connected graphs, the cycles, and `K₂`. -/
def IsTutteTorso {X : Type u} [Fintype X] [DecidableEq X] (H : SimpleGraph X) : Prop :=
  IsKConnected H 3 ∨ (∃ n : ℕ, 3 ≤ n ∧ Nonempty (H ≃g SimpleGraph.cycleGraph n)) ∨
    Nonempty (H ≃g (⊤ : SimpleGraph (Fin 2)))

end TutteDecomposition

open TutteDecomposition

/-- Theorem 2.4 of Bourneuf–Planken, arXiv:2508.06212 (Cunningham–Edmonds 1980), the output
of their linear-time algorithm (Theorem 1.1; the running time is not formalised): a 2-connected
graph has a tree-decomposition of adhesion two with torsos 3-connected, cycles or `K₂`, whose
tree edges induce exactly the totally nested 2-separations. -/
theorem P100 {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (_hG : IsKConnected G 2) :
    ∃ (W : Type u) (D : TreeDecomp G W),
      (∀ t t' : W, D.tree.Adj t t' → (D.adhesion t t').card = 2) ∧
      (∀ t : W, IsTutteTorso (D.torso t)) ∧
      (∀ t t' : W, D.tree.Adj t t' →
        ∃ s : Separation G, s.order = 2 ∧ s.TotallyNested ∧ D.Induces t t' s) ∧
      (∀ s : Separation G, s.order = 2 → s.TotallyNested →
        ∃ t t' : W, D.tree.Adj t t' ∧ D.Induces t t' s) := by
  sorry

/-- Direct corollary: every 2-connected graph has a tree-decomposition of adhesion two all
of whose torsos are 3-connected, cycles or `K₂`. -/
theorem P100_treeDecomp {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : IsKConnected G 2) :
    ∃ (W : Type u) (D : TreeDecomp G W),
      (∀ t t' : W, D.tree.Adj t t' → (D.adhesion t t').card = 2) ∧
      ∀ t : W, IsTutteTorso (D.torso t) := by
  obtain ⟨W, D, hadh, htorso, -, -⟩ := P100 G hG
  exact ⟨W, D, hadh, htorso⟩

/-- Direct corollary: a 3-connected graph has no totally-nested 2-separation, so its
Tutte-decomposition has a single node. -/
theorem P100_noTotallyNested_of_threeConnected {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsKConnected G 3) (s : Separation G) : s.order ≠ 2 :=
  fun h => by have := hG.2 s; omega
