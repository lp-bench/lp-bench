import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

variable {V W : Type*}
variable {G : SimpleGraph V} {H : SimpleGraph W}

open SimpleGraph

/-- A decomposition of `G` modelled on `H` by parts `bags w`, subgraphs of `G` that need not be
induced: together the parts cover every vertex and every edge of `G` (`cond₁`), and for every
vertex `v` the nodes whose part contains `v` induce a connected subgraph of `H` (`cond₂`). -/
structure Decomposition (G : SimpleGraph V) (H : SimpleGraph W) where
  bags : W → Subgraph G
  cond₁ : ⨆ w : W, bags w = (⊤ : Subgraph G)
  cond₂ : ∀ v : V, (H.induce {w | v ∈ (bags w).verts}).Connected

namespace Decomposition

/-- The set of nodes of `H` whose part contains the vertex `v`. -/
def dual_bags (S : Decomposition G H) (v : V) : Set W := {w | v ∈ (S.bags w).verts}

/-- Every vertex of `G` lies in some part. -/
lemma exists_bag (S : Decomposition G H) (x : V) :
    ∃ w, x ∈ (S.bags w).verts := by
  have hx : x ∈ (⨆ w, S.bags w).verts := by
    rw [S.cond₁, Subgraph.verts_top]; exact Set.mem_univ x
  rw [Subgraph.verts_iSup, Set.mem_iUnion] at hx
  exact hx

/-- Both ends of every edge of `G` lie in a common part. -/
lemma exists_bag_of_adj (S : Decomposition G H) {x y : V} (h : G.Adj x y) :
    ∃ w, x ∈ (S.bags w).verts ∧ y ∈ (S.bags w).verts := by
  have hadj : (⨆ w, S.bags w).Adj x y := by rw [S.cond₁]; exact (Subgraph.top_adj).2 h
  rw [Subgraph.iSup_adj] at hadj
  obtain ⟨w, hw⟩ := hadj
  exact ⟨w, hw.fst_mem, hw.snd_mem⟩

/-- The union `⋃_{w ∈ U} V_w` of the vertex sets of the parts at the nodes in `U`. -/
def side (S : Decomposition G H) (U : Set W) : Set V := ⋃ w ∈ U, (S.bags w).verts

end Decomposition

/-- A graph-decomposition of `G` modelled on `H` (Definition 3.2 of Diestel–Jacobs–Knappe–Kurkofka,
arXiv:2207.04855): bags `bag h ⊆ V(G)` whose induced subgraphs `G[bag h]` cover every vertex and
every edge of `G` (`cond₁`), such that for every vertex `v` the nodes `h` with `v ∈ bag h` induce
a connected subgraph of `H` (`cond₂`). -/
structure GraphDecomp (G : SimpleGraph V) (H : SimpleGraph W) where
  bag : W → Set V
  cond₁ : ⨆ w : W, (⊤ : G.Subgraph).induce (bag w) = ⊤
  cond₂ : ∀ v : V, (H.induce {h : W | v ∈ bag h}).Connected

namespace GraphDecomp

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- The union `⋃_{h ∈ U} V_h` of the bags at the nodes in `U`. -/
def side (D : GraphDecomp G H) (U : Set W) : Set V :=
  {x : V | ∃ h, h ∈ U ∧ x ∈ D.bag h}

end GraphDecomp

/-- The graph-decomposition whose bags are the vertex sets of the parts of `S`. -/
def Decomposition.toGraphDecomp (S : Decomposition G H) : GraphDecomp G H where
  bag w := (S.bags w).verts
  cond₁ := by
    refine le_antisymm le_top ?_
    refine ⟨?_, ?_⟩
    · intro x _
      obtain ⟨w, hw⟩ := S.exists_bag x
      rw [Subgraph.verts_iSup, Set.mem_iUnion]
      exact ⟨w, hw⟩
    · intro x y hxy
      obtain ⟨w, hxw, hyw⟩ := S.exists_bag_of_adj (Subgraph.top_adj.mp hxy)
      rw [Subgraph.iSup_adj]
      exact ⟨w, hxw, hyw, hxy⟩
  cond₂ := S.cond₂

/-- The decomposition whose parts are the induced subgraphs `G[bag h]` of `D`. -/
def GraphDecomp.induced (D : GraphDecomp G H) : Decomposition G H where
  bags w := (⊤ : Subgraph G).induce (D.bag w)
  cond₁ := D.cond₁
  cond₂ := D.cond₂

/-- A tree-decomposition: a graph-decomposition whose model graph `H` is a tree. -/
structure TreeDecomp (G : SimpleGraph V) (H : SimpleGraph W)
  extends GraphDecomp G H where
  isTree : H.IsTree

namespace TreeDecomp

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- A tree-decomposition as a decomposition whose parts are the induced subgraphs on the bags. -/
def toDecomposition (D : TreeDecomp G H) : Decomposition G H := D.toGraphDecomp.induced

end TreeDecomp
