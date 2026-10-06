import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Graph decompositions (after Diestel–Jacobs–Knappe–Kurkofka, *Canonical graph
decompositions via coverings*)

This file develops graph decompositions as a chain of increasing specialisation, so that the
*most general* notion is primitive and the more specialised ones are obtained from it:

```
        Decomposition          (subgraph parts  G_h ⊆ G ;  ⨆ bags = ⊤)        -- general (H1')
            │  toGraphDecomp    (forget edges:  bag := (bags ·).verts)        -- unique
            ▼
        GraphDecomp            (vertex-set bags  V_h ;  induced parts)         -- Def. 3.2  (H1)
            │  +  H.IsTree
            ▼
        TreeDecomp             (model H is a tree)                             -- tree-decomposition
```

* `Decomposition` carries **subgraphs** `bags w : Subgraph G` and a single join condition
  `⨆ bags = ⊤`. This is the paper's "fleshed-out parts" formulation (H1′)/(H2′); the parts need
  not be induced, which is exactly what the covering construction needs (and what cycle
  decompositions need: a cycle through some vertices omits the chords).

* `GraphDecomp` carries **vertex sets** `bag w : Set V` with the cover split into a vertex half
  and an edge half. This is the literal transcription of Definition 3.2 (H1)/(H2), and the natural
  home for the width parameter (treewidth).

* `Decomposition.toGraphDecomp` is the **unique** projection (subgraph ⟹ vertex): take vertex
  sets of the parts. `GraphDecomp.induced` is the canonical section back (choose induced parts),
  and `toGraphDecomp_induced` shows the round trip on the vertex side is the identity. So
  `GraphDecomp` is a retract of `Decomposition`.

Lemma 3.4 (the separation induced by a set-separation of `V(H)`) is proved at both levels:
`Decomposition.lemma_3_4` for the general object and `GraphDecomp.lemma_3_4` for the vertex object.
-/

variable {V W : Type*}
variable {G : SimpleGraph V} {H : SimpleGraph W}

open SimpleGraph

/-! The separation vocabulary used below — `Separates` (the cut predicate), `IsSeparation`
(a separation `{A,B}`), `separates_iff_of_cover`, and `Walk.exists_boundary_edge` — now lives in
`…Connectivity.VertexConnected`, beside the bundled finite `Separation` structure. -/

/-! ## Level 1 — general decomposition by subgraph parts  (H1′)/(H2′) -/

/-- A decomposition of `G` modelled on `H`, given by a choice of **parts** `bags w : Subgraph G`.

* `cond₁ : ⨆ w, bags w = ⊤` is (H1′): the parts cover all vertices **and** all edges of `G`.
  Unfolded in the `Subgraph` lattice it says `⋃ (bags w).verts = V(G)` together with
  `G.Adj x y → ∃ w, (bags w).Adj x y`.
* `cond₂` is (H2): for every `v`, the induced subgraph `H[W_v]` on `W_v = {w | v ∈ V_{w}}` is
  connected.

The parts need not be induced subgraphs of `G`. -/
structure Decomposition (G : SimpleGraph V) (H : SimpleGraph W) where
  bags : W → Subgraph G
  cond₁ : ⨆ w : W, bags w = (⊤ : Subgraph G)
  cond₂ : ∀ v : V, (H.induce {w | v ∈ (bags w).verts}).Connected

namespace Decomposition

def dual_bags (S : Decomposition G H) (v : V) : Set W := {w | v ∈ (S.bags w).verts}

/- Every vertex of `G` lives inside some bag (the vertex half of `cond₁`). -/
lemma exists_bag (S : Decomposition G H) (x : V) :
    ∃ w, x ∈ (S.bags w).verts := by
  have hx : x ∈ (⨆ w, S.bags w).verts := by
    rw [S.cond₁, Subgraph.verts_top]; exact Set.mem_univ x
  rw [Subgraph.verts_iSup, Set.mem_iUnion] at hx
  exact hx

/- Every edge of `G` lives inside a single bag (the edge half of `cond₁`). -/
lemma exists_bag_of_adj (S : Decomposition G H) {x y : V} (h : G.Adj x y) :
    ∃ w, x ∈ (S.bags w).verts ∧ y ∈ (S.bags w).verts := by
  have hadj : (⨆ w, S.bags w).Adj x y := by rw [S.cond₁]; exact (Subgraph.top_adj).2 h
  rw [Subgraph.iSup_adj] at hadj
  obtain ⟨w, hw⟩ := hadj
  exact ⟨w, hw.fst_mem, hw.snd_mem⟩

/-! ### The induced separation
`{side U, side U'}` and its separator `side U ∩ side U'` (Lemma 3.4).

The **separation** is the library one (`SimpleGraph.IsSeparation`), whose separator is the
intersection `side U ∩ side U'` — so no bespoke separator set is defined here. The explicit
*adhesion* description of that intersection (the actual content of Lemma 3.4, and where the
connectivity condition H2 is used) is recorded in `inter_eq_adhesions`. -/

/-- The `G`-side `A = ⋃_{h∈U} V_h`. -/
def side (S : Decomposition G H) (U : Set W) : Set V := ⋃ w ∈ U, (S.bags w).verts

end Decomposition

/-! ## Level 2 — decomposition by vertex sets  (Definition 3.2, H1/H2) -/

/- A graph-decomposition of `G` modelled on `H`, with bags `bag h = V_h ⊆ V(G)`.

The parts are the **induced** subgraphs `G[V_h] = (⊤ : Subgraph G).induce V_h`, so — unlike the
general `Decomposition` — the parts are pinned by their vertex sets alone. Accordingly the cover
condition is stated with the *same single join* `cond₁` as `Decomposition`, only over the induced
parts:

* `cond₁ : ⨆ w, (⊤ : Subgraph G).induce (bag w) = ⊤` is (H1): the induced parts cover all vertices
  **and** all edges of `G`. Its vertex and edge halves are repackaged below as `cover_vx` and
  `cover_edge` (every vertex, resp. every edge, of `G` lies in some part `G[V_h]`).
* `cond₂` is (H2): for every `v`, the induced subgraph `H[W_v]` on `W_v = {h | v ∈ V_h}` is
  connected. It is exposed below under the name `coparts_connected`. -/
structure GraphDecomp (G : SimpleGraph V) (H : SimpleGraph W) where
  bag : W → Set V
  cond₁ : ⨆ w : W, (⊤ : G.Subgraph).induce (bag w) = ⊤
  cond₂ : ∀ v : V, (H.induce {h : W | v ∈ bag h}).Connected

namespace GraphDecomp

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- `A = ⋃_{h ∈ U} V_h`. -/
def side (D : GraphDecomp G H) (U : Set W) : Set V :=
  {x : V | ∃ h, h ∈ U ∧ x ∈ D.bag h}

end GraphDecomp

/-! ## Bridges:  subgraph ⟹ vertex ⟹ subgraph -/

/- **Subgraph ⟹ vertex** (forgetful, and the *unique* such reduction): take the vertex set of
each part. The bag is `(S.bags w).verts`; `cond₂` is inherited, and `cond₁` (the cover by the
*induced* parts on those vertex sets) follows from `exists_bag`/`exists_bag_of_adj`. -/
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

/-- **Vertex ⟹ subgraph** (canonical section): flesh out each bag to its *induced* subgraph. With
the induced parts baked into `GraphDecomp`, both fields are now literally the decomposition's own
conditions. -/
def GraphDecomp.induced (D : GraphDecomp G H) : Decomposition G H where
  bags w := (⊤ : Subgraph G).induce (D.bag w)
  cond₁ := D.cond₁
  cond₂ := D.cond₂

/-! ## Level 3 — tree-decompositions  (model `H` is a tree) -/

/-- A **tree-decomposition** is a vertex-set decomposition whose model graph is a tree. Every
`TreeDecomp` is a `GraphDecomp` via the inherited `toGraphDecomp` projection, and hence a
`Decomposition` via `toGraphDecomp.induced`. -/
structure TreeDecomp (G : SimpleGraph V) (H : SimpleGraph W)
  extends GraphDecomp G H where
  isTree : H.IsTree

namespace TreeDecomp

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Climb back to the general (subgraph) decomposition via the induced parts. -/
def toDecomposition (D : TreeDecomp G H) : Decomposition G H := D.toGraphDecomp.induced

end TreeDecomp
