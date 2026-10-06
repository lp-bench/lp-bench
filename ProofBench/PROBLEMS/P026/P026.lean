import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
============================================================================================
### A Graph Minors Approach to Temporal Sequences
================================================================================================
-/

universe u w

namespace TemporalSequences

/-! ## Edge-labelled graphs -/

/-- A labelled graph has separate finite vertex and edge types. -/
structure LGraph where
  V : Type u
  E : Type u
  instV : Fintype V
  instE : Fintype E
  decV : DecidableEq V
  decE : DecidableEq E
  ends : E → Finset V
  edge_nonempty : ∀ e : E, (ends e).Nonempty
  edge_card_le_two : ∀ e : E, (ends e).card ≤ 2

attribute [instance] LGraph.instV LGraph.instE LGraph.decV LGraph.decE

namespace LGraph

/-- Edges incident with a vertex. -/
def incidentEdges (G : LGraph.{u}) (x : G.V) : Finset G.E :=
  Finset.univ.filter (fun e => x ∈ G.ends e)

/-- Two distinct vertices are adjacent when some labelled edge is incident with both. -/
def Adj (G : LGraph.{u}) (x y : G.V) : Prop :=
  ∃ e : G.E, x ∈ G.ends e ∧ y ∈ G.ends e ∧ x ≠ y

/-- The graph has at least two vertices. -/
def HasAtLeastTwoVertices (G : LGraph.{u}) : Prop :=
  ∃ x y : G.V, x ≠ y

/-- A walk records the labelled edge used at each step. -/
inductive Walk (G : LGraph.{u}) : G.V → G.V → Type u
  | nil {x : G.V} : Walk G x x
  | cons {x y z : G.V} (e : G.E)
      (hx : x ∈ G.ends e) (hy : y ∈ G.ends e)
      (rest : Walk G y z) : Walk G x z

/-- Vertices visited by a walk. -/
def Walk.support {G : LGraph.{u}} {a b : G.V} : G.Walk a b → List G.V
  | Walk.nil => [a]
  | Walk.cons _ _ _ rest => a :: rest.support

/-- Edge labels used by a walk. -/
def Walk.edgeSupport {G : LGraph.{u}} {a b : G.V} : G.Walk a b → List G.E
  | Walk.nil => []
  | Walk.cons e _ _ rest => e :: rest.edgeSupport

/-- A walk stays inside a vertex set and uses only a chosen edge set. -/
def Walk.StaysIn {G : LGraph.{u}} {a b : G.V}
    (w : G.Walk a b) (verts : Finset G.V) (edges : Finset G.E) : Prop :=
  (∀ x ∈ w.support, x ∈ verts) ∧
  ∀ e ∈ w.edgeSupport, e ∈ edges

/-- Connectivity of the whole labelled graph. -/
def Connected (G : LGraph.{u}) : Prop :=
  ∀ x y : G.V, Nonempty (G.Walk x y)

/-- Connectivity after deleting one vertex. -/
def ConnectedAfterDeletingVertex (G : LGraph.{u}) (x : G.V) : Prop :=
  ∀ y z : G.V, y ≠ x → z ≠ x → ∃ w : G.Walk y z, x ∉ w.support

/-- Labelled 2-connectivity. -/
def TwoConnected (G : LGraph.{u}) : Prop :=
  G.Connected ∧ G.HasAtLeastTwoVertices ∧
  ∀ x : G.V, G.ConnectedAfterDeletingVertex x

end LGraph

/-! ## Rotation systems and embeddings -/

/-- A dart is an incidence of an edge with one of its endpoint vertices. -/
abbrev Dart (G : LGraph.{u}) : Type u :=
  Σ e : G.E, {x : G.V // x ∈ G.ends e}

/-- A face system covers every dart. -/
def FacesCoverDarts (G : LGraph.{u}) (faces : Finset (List (Dart G))) : Prop :=
  ∀ d : Dart G, ∃ f ∈ faces, d ∈ f

/-- A face system assigns each dart to a unique face boundary. -/
def FacesUniqueDarts (G : LGraph.{u}) (faces : Finset (List (Dart G))) : Prop :=
  ∀ d : Dart G, ∀ f₁ ∈ faces, ∀ f₂ ∈ faces,
    d ∈ f₁ → d ∈ f₂ → f₁ = f₂

/-- Face boundaries do not repeat darts. -/
def FaceBoundariesNodup (G : LGraph.{u}) (faces : Finset (List (Dart G))) : Prop :=
  ∀ f ∈ faces, f.Nodup

/-- Face boundaries are genuine listed boundaries, not empty placeholders. -/
def FaceBoundariesNonempty (G : LGraph.{u}) (faces : Finset (List (Dart G))) : Prop :=
  ∀ f ∈ faces, f ≠ []

/-- Cyclic consecutiveness in a boundary or rotator list. -/
def CyclicNext {α : Type _} (a b : α) (l : List α) : Prop :=
  (∃ left right, l = left ++ a :: b :: right) ∨
  ∃ middle, l = b :: middle ++ [a]

/-- A rotation system gives a cyclic order of incident edge labels at each vertex. -/
structure RotationSystem (G : LGraph.{u}) where
  rotator : G.V → List G.E
  exactly_incident :
    ∀ x e, e ∈ rotator x ↔ e ∈ G.incidentEdges x
  nodup : ∀ x, (rotator x).Nodup

/-- The next dart on a face follows the usual rotation-after-edge rule. -/
def FaceStep (G : LGraph.{u}) (ρ : RotationSystem G)
    (d d' : Dart G) : Prop :=
  d'.2.1 ∈ G.ends d.1 ∧
  d'.2.1 ≠ d.2.1 ∧
  CyclicNext d.1 d'.1 (ρ.rotator d'.2.1)

/-- Listed face boundaries are traced by the rotation system. -/
def FacesFollowRotation (G : LGraph.{u}) (ρ : RotationSystem G)
    (faces : Finset (List (Dart G))) : Prop :=
  ∀ f ∈ faces, ∀ d d',
    CyclicNext d d' f → FaceStep G ρ d d'

/-- Reversing every local rotator gives the global reorientation. -/
def RotationSystem.reorient {G : LGraph.{u}}
    (ρ : RotationSystem G) : RotationSystem G where
  rotator x := (ρ.rotator x).reverse
  exactly_incident := by
    intro x e
    rw [List.mem_reverse]
    exact ρ.exactly_incident x e
  nodup := by
    intro x
    exact (ρ.nodup x).reverse.imp (by
      intro a b h
      exact h.symm)

/-- A combinatorial planar embedding represented by a rotation system and
explicit face boundaries.  The Euler equation uses the number of listed faces,
so the face count is not a free parameter. -/
structure PlanarEmbedding (G : LGraph.{u}) where
  rotation : RotationSystem G
  faces : Finset (List (Dart G))
  faces_cover_darts : FacesCoverDarts G faces
  faces_unique_darts : FacesUniqueDarts G faces
  face_boundaries_nodup : FaceBoundariesNodup G faces
  face_boundaries_nonempty : FaceBoundariesNonempty G faces
  faces_follow_rotation : FacesFollowRotation G rotation faces
  euler_planar :
    (Fintype.card G.V : ℤ) - (Fintype.card G.E : ℤ) + (faces.card : ℤ) = 2

/-! ## Label-preserving minors with histories -/

/-- Data verifying that `H` is obtained from `G` by deleting one labelled edge. -/
structure EdgeDeletionData (G H : LGraph.{u}) where
  deleted : G.E
  vertexEquiv : H.V ≃ G.V
  edgeEquiv : H.E ≃ {e : G.E // e ≠ deleted}
  ends_respected :
    ∀ e : H.E, ∀ x : H.V,
      x ∈ H.ends e ↔ vertexEquiv x ∈ G.ends (edgeEquiv e).1

/-- Data verifying that `H` is obtained by deleting one isolated vertex. -/
structure IsolatedVertexDeletionData (G H : LGraph.{u}) where
  deleted : G.V
  isolated : ∀ e : G.E, deleted ∉ G.ends e
  vertexEquiv : H.V ≃ {x : G.V // x ≠ deleted}
  edgeEquiv : H.E ≃ G.E
  ends_respected :
    ∀ e : H.E, ∀ x : H.V,
      x ∈ H.ends e ↔ (vertexEquiv x).1 ∈ G.ends (edgeEquiv e)

/-- Data verifying that `H` is obtained from `G` by contracting one edge. -/
structure EdgeContractionData (G H : LGraph.{u}) where
  contracted : G.E
  quotient : G.V → H.V
  quotient_surjective : Function.Surjective quotient
  contracted_endpoints_identified :
    ∀ x ∈ G.ends contracted, ∀ y ∈ G.ends contracted, quotient x = quotient y
  quotient_exact :
    ∀ x y : G.V, quotient x = quotient y ↔
      x = y ∨ (x ∈ G.ends contracted ∧ y ∈ G.ends contracted)
  edgeEquiv : H.E ≃ {e : G.E // e ≠ contracted}
  ends_respected :
    ∀ e : H.E, ∀ z : H.V,
      z ∈ H.ends e ↔ ∃ x ∈ G.ends (edgeEquiv e).1, quotient x = z

/-- Data verifying that `H` is obtained from `G` by relabelling vertices. -/
structure VertexRelabellingData (G H : LGraph.{u}) where
  vertexEquiv : G.V ≃ H.V
  edgeEquiv : G.E ≃ H.E
  ends_respected :
    ∀ e : G.E, ∀ x : G.V,
      x ∈ G.ends e ↔ vertexEquiv x ∈ H.ends (edgeEquiv e)

/-- One elementary labelled minor operation with data tying source and target. -/
inductive MinorStep (G H : LGraph.{u}) : Type u
  | deleteEdge (data : EdgeDeletionData G H) : MinorStep G H
  | contractEdge (data : EdgeContractionData G H) : MinorStep G H
  | deleteIsolatedVertex (data : IsolatedVertexDeletionData G H) : MinorStep G H
  | relabelVertices (data : VertexRelabellingData G H) : MinorStep G H

/-- A chained minor derivation from `G` down to `H`. -/
inductive MinorChain : LGraph.{u} → LGraph.{u} → Type (u + 1)
  | refl (G : LGraph.{u}) : MinorChain G G
  | step {G K H : LGraph.{u}} :
      MinorStep G K → MinorChain K H → MinorChain G H

/-- Edge and vertex models for one elementary minor step. -/
def MinorStepModels {G K : LGraph.{u}} (s : MinorStep G K)
    (edgeModel : K.E → G.E) (vertexModel : K.V → Finset G.V) : Prop :=
  match s with
  | MinorStep.deleteEdge data =>
      (∀ e : K.E, edgeModel e = (data.edgeEquiv e).1) ∧
      ∀ x : K.V, vertexModel x = {data.vertexEquiv x}
  | MinorStep.contractEdge data =>
      (∀ e : K.E, edgeModel e = (data.edgeEquiv e).1) ∧
      ∀ z : K.V, vertexModel z =
        Finset.univ.filter (fun x : G.V => data.quotient x = z)
  | MinorStep.deleteIsolatedVertex data =>
      (∀ e : K.E, edgeModel e = data.edgeEquiv e) ∧
      ∀ x : K.V, vertexModel x = {(data.vertexEquiv x).1}
  | MinorStep.relabelVertices data =>
      (∀ e : K.E, edgeModel e = data.edgeEquiv.symm e) ∧
      ∀ x : K.V, vertexModel x = {data.vertexEquiv.symm x}

/-- The edge and vertex models are obtained by composing the models of a
chained minor derivation. -/
def MinorChainModels {G H : LGraph.{u}} (chain : MinorChain G H)
    (edgeModel : H.E → G.E) (vertexModel : H.V → Finset G.V) : Prop :=
  match chain with
  | MinorChain.refl _ =>
      (∀ e : G.E, edgeModel e = e) ∧
      ∀ x : G.V, vertexModel x = {x}
  | MinorChain.step (G := G) (K := K) (H := H) step rest =>
      ∃ edgeStep : K.E → G.E,
      ∃ vertexStep : K.V → Finset G.V,
      ∃ edgeRest : H.E → K.E,
      ∃ vertexRest : H.V → Finset K.V,
        MinorStepModels step edgeStep vertexStep ∧
        MinorChainModels rest edgeRest vertexRest ∧
        (∀ e : H.E, edgeModel e = edgeStep (edgeRest e)) ∧
        ∀ x : H.V, vertexModel x = (vertexRest x).biUnion vertexStep

/-- A concrete minor history from `G` down to `H`. -/
structure MinorHistory (H G : LGraph.{u}) where
  chain : MinorChain G H
  edgeModel : H.E → G.E
  vertexModel : H.V → Finset G.V
  model_realises_chain : MinorChainModels chain edgeModel vertexModel
  vertexModel_nonempty : ∀ x : H.V, (vertexModel x).Nonempty
  edgeModel_supported :
    ∀ e : H.E, ∀ x ∈ H.ends e, ∀ y ∈ vertexModel x, y ∈ G.ends (edgeModel e)

scoped notation:50 H " ≼ " G => MinorHistory H G

namespace MinorHistory

/-- Push a vertex set of a minor up to the larger graph. -/
noncomputable def vertexImage {H G : LGraph.{u}} (h : H ≼ G)
    (S : Finset H.V) : Finset G.V :=
  S.biUnion h.vertexModel

/-- Pull a vertex set of the larger graph back to the minor. -/
noncomputable def vertexPreimage {H G : LGraph.{u}} (h : H ≼ G)
    (S : Finset G.V) : Finset H.V :=
  Finset.univ.filter (fun x => ∃ y ∈ h.vertexModel x, y ∈ S)

end MinorHistory

/-- The source-side rotator represented by all vertices in the model of one
minor vertex.  This handles contractions by concatenating the rotators of all
source vertices collapsed to the target vertex. -/
noncomputable def modelRotator {H G : LGraph.{u}} (h : H ≼ G)
    (embG : PlanarEmbedding G) (x : H.V) : List G.E :=
  (h.vertexModel x).toList.flatMap (fun y => embG.rotation.rotator y)

/-- Edge labels of the larger graph that survive as labels of the minor. -/
noncomputable def survivingModelEdges {H G : LGraph.{u}} (h : H ≼ G) : Finset G.E :=
  Finset.univ.image h.edgeModel

/-- The target embedding is induced from the source embedding along a minor history. -/
def InducedRotation {H G : LGraph.{u}} (h : H ≼ G)
    (embG : PlanarEmbedding G) (embH : PlanarEmbedding H) : Prop :=
  ∀ x : H.V,
    List.map h.edgeModel (embH.rotation.rotator x) =
      (modelRotator h embG x).filter (fun e => e ∈ survivingModelEdges h)

/-- Embedded minor data. -/
structure EmbeddedMinor (H G : LGraph.{u})
    (embG : PlanarEmbedding G) (embH : PlanarEmbedding H) where
  history : H ≼ G
  induced_rotation : InducedRotation history embG embH

/-! ## Tutte data and 3-blocks -/

/-- A two-separator with two nonempty sides and no cross edge. -/
structure TwoSeparator (G : LGraph.{u}) where
  x : G.V
  y : G.V
  distinct : x ≠ y
  sideA : Finset G.V
  sideB : Finset G.V
  sideA_nonempty : sideA.Nonempty
  sideB_nonempty : sideB.Nonempty
  disjoint : Disjoint sideA sideB
  avoids_x : x ∉ sideA ∧ x ∉ sideB
  avoids_y : y ∉ sideA ∧ y ∉ sideB
  no_cross_edge :
    ∀ a ∈ sideA, ∀ b ∈ sideB, ¬ G.Adj a b

/-- Edges of a block are supported on its vertex set. -/
def EdgeSupportedOn {G : LGraph.{u}}
    (verts : Finset G.V) (edges : Finset G.E) : Prop :=
  ∀ e ∈ edges, ∀ x ∈ G.ends e, x ∈ verts

/-- Virtual torso edges are unordered endpoint pairs added across 2-separators. -/
abbrev VirtualEdges (G : LGraph.{u}) := Finset (G.V × G.V)

/-- Virtual torso edges are supported on the block's vertex set. -/
def VirtualEdgesSupportedOn {G : LGraph.{u}}
    (verts : Finset G.V) (virtualEdges : VirtualEdges G) : Prop :=
  ∀ p ∈ virtualEdges, p.1 ∈ verts ∧ p.2 ∈ verts ∧ p.1 ≠ p.2

/-- A virtual edge is justified by a two-separator with the same endpoints. -/
def VirtualEdgesFromTwoSeparators {G : LGraph.{u}}
    (virtualEdges : VirtualEdges G) : Prop :=
  ∀ p ∈ virtualEdges, ∃ s : TwoSeparator G,
    (p.1 = s.x ∧ p.2 = s.y) ∨ (p.1 = s.y ∧ p.2 = s.x)

/-- Adjacency in a Tutte torso: real block edges plus virtual separator edges. -/
def TorsoAdj {G : LGraph.{u}}
    (realEdges : Finset G.E) (virtualEdges : VirtualEdges G)
    (x y : G.V) : Prop :=
  (∃ e ∈ realEdges, x ∈ G.ends e ∧ y ∈ G.ends e ∧ x ≠ y) ∨
  (x, y) ∈ virtualEdges ∨ (y, x) ∈ virtualEdges

/-- The torso carried by `verts`, real edges, and virtual edges is connected. -/
def TorsoConnected {G : LGraph.{u}}
    (verts : Finset G.V) (realEdges : Finset G.E)
    (virtualEdges : VirtualEdges G) : Prop :=
  ∀ x ∈ verts, ∀ y ∈ verts,
    Relation.ReflTransGen
      (fun a b => a ∈ verts ∧ b ∈ verts ∧ TorsoAdj realEdges virtualEdges a b)
      x y

/-- Deleting fewer than `k` vertices does not disconnect the torso. -/
def TorsoConnectedAfterDeletingLessThan {G : LGraph.{u}}
    (k : ℕ) (verts : Finset G.V) (realEdges : Finset G.E)
    (virtualEdges : VirtualEdges G) : Prop :=
  ∀ s : Finset G.V, s ⊆ verts → s.card < k →
    ∀ x ∈ verts, x ∉ s →
    ∀ y ∈ verts, y ∉ s →
      Relation.ReflTransGen
        (fun a b =>
          a ∈ verts \ s ∧ b ∈ verts \ s ∧
          TorsoAdj realEdges virtualEdges a b)
        x y

/-- The torso carried by `verts, edges` is 3-connected. -/
def ThreeConnectedTorso {G : LGraph.{u}}
    (verts : Finset G.V) (edges : Finset G.E)
    (virtualEdges : VirtualEdges G) : Prop :=
  4 ≤ verts.card ∧
  EdgeSupportedOn verts edges ∧
  VirtualEdgesSupportedOn verts virtualEdges ∧
  VirtualEdgesFromTwoSeparators virtualEdges ∧
  TorsoConnected verts edges virtualEdges ∧
  TorsoConnectedAfterDeletingLessThan 3 verts edges virtualEdges

/-- Maximality among 3-connected torsos in the same graph. -/
def MaximalThreeConnectedTorso {G : LGraph.{u}}
    (verts : Finset G.V) (edges : Finset G.E)
    (virtualEdges : VirtualEdges G) : Prop :=
  ThreeConnectedTorso verts edges virtualEdges ∧
  ∀ verts' edges' virtualEdges',
    verts ⊆ verts' →
    edges ⊆ edges' →
    virtualEdges ⊆ virtualEdges' →
    ThreeConnectedTorso (G := G) verts' edges' virtualEdges' →
      verts' = verts ∧ edges' = edges ∧ virtualEdges' = virtualEdges

/-- A 3-block/torsor datum from the Tutte decomposition. -/
structure ThreeBlock (G : LGraph.{u}) where
  verts : Finset G.V
  edges : Finset G.E
  virtualEdges : VirtualEdges G
  verts_nonempty : verts.Nonempty
  edges_nonempty : edges.Nonempty
  edges_supported : EdgeSupportedOn verts edges
  virtual_edges_supported : VirtualEdgesSupportedOn verts virtualEdges
  virtual_edges_from_separators : VirtualEdgesFromTwoSeparators virtualEdges
  torso_three_connected : ThreeConnectedTorso verts edges virtualEdges
  maximal_three_connected_torso : MaximalThreeConnectedTorso verts edges virtualEdges

/-- Tutte-equivalent blocks are blocks belonging to the same bag. -/
structure TutteEquivalent {G : LGraph.{u}} (B C : ThreeBlock G) : Prop where
  same_bag : B.verts = C.verts
  compatible_torso_edges : B.edges = C.edges
  compatible_virtual_edges : B.virtualEdges = C.virtualEdges

/-- Tree-like decomposition data whose bags are 3-block torsos. -/
structure TutteDecomposition (G : LGraph.{u}) where
  Node : Type w
  instNode : Fintype Node
  decNode : DecidableEq Node
  treeAdj : Node → Node → Prop
  tree_symm : ∀ a b, treeAdj a b → treeAdj b a
  tree_loopless : ∀ a, ¬ treeAdj a a
  tree_connected : ∀ a b, Relation.ReflTransGen treeAdj a b
  block : Node → ThreeBlock G
  covers_vertices : ∀ x : G.V, ∃ t : Node, x ∈ (block t).verts
  covers_edges : ∀ e : G.E, ∃ t : Node, e ∈ (block t).edges
  running_intersection :
    ∀ x : G.V, ∀ a b : Node,
      x ∈ (block a).verts → x ∈ (block b).verts →
        Relation.ReflTransGen
          (fun p q => treeAdj p q ∧ x ∈ (block p).verts ∧ x ∈ (block q).verts)
          a b
  virtual_edges_match_separators :
    ∀ t : Node, VirtualEdgesFromTwoSeparators (block t).virtualEdges

attribute [instance] TutteDecomposition.instNode TutteDecomposition.decNode

/-- A node is a leaf of the decomposition tree. -/
def IsLeafNode {G : LGraph.{u}} (D : TutteDecomposition.{u, w} G)
    (t : D.Node) : Prop :=
  ∃ n : D.Node, D.treeAdj t n ∧ ∀ m : D.Node, D.treeAdj t m → m = n

/-- A Tutte leaf is a leaf bag with a nonempty edge set. -/
structure TutteLeaf (G : LGraph.{u}) where
  D : TutteDecomposition.{u, w} G
  node : D.Node
  is_leaf : IsLeafNode D node
  leaf_edges_nonempty : (D.block node).edges.Nonempty

namespace TutteLeaf

def block {G : LGraph.{u}} (A : TutteLeaf.{u, w} G) : ThreeBlock G :=
  A.D.block A.node

end TutteLeaf

/-! ## Temporal sequences -/

/-- The minor directions alternate in consecutive links. -/
def AlternatingMinorDirections {n : ℕ}
    (graph : Fin n → LGraph.{u})
    (adjacent :
      ∀ i : Fin (n - 1),
        (graph ⟨i.val, by omega⟩ ≼ graph ⟨i.val + 1, by omega⟩) ⊕
        (graph ⟨i.val + 1, by omega⟩ ≼ graph ⟨i.val, by omega⟩)) : Prop :=
  ∀ i : Fin (n - 2),
    (∃ h₁ h₂,
      adjacent ⟨i.val, by omega⟩ = Sum.inl h₁ ∧
      adjacent ⟨i.val + 1, by omega⟩ = Sum.inr h₂) ∨
    (∃ h₁ h₂,
      adjacent ⟨i.val, by omega⟩ = Sum.inr h₁ ∧
      adjacent ⟨i.val + 1, by omega⟩ = Sum.inl h₂)

/-- A temporal sequence records explicit minor histories between neighbours. -/
structure TemporalSeq (n : ℕ) where
  graph : Fin n → LGraph.{u}
  adjacent :
    ∀ i : Fin (n - 1),
      (graph ⟨i.val, by omega⟩ ≼ graph ⟨i.val + 1, by omega⟩) ⊕
      (graph ⟨i.val + 1, by omega⟩ ≼ graph ⟨i.val, by omega⟩)
  alternating_minor_directions : AlternatingMinorDirections graph adjacent

namespace TemporalSeq

def Nonempty {n : ℕ} (_T : TemporalSeq.{u} n) : Prop := 0 < n

def TwoConnected {n : ℕ} (T : TemporalSeq.{u} n) : Prop :=
  ∀ i : Fin n, (T.graph i).TwoConnected

noncomputable def size {n : ℕ} (T : TemporalSeq.{u} n) : ℕ :=
  ∑ i : Fin n, Fintype.card (T.graph i).E

/-- Edges of graph `i` are new relative to `i - 1` when no edge of the previous
graph maps to one of them. If the minor direction is from `i` down to `i - 1`,
the condition says that the listed current edges are not among the contracted
survivors represented in the previous graph. -/
def EdgesNewRelativeToPrevious {n : ℕ} (T : TemporalSeq.{u} n)
    (i : Fin n) (hi : 0 < i.val) (edges : Finset (T.graph i).E) : Prop :=
  match T.adjacent ⟨i.val - 1, by omega⟩ with
  | Sum.inl h =>
      ∀ e ∈ edges, ∀ eprev : (T.graph ⟨i.val - 1, by omega⟩).E,
        ¬ HEq (h.edgeModel eprev) e
  | Sum.inr h =>
      ∀ e ∈ edges,
        ∀ ecur : (T.graph ⟨(i.val - 1) + 1, by omega⟩).E,
          HEq ecur e →
            ∃ eprev : (T.graph ⟨i.val - 1, by omega⟩).E,
              h.edgeModel ecur = eprev

/-- An upleaf is a Tutte leaf at an even-indexed graph whose edge set is new
relative to the previous graph, except at the root. -/
structure Upleaf {n : ℕ} (T : TemporalSeq.{u} n) where
  index : Fin n
  even_index : index.val % 2 = 0
  leaf : TutteLeaf.{u, w} (T.graph index)
  root_or_new_edges :
    index.val = 0 ∨
      ∀ hprev : 0 < index.val,
        EdgesNewRelativeToPrevious T index hprev leaf.block.edges

end TemporalSeq

/-! ## Lists and simultaneous list-embeddings -/

/-- A block embedding is an embedding of the ambient graph supported on a block. -/
structure BlockEmbedding {G : LGraph.{u}} (B : ThreeBlock G) where
  emb : PlanarEmbedding G
  supported_on_block :
    ∀ x : G.V, x ∉ B.verts → emb.rotation.rotator x = []

/-- Two block embeddings of the same graph are equal up to global reorientation. -/
def SameUpToReorientation {G : LGraph.{u}} {B C : ThreeBlock G}
    (α : BlockEmbedding B) (β : BlockEmbedding C) : Prop :=
  α.emb.rotation.rotator = β.emb.rotation.rotator ∨
  α.emb.rotation.rotator = β.emb.rotation.reorient.rotator

/-- Transport witnessing that two prescribed block embeddings agree across
possibly different labelled graphs. -/
structure BlockEmbeddingTransport
    {G H : LGraph.{u}} {B : ThreeBlock G} {C : ThreeBlock H}
    (α : BlockEmbedding B) (β : BlockEmbedding C) where
  vertexEquiv : G.V ≃ H.V
  edgeEquiv : G.E ≃ H.E
  maps_block_vertices :
    ∀ x : G.V, x ∈ B.verts ↔ vertexEquiv x ∈ C.verts
  maps_block_edges :
    ∀ e : G.E, e ∈ B.edges ↔ edgeEquiv e ∈ C.edges
  preserves_rotation :
    ∀ x : G.V,
      List.map edgeEquiv (α.emb.rotation.rotator x) =
        β.emb.rotation.rotator (vertexEquiv x)

/-- Transport witnessing agreement with the target embedding after global reorientation. -/
structure BlockEmbeddingReorientationTransport
    {G H : LGraph.{u}} {B : ThreeBlock G} {C : ThreeBlock H}
    (α : BlockEmbedding B) (β : BlockEmbedding C) where
  vertexEquiv : G.V ≃ H.V
  edgeEquiv : G.E ≃ H.E
  maps_block_vertices :
    ∀ x : G.V, x ∈ B.verts ↔ vertexEquiv x ∈ C.verts
  maps_block_edges :
    ∀ e : G.E, e ∈ B.edges ↔ edgeEquiv e ∈ C.edges
  preserves_reoriented_rotation :
    ∀ x : G.V,
      List.map edgeEquiv (α.emb.rotation.rotator x) =
        β.emb.rotation.reorient.rotator (vertexEquiv x)

/-- Compatibility of prescribed block embeddings, allowing global reorientation. -/
def BlockEmbeddingsCompatible
    {G H : LGraph.{u}} {B : ThreeBlock G} {C : ThreeBlock H}
    (α : BlockEmbedding B) (β : BlockEmbedding C) : Prop :=
  Nonempty (BlockEmbeddingTransport α β) ∨
  Nonempty (BlockEmbeddingReorientationTransport α β)

/-- A list is a partition of selected 3-blocks with an embedding chosen for each block. -/
structure TempList {n : ℕ} (T : TemporalSeq.{u} n) where
  selected : (Σ i : Fin n, ThreeBlock (T.graph i)) → Prop
  same_part :
    (Σ i : Fin n, ThreeBlock (T.graph i)) →
    (Σ i : Fin n, ThreeBlock (T.graph i)) → Prop
  same_part_selected_left : ∀ A B, same_part A B → selected A
  same_part_selected_right : ∀ A B, same_part A B → selected B
  same_part_refl : ∀ B, same_part B B
  same_part_symm : ∀ B C, same_part B C → same_part C B
  same_part_trans : ∀ A B C, same_part A B → same_part B C → same_part A C
  embedding :
    ∀ B : Σ i : Fin n, ThreeBlock (T.graph i), BlockEmbedding B.2
  closed_under_tutte :
    ∀ (i : Fin n) (B C : ThreeBlock (T.graph i)),
      selected ⟨i, B⟩ → TutteEquivalent B C →
        same_part ⟨i, B⟩ ⟨i, C⟩
  tutte_equiv_embeddings :
    ∀ (i : Fin n) (B C : ThreeBlock (T.graph i)) (_s : selected ⟨i, B⟩)
      (_h : TutteEquivalent B C),
      SameUpToReorientation (embedding ⟨i, B⟩) (embedding ⟨i, C⟩)

/-- A whole-graph embedding induces the prescribed embedding on a block. -/
def EmbeddingMatchesBlock {G : LGraph.{u}} {B : ThreeBlock G}
    (emb : PlanarEmbedding G) (α : BlockEmbedding B) : Prop :=
  emb.rotation.rotator = α.emb.rotation.rotator ∨
  emb.rotation.rotator = α.emb.rotation.reorient.rotator

/-- A sequence of embeddings respects a list. -/
def EmbeddingRespectsList {n : ℕ} {T : TemporalSeq.{u} n}
    (emb : ∀ i : Fin n, PlanarEmbedding (T.graph i))
    (L : TempList T) : Prop :=
  (∀ A : Σ i : Fin n, ThreeBlock (T.graph i),
      L.selected A → EmbeddingMatchesBlock (emb A.1) (L.embedding A)) ∧
  ∀ A B : Σ i : Fin n, ThreeBlock (T.graph i),
    L.same_part A B →
      BlockEmbeddingsCompatible (L.embedding A) (L.embedding B)

/-- Adjacent embeddings are compatible when the smaller graph's embedding is induced. -/
def AdjacentEmbeddingsCompatible {n : ℕ} (T : TemporalSeq.{u} n)
    (emb : ∀ i : Fin n, PlanarEmbedding (T.graph i))
    (i : Fin (n - 1)) : Prop :=
  match T.adjacent i with
  | Sum.inl _ =>
      Nonempty (EmbeddedMinor
        (T.graph ⟨i.val, by omega⟩)
        (T.graph ⟨i.val + 1, by omega⟩)
        (emb ⟨i.val + 1, by omega⟩)
        (emb ⟨i.val, by omega⟩))
  | Sum.inr _ =>
      Nonempty (EmbeddedMinor
        (T.graph ⟨i.val + 1, by omega⟩)
        (T.graph ⟨i.val, by omega⟩)
        (emb ⟨i.val, by omega⟩)
        (emb ⟨i.val + 1, by omega⟩))

/-- Simultaneous list-embedding for two lists. -/
def SimultListEmb {n : ℕ} (T : TemporalSeq.{u} n)
    (L M : TempList T) : Prop :=
  ∃ emb : ∀ i : Fin n, PlanarEmbedding (T.graph i),
    (∀ i : Fin (n - 1), AdjacentEmbeddingsCompatible T emb i) ∧
    EmbeddingRespectsList emb L ∧
    EmbeddingRespectsList emb M

/-! ## Improvements -/

structure FlexParams (G : LGraph.{u}) where
  alpha : ℕ
  beta : ℕ
  gamma : ℕ

def flexSingleInt {G : LGraph.{u}} (p : FlexParams G) : ℤ :=
  1 + 2 * ((p.alpha : ℤ) + 3 * (p.beta : ℤ)) - (p.gamma : ℤ)

noncomputable def flexSeqInt {n : ℕ} (T : TemporalSeq.{u} n)
    (params : ∀ i : Fin n, FlexParams (T.graph i)) : ℤ :=
  ∑ i : Fin n,
    if i.val % 2 = 0 then ((n - i.val : ℕ) : ℤ) * flexSingleInt (params i) else 0

def AreAnalogues {n : ℕ} (T T' : TemporalSeq.{u} n)
    (L M : TempList T) (L' M' : TempList T') : Prop :=
  SimultListEmb T L M ↔ SimultListEmb T' L' M'

/-- Niceness records separation/attachment conditions. -/
structure NiceGraph (G : LGraph.{u}) : Prop where
  tuplets_far_apart :
    ∀ s t : TwoSeparator G, s.x ≠ t.x ∨ s.y ≠ t.y
  single_edge_attachment :
    ∀ s : TwoSeparator G, ∃ e : G.E, s.x ∈ G.ends e ∨ s.y ∈ G.ends e

structure IsImprovement {n : ℕ}
    (T : TemporalSeq.{u} n) (L M : TempList T)
    (T' : TemporalSeq.{u} n) (L' M' : TempList T')
    (params : ∀ i : Fin n, FlexParams (T.graph i))
    (params' : ∀ i : Fin n, FlexParams (T'.graph i)) : Prop where
  analogue : AreAnalogues T T' L M L' M'
  nice : ∀ i : Fin n, NiceGraph (T'.graph i)
  size_global : T'.size ≤ 100 * T.size ^ 2
  flex_if_nice :
    (∀ i : Fin n, NiceGraph (T.graph i)) →
      flexSeqInt T' params' ≤ flexSeqInt T params - 1
  size_if_nice :
    (∀ i : Fin n, NiceGraph (T.graph i)) →
      T'.size ≤ T.size + 13 * (Int.natAbs (flexSeqInt T params)) ^ 2

/-! ## The five obstruction classes -/

abbrev TempTriple := TemporalSeq.{u} 3

/-- A list of edges is realised by a labelled walk. -/
def EdgeListSupportsWalk {G : LGraph.{u}}
    (source sink : G.V) (path : List G.E) : Prop :=
  ∃ w : G.Walk source sink, w.edgeSupport = path

def EdgeListsDisjoint {E : Type u} (p q : List E) : Prop :=
  ∀ e, e ∈ p → e ∉ q

/-- Internal vertices of a labelled walk, with the endpoints removed. -/
def Walk.internalSupport {G : LGraph.{u}} {a b : G.V}
    (w : G.Walk a b) : List G.V :=
  (w.support.erase a).erase b

/-- A listed path has the stated internal vertex trace. -/
def EdgeListSupportsWalkWithInternal {G : LGraph.{u}}
    (source sink : G.V) (path : List G.E) (internal : List G.V) : Prop :=
  ∃ w : G.Walk source sink, w.edgeSupport = path ∧ Walk.internalSupport w = internal

def VertexListsDisjoint {V : Type u} (p q : List V) : Prop :=
  ∀ x, x ∈ p → x ∉ q

/-- A theta witness records three internally edge-disjoint labelled paths. -/
structure ThetaWitness (G : LGraph.{u}) where
  source : G.V
  sink : G.V
  source_ne_sink : source ≠ sink
  path1 : List G.E
  path2 : List G.E
  path3 : List G.E
  internal1 : List G.V
  internal2 : List G.V
  internal3 : List G.V
  path1_nonempty : path1 ≠ []
  path2_nonempty : path2 ≠ []
  path3_nonempty : path3 ≠ []
  path1_valid : EdgeListSupportsWalkWithInternal source sink path1 internal1
  path2_valid : EdgeListSupportsWalkWithInternal source sink path2 internal2
  path3_valid : EdgeListSupportsWalkWithInternal source sink path3 internal3
  path12_disjoint : EdgeListsDisjoint path1 path2
  path13_disjoint : EdgeListsDisjoint path1 path3
  path23_disjoint : EdgeListsDisjoint path2 path3
  internal12_disjoint : VertexListsDisjoint internal1 internal2
  internal13_disjoint : VertexListsDisjoint internal1 internal3
  internal23_disjoint : VertexListsDisjoint internal2 internal3

def FirstEdge {G : LGraph.{u}} (p : List G.E) (e : G.E) : Prop :=
  p.head? = some e

def LastEdge {G : LGraph.{u}} (p : List G.E) (e : G.E) : Prop :=
  p.getLast? = some e

/-- A theta orientation appears in the rotation system at both branch vertices. -/
def ThetaOrientationCompatible {G : LGraph.{u}}
    (θ : ThetaWitness G) (emb : PlanarEmbedding G) : Prop :=
  ∃ a b c a' b' c' : G.E,
    FirstEdge θ.path1 a ∧ FirstEdge θ.path2 b ∧ FirstEdge θ.path3 c ∧
    LastEdge θ.path1 a' ∧ LastEdge θ.path2 b' ∧ LastEdge θ.path3 c' ∧
    (List.Sublist [a, b, c] (emb.rotation.rotator θ.source) ∨
      List.Sublist [c, b, a] (emb.rotation.rotator θ.source)) ∧
    (List.Sublist [a', b', c'] (emb.rotation.rotator θ.sink) ∨
      List.Sublist [c', b', a'] (emb.rotation.rotator θ.sink))

/-- Two theta witnesses have no common induced orientation. -/
def NoCommonInducedThetaOrientation {G : LGraph.{u}}
    (θ₁ θ₂ : ThetaWitness G) : Prop :=
  ¬ ∃ emb : PlanarEmbedding G,
    ThetaOrientationCompatible θ₁ emb ∧ ThetaOrientationCompatible θ₂ emb

/-- Disagreeable triples contain incompatible theta minors. -/
structure IncompatibleThetaMinors (T : TempTriple) where
  H1 : LGraph.{u}
  H3 : LGraph.{u}
  left_minor : H1 ≼ T.graph 0
  right_minor : H3 ≼ T.graph 2
  theta1 : ThetaWitness (T.graph 1)
  theta2 : ThetaWitness (T.graph 1)
  no_common_induced_orientation :
    NoCommonInducedThetaOrientation theta1 theta2

def IsDisagreeable (T : TempTriple) : Prop :=
  Nonempty (IncompatibleThetaMinors T)

/-- A walk avoids the separator vertices. -/
def WalkAvoidsTwoSeparator {G : LGraph.{u}} {a b : G.V}
    (w : G.Walk a b) (sep : TwoSeparator G) : Prop :=
  sep.x ∉ w.support ∧ sep.y ∉ w.support

/-- A component after deleting a two-separator. -/
def IsComponentAfterDeletingSep {G : LGraph.{u}}
    (sep : TwoSeparator G) (component : Finset G.V) : Prop :=
  component.Nonempty ∧
  sep.x ∉ component ∧ sep.y ∉ component ∧
  (∀ x ∈ component, ∀ y ∈ component,
    ∃ w : G.Walk x y, WalkAvoidsTwoSeparator w sep) ∧
  ∀ z : G.V, z ≠ sep.x → z ≠ sep.y →
    (∃ x ∈ component, ∃ w : G.Walk x z, WalkAvoidsTwoSeparator w sep) →
      z ∈ component

structure TwoComponentAt (G : LGraph.{u}) where
  sep : TwoSeparator G
  component : Finset G.V
  is_component : IsComponentAfterDeletingSep sep component

namespace TwoComponentAt

theorem component_nonempty {G : LGraph.{u}} (C : TwoComponentAt G) :
    C.component.Nonempty :=
  C.is_component.1

theorem avoids_separator {G : LGraph.{u}} (C : TwoComponentAt G) :
    C.sep.x ∉ C.component ∧ C.sep.y ∉ C.component :=
  ⟨C.is_component.2.1, C.is_component.2.2.1⟩

end TwoComponentAt

/-- Shadow of a block from graph `0` in the middle graph of a triple. -/
noncomputable def leftBlockShadow (T : TempTriple)
    (A : TutteLeaf.{u, w} (T.graph 0)) : Finset (T.graph 1).V :=
  match T.adjacent ⟨0, by omega⟩ with
  | Sum.inl h => h.vertexImage A.block.verts
  | Sum.inr h => h.vertexPreimage A.block.verts

/-- Shadow of a separator component from graph `2` in the middle graph. -/
noncomputable def rightComponentShadow (T : TempTriple)
    (C : TwoComponentAt (T.graph 2)) : Finset (T.graph 1).V :=
  match T.adjacent ⟨1, by omega⟩ with
  | Sum.inl h => h.vertexPreimage C.component
  | Sum.inr h => h.vertexImage C.component

def AffectiveShadowPresent (T : TempTriple)
    (A : TutteLeaf.{u, w} (T.graph 0)) (C : TwoComponentAt (T.graph 2)) : Prop :=
  (leftBlockShadow T A).Nonempty ∧ (rightComponentShadow T C).Nonempty

def AffectivelyConnected (T : TempTriple)
    (A : TutteLeaf.{u, w} (T.graph 0)) (C : TwoComponentAt (T.graph 2)) : Prop :=
  ∃ x ∈ leftBlockShadow T A, ∃ y ∈ rightComponentShadow T C,
    x = y ∨ (T.graph 1).Adj x y

structure NotAffectivelyConnected (T : TempTriple)
    (A : TutteLeaf.{u, w} (T.graph 0)) (C : TwoComponentAt (T.graph 2)) where
  shadow_present : AffectiveShadowPresent T A C
  affective_failure : ¬ AffectivelyConnected T A C

def IsAmazinglyBad (T : TempTriple) : Prop :=
  ∃ A : TutteLeaf.{u, w} (T.graph 0), ∃ C : TwoComponentAt (T.graph 2),
    Nonempty (NotAffectivelyConnected T A C)

def EdgeIncidentWith {G : LGraph.{u}} (e : G.E) (x : G.V) : Prop :=
  x ∈ G.ends e

def EdgeCrosses {G : LGraph.{u}}
    (left right : Finset G.V) (e : G.E) : Prop :=
  ∃ x ∈ left, ∃ y ∈ right, x ∈ G.ends e ∧ y ∈ G.ends e

def ColourClassCentredAt {G : LGraph.{u}}
    (centre : G.V) (colour : Finset G.E) : Prop :=
  ∀ e ∈ colour, EdgeIncidentWith e centre

def ViolatesBondRespect {G : LGraph.{u}}
    (sep : TwoSeparator G) (red blue : Finset G.E) : Prop :=
  (∃ e ∈ red, EdgeCrosses sep.sideA sep.sideB e) ∧
  (∃ e ∈ blue, EdgeCrosses sep.sideA sep.sideB e)

structure GaudyColouring (G : LGraph.{u}) where
  sep : TwoSeparator G
  centre : G.V
  centre_on_separator : centre = sep.x ∨ centre = sep.y
  red : Finset G.E
  blue : Finset G.E
  red_nonempty : red.Nonempty
  blue_nonempty : blue.Nonempty
  disjoint : Disjoint red blue
  red_centred : ColourClassCentredAt centre red
  blue_centred : ColourClassCentredAt centre blue
  violates_bond_respect : ViolatesBondRespect sep red blue

def IsGaudy (T : TempTriple) : Prop :=
  Nonempty (GaudyColouring (T.graph 2))

def PrescribedEmbeddingsIncompatible
    {T : TempTriple} (L : TempList T)
    (B₁ : ThreeBlock (T.graph 0))
    (B₃ : ThreeBlock (T.graph 2)) : Prop :=
  ¬ BlockEmbeddingsCompatible (L.embedding ⟨0, B₁⟩) (L.embedding ⟨2, B₃⟩)

structure LocalListClash (T : TempTriple) (L : TempList T) where
  B₁ : ThreeBlock (T.graph 0)
  B₃ : ThreeBlock (T.graph 2)
  same_part : L.same_part ⟨0, B₁⟩ ⟨2, B₃⟩
  incompatible_prescribed_embeddings :
    PrescribedEmbeddingsIncompatible L B₁ B₃

def IsInconsistent (T : TempTriple) (L : TempList T) : Prop :=
  Nonempty (LocalListClash T L)

def ListsEquivalent {n : ℕ} {T : TemporalSeq.{u} n}
    (L M : TempList T) : Prop :=
  (∀ A B, L.same_part A B ↔ M.same_part A B) ∧
  ∀ A, SameUpToReorientation (L.embedding A) (M.embedding A)

def ListsSpecifySameEmbeddings {n : ℕ} {T : TemporalSeq.{u} n}
    (L M : TempList T) : Prop :=
  ∀ A, SameUpToReorientation (L.embedding A) (M.embedding A)

def ListsCombinable {n : ℕ} {T : TemporalSeq.{u} n}
    (L M : TempList T) : Prop :=
  ∃ L' M' : TempList T,
    ListsEquivalent L L' ∧
    ListsEquivalent M M' ∧
    ListsSpecifySameEmbeddings L' M'

def IsUncombinable {n : ℕ} (T : TemporalSeq.{u} n)
    (L M : TempList T) : Prop :=
  ¬ ListsCombinable L M

/-- Restrict a temporal sequence to a length-three window. -/
def tripleWindow {n : ℕ} (T : TemporalSeq.{u} n)
    (i : Fin (n - 2)) : TempTriple where
  graph j := T.graph ⟨i.val + j.val, by omega⟩
  adjacent k := by
    exact T.adjacent ⟨i.val + k.val, by omega⟩
  alternating_minor_directions := by
    intro k
    rcases T.alternating_minor_directions ⟨i.val + k.val, by omega⟩ with h | h
    · rcases h with ⟨h₁, h₂, hleft, hright⟩
      exact Or.inl ⟨h₁, h₂, hleft, hright⟩
    · rcases h with ⟨h₁, h₂, hleft, hright⟩
      exact Or.inr ⟨h₁, h₂, hleft, hright⟩

/-- Restrict a list to a length-three window. -/
def restrictListToWindow {n : ℕ} {T : TemporalSeq.{u} n}
    (L : TempList T) (i : Fin (n - 2)) : TempList (tripleWindow T i) where
  selected A :=
    L.selected ⟨⟨i.val + A.1.val, by omega⟩, A.2⟩
  same_part A B :=
    L.same_part
      ⟨⟨i.val + A.1.val, by omega⟩, A.2⟩
      ⟨⟨i.val + B.1.val, by omega⟩, B.2⟩
  same_part_selected_left A B h := L.same_part_selected_left _ _ h
  same_part_selected_right A B h := L.same_part_selected_right _ _ h
  same_part_refl A := L.same_part_refl _
  same_part_symm A B h := L.same_part_symm _ _ h
  same_part_trans A B C hAB hBC := L.same_part_trans _ _ _ hAB hBC
  embedding A := L.embedding ⟨⟨i.val + A.1.val, by omega⟩, A.2⟩
  closed_under_tutte j B C s h :=
    L.closed_under_tutte ⟨i.val + j.val, by omega⟩ B C s h
  tutte_equiv_embeddings j B C s h :=
    L.tutte_equiv_embeddings ⟨i.val + j.val, by omega⟩ B C s h

/-- Definition 4.42-style obstruction predicate. -/
def IsObstructed {n : ℕ} (T : TemporalSeq.{u} n)
    (L M : TempList T) : Prop :=
  (∃ i : Fin (n - 2),
    let W := tripleWindow T i
    IsDisagreeable W ∨ IsAmazinglyBad.{u, w} W ∨ IsGaudy W ∨
      IsInconsistent W (restrictListToWindow L i) ∨
      IsInconsistent W (restrictListToWindow M i)) ∨
  IsUncombinable T L M

/-! ## Main theorem -/

/-- Theorem 3.5.  The definitions above are fully specified; the remaining
obligation is the paper's long combinatorial proof. -/
theorem P026 {n : ℕ}
    (T : TemporalSeq.{u} n) (L M : TempList T)
    (params : ∀ i : Fin n, FlexParams (T.graph i))
    (hne : T.Nonempty) (h2c : T.TwoConnected) :
    IsObstructed T L M ∨
    ∃ (T' : TemporalSeq.{u} n) (L' M' : TempList T')
      (params' : ∀ i : Fin n, FlexParams (T'.graph i)),
        IsImprovement T L M T' L' M' params params' := by
  sorry

end TemporalSequences
