import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Set.Card
import Mathlib.Tactic
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Decomposition

open SimpleGraph

universe u v w

/-- A pair `(A, B)` of vertex sets; a mixed-separation⁺ of a graph when `A ∪ B = V`. -/
@[ext]
structure MixedSep (V : Type u) where
  A : Set V
  B : Set V

namespace MixedSep

variable {V : Type u}

/-- The partial order on pairs: `(A, B) ≤ (C, D)` iff `A ⊆ C` and `B ⊇ D`. -/
def Le (s t : MixedSep V) : Prop := s.A ⊆ t.A ∧ t.B ⊆ s.B

/-- The pair `(B, A)`. -/
def flip (s : MixedSep V) : MixedSep V := ⟨s.B, s.A⟩

/-- `(A, B)` and `(C, D)` are nested if `(A, B) ≤ (C, D)` after possibly swapping the names
`A, B` or the names `C, D`. -/
def Nested (s t : MixedSep V) : Prop :=
  s.Le t ∨ s.flip.Le t ∨ s.Le t.flip ∨ s.flip.Le t.flip

/-- The edge set `E(A \ B, B \ A)` of `G`: the edges with one end in `A \ B` and the other in
`B \ A`. -/
def crossEdges (G : SimpleGraph V) (s : MixedSep V) : Set (Sym2 V) :=
  {e | ∃ x y, e = s(x, y) ∧ G.Adj x y ∧ x ∈ s.A \ s.B ∧ y ∈ s.B \ s.A}

/-- The order of `(A, B)` in `G`: the size of its separator `S(A, B)`, the disjoint union of the
vertex set `A ∩ B` and the edge set `E(A \ B, B \ A)`. -/
noncomputable def order (G : SimpleGraph V) (s : MixedSep V) : ℕ∞ :=
  (s.A ∩ s.B).encard + (crossEdges G s).encard

/-- `(A, B)` is a (proper) mixed-separation: `A ∪ B = V` and `A \ B`, `B \ A` are nonempty. -/
def IsMixedSep (s : MixedSep V) : Prop :=
  s.A ∪ s.B = Set.univ ∧ (s.A \ s.B).Nonempty ∧ (s.B \ s.A).Nonempty

/-- The degree-condition: every vertex of `A ∩ B` has at least two neighbours in `A \ B` and at
least two in `B \ A`. -/
def DegreeCondition (G : SimpleGraph V) (s : MixedSep V) : Prop :=
  ∀ x ∈ s.A ∩ s.B,
    2 ≤ (G.neighborSet x ∩ (s.A \ s.B)).encard ∧ 2 ≤ (G.neighborSet x ∩ (s.B \ s.A)).encard

/-- The matching-condition: the edges in `S(A, B)` form a matching, i.e. two of them that share
an end are equal. -/
def MatchingCondition (G : SimpleGraph V) (s : MixedSep V) : Prop :=
  ∀ e ∈ crossEdges G s, ∀ f ∈ crossEdges G s, ∀ x, x ∈ e → x ∈ f → e = f

/-- A tetra-separation of `G` (Definition 2.1): a mixed-separation of order `4` satisfying the
degree-condition and the matching-condition. -/
def IsTetraSep (G : SimpleGraph V) (s : MixedSep V) : Prop :=
  s.IsMixedSep ∧ s.order G = 4 ∧ DegreeCondition G s ∧ MatchingCondition G s

/-- A totally-nested tetra-separation of `G`: a tetra-separation nested with every
tetra-separation of `G`. -/
def IsTotallyNested (G : SimpleGraph V) (s : MixedSep V) : Prop :=
  IsTetraSep G s ∧ ∀ t : MixedSep V, IsTetraSep G t → s.Nested t

/-- The vertex set `λ(A, B)`: the vertices of `A ∩ B` together with the end in `A \ B` of each
edge of `E(A \ B, B \ A)`. -/
def lam (G : SimpleGraph V) (s : MixedSep V) : Set V :=
  (s.A ∩ s.B) ∪ {x | x ∈ s.A \ s.B ∧ ∃ y ∈ s.B \ s.A, G.Adj x y}

end MixedSep

/-- A mixed-tree-decomposition of a graph on `V` (Section 2.2): a tree on `T` with a bag
`V_t ⊆ V` at each node such that (M1) every vertex lies in a bag and (M2) the nodes whose bags
contain a given vertex induce a connected subtree. -/
structure MixedTreeDecomp (V : Type u) (T : Type v) where
  tree : SimpleGraph T
  isTree : tree.IsTree
  bag : T → Set V
  M1 : ∀ x : V, ∃ t, x ∈ bag t
  M2 : ∀ x : V, (tree.induce {t | x ∈ bag t}).Connected

namespace MixedTreeDecomp

variable {V : Type u} {T : Type v} (G : SimpleGraph V) (D : MixedTreeDecomp V T)

/-- The union of the bags of the nodes in the component of `T - t₁t₂` that contains `t₁`. -/
def side (t₁ t₂ : T) : Set V :=
  {x | ∃ t, (D.tree.deleteEdges {s(t₁, t₂)}).Reachable t₁ t ∧ x ∈ D.bag t}

/-- The mixed-separation⁺ `α(t₁, t₂) = (A₁, A₂)` induced by the oriented tree edge `(t₁, t₂)`,
where `Aᵢ` is the union of the bags in the component of `T - t₁t₂` containing `tᵢ`. -/
def sep (t₁ t₂ : T) : MixedSep V := ⟨D.side t₁ t₂, D.side t₂ t₁⟩

/-- `D` is the mixed-tree-decomposition determined by the totally-nested tetra-separations of
`G`: `(t₁, t₂) ↦ α(t₁, t₂)` is a bijection from the oriented edges of the tree onto the set of
totally-nested tetra-separations of `G`. -/
def IsDeterminedByTotallyNested : Prop :=
  (∀ t₁ t₂, D.tree.Adj t₁ t₂ → MixedSep.IsTotallyNested G (D.sep t₁ t₂)) ∧
  (∀ s, MixedSep.IsTotallyNested G s → ∃ t₁ t₂, D.tree.Adj t₁ t₂ ∧ D.sep t₁ t₂ = s) ∧
  (∀ t₁ t₂ t₃ t₄, D.tree.Adj t₁ t₂ → D.tree.Adj t₃ t₄ → D.sep t₁ t₂ = D.sep t₃ t₄ →
    t₁ = t₃ ∧ t₂ = t₄)

/-- Canonicity (Remark 1.2): every automorphism `φ` of `G` is matched by an automorphism `ψ` of
the decomposition tree with `V_{ψ(t)} = φ(V_t)` for every node `t`. -/
def IsAutInvariant : Prop :=
  ∀ φ : G ≃g G, ∃ ψ : D.tree ≃g D.tree, ∀ t, D.bag (ψ t) = φ '' D.bag t

/-- The vertex set `V_t ∪ ⋃ λ(α(s, t))` of the expanded-torso at `t`, the union over the
neighbours `s` of `t`. -/
def expandedTorsoVerts (t : T) : Set V :=
  D.bag t ∪ {x | ∃ s, D.tree.Adj s t ∧ x ∈ MixedSep.lam G (D.sep s t)}

/-- The expanded-torso at `t`: the subgraph of `G` induced by `expandedTorsoVerts`, with each
`λ(α(s, t))` made into a clique. -/
def expandedTorso (t : T) : SimpleGraph (D.expandedTorsoVerts G t) where
  Adj x y := x ≠ y ∧ (G.Adj x y ∨
    ∃ s, D.tree.Adj s t ∧ x.1 ∈ MixedSep.lam G (D.sep s t) ∧ y.1 ∈ MixedSep.lam G (D.sep s t))
  symm := ⟨by
    rintro x y ⟨hxy, h | ⟨s, hs, hx, hy⟩⟩
    · exact ⟨hxy.symm, Or.inl h.symm⟩
    · exact ⟨hxy.symm, Or.inr ⟨s, hs, hy, hx⟩⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- The edges of the expanded-torso at `t` that lie in an adhesion-set, i.e. in
`E(A \ B, B \ A)` for some `(A, B) = α(s, t)` with `s` a neighbour of `t`. -/
def adhesionEdges (t : T) : SimpleGraph (D.expandedTorsoVerts G t) where
  Adj x y := ∃ s, D.tree.Adj s t ∧ s(x.1, y.1) ∈ MixedSep.crossEdges G (D.sep s t)
  symm := ⟨by
    rintro x y ⟨s, hs, he⟩
    exact ⟨s, hs, by rwa [Sym2.eq_swap]⟩⟩
  loopless := ⟨by
    rintro x ⟨s, -, a, b, hab, hadj, -, -⟩
    rcases Sym2.eq_iff.mp hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hadj.ne (h1.symm.trans h2)
    · exact hadj.ne (h2.symm.trans h1)⟩

/-- The (compressed) torso at `t`: the expanded-torso with all edges of `adhesionEdges`
contracted. Its vertices are the classes of vertices joined by contracted edges; two distinct
classes are adjacent if the expanded-torso has an edge between them. -/
def torso (t : T) : SimpleGraph (D.adhesionEdges G t).ConnectedComponent where
  Adj c d := c ≠ d ∧ ∃ x y, (D.expandedTorso G t).Adj x y ∧
    (D.adhesionEdges G t).connectedComponentMk x = c ∧
    (D.adhesionEdges G t).connectedComponentMk y = d
  symm := ⟨by
    rintro c d ⟨hcd, x, y, hxy, hx, hy⟩
    exact ⟨hcd.symm, y, x, hxy.symm, hy, hx⟩⟩
  loopless := ⟨fun c h => h.1 rfl⟩

end MixedTreeDecomp

section TorsoTypes

variable {W : Type u} {N : Type v}

/-- `X` is quasi-`5`-connected: `4`-connected, and every `4`-separation `(A, B)` (a separation
with `A \ B`, `B \ A` nonempty and `|A ∩ B| = 4`) has `|A \ B| = 1` or `|B \ A| = 1`. -/
def IsQuasi5Connected (X : SimpleGraph W) : Prop :=
  X.IsVertexConnected 4 ∧
    ∀ A B : Set W, X.IsSeparation A B → (A \ B).Nonempty → (B \ A).Nonempty →
      (A ∩ B).encard = 4 → (A \ B).encard = 1 ∨ (B \ A).encard = 1

/-- The torso of the part `G_h` of a graph-decomposition `D` of `X` modelled on `H`: the part
`G_h` with every adhesion-set `V(G_h) ∩ V(G_{h'})`, `hh' ∈ E(H)`, made complete. -/
def partTorso {X : SimpleGraph W} {H : SimpleGraph N} (D : Decomposition X H) (h : N) :
    SimpleGraph (D.bags h).verts where
  Adj x y := (D.bags h).Adj x.1 y.1 ∨
    (x ≠ y ∧ ∃ h', H.Adj h h' ∧ x.1 ∈ (D.bags h').verts ∧ y.1 ∈ (D.bags h').verts)
  symm := ⟨by
    rintro x y (hxy | ⟨hne, h', hh', hx, hy⟩)
    · exact Or.inl hxy.symm
    · exact Or.inr ⟨hne.symm, h', hh', hy, hx⟩⟩
  loopless := ⟨by
    rintro x (hxx | ⟨hne, -⟩)
    · exact hxx.ne rfl
    · exact hne rfl⟩

/-- `X` is a cycle of triangle-torsos and `3`-connected torsos on at most `5` vertices: `X` is
`4`-connected and has a cycle-decomposition (modelled on the cycle `C_n`, `n ≥ 3`) with all
adhesion-sets of size two, each of whose torsos is a triangle or a `3`-connected graph on at most
`5` vertices. -/
def IsCycleOfSmallTorsos (X : SimpleGraph W) : Prop :=
  X.IsVertexConnected 4 ∧ ∃ n : ℕ, 3 ≤ n ∧ ∃ D : Decomposition X (cycleGraph n),
    (∀ h h', (cycleGraph n).Adj h h' → ((D.bags h).verts ∩ (D.bags h').verts).encard = 2) ∧
    ∀ h, Nonempty (partTorso D h ≃g completeGraph (Fin 3)) ∨
      ((partTorso D h).IsVertexConnected 3 ∧ ENat.card (D.bags h).verts ≤ 5)

/-- `X` is a generalised double-wheel with centre `{a, b}`: `X` is `4`-connected, `a ≠ b`, and
`X - a - b` has a cycle-decomposition (modelled on `C_n`, `n ≥ 3`) with all adhesion-sets of
size one, each of whose parts is a `K₂` or a triangle. -/
def IsGeneralisedDoubleWheel (X : SimpleGraph W) (a b : W) : Prop :=
  X.IsVertexConnected 4 ∧ a ≠ b ∧ ∃ n : ℕ, 3 ≤ n ∧
    ∃ D : Decomposition (X.induce ({a, b} : Set W)ᶜ) (cycleGraph n),
      (∀ h h', (cycleGraph n).Adj h h' → ((D.bags h).verts ∩ (D.bags h').verts).encard = 1) ∧
      ∀ h, Nonempty ((D.bags h).coe ≃g completeGraph (Fin 2)) ∨
        Nonempty ((D.bags h).coe ≃g completeGraph (Fin 3))

/-- `K_{4,m}` (left side `Fin 4`, right side `Fin m`) with the edges of `E` added on the left
side. -/
def k4mPlus (m : ℕ) (E : SimpleGraph (Fin 4)) : SimpleGraph (Fin 4 ⊕ Fin m) :=
  completeBipartiteGraph (Fin 4) (Fin m) ⊔ E.map Function.Embedding.inl

/-- `X` is a thickened `K_{4,m}`: a `K_{4,m}` whose left side is turned into a `K₄`. -/
def IsThickenedK4m (X : SimpleGraph W) (m : ℕ) : Prop :=
  Nonempty (X ≃g k4mPlus m ⊤)

/-- `X` is a sprinkled `K_{4,m}`: a `K_{4,m}` with any number of edges added to the left side. -/
def IsSprinkledK4m (X : SimpleGraph W) (m : ℕ) : Prop :=
  ∃ E : SimpleGraph (Fin 4), Nonempty (X ≃g k4mPlus m E)

end TorsoTypes

/-- The outcomes of Theorem 1 for a torso `τ` of a decomposition of `G`: (i) `τ` is
quasi-`5`-connected; (ii) a cycle of triangle-torsos and `3`-connected torsos on `≤ 5` vertices;
(iii) a generalised double-wheel; (iv) a thickened `K_{4,m}`, or `G` is a sprinkled `K_{4,m}`
with `m ≥ 4`. -/
def TorsoOutcome {V : Type u} {W : Type w} (G : SimpleGraph V) (τ : SimpleGraph W) : Prop :=
  IsQuasi5Connected τ ∨ IsCycleOfSmallTorsos τ ∨ (∃ a b, IsGeneralisedDoubleWheel τ a b) ∨
    (∃ m, IsThickenedK4m τ m) ∨ (∃ m, 4 ≤ m ∧ IsSprinkledK4m G m)

/-- Theorem 1 with Remark 1.2: if `G` is `4`-connected, a mixed-tree-decomposition determined by
the totally-nested tetra-separations of `G` exists, and every such decomposition is invariant
under the automorphisms of `G` and has all its torsos of one of the types (i)–(iv). -/
def MainTheorem1Statement {V : Type u} (G : SimpleGraph V) : Prop :=
  G.IsVertexConnected 4 →
    (∃ (T : Type u) (D : MixedTreeDecomp V T), D.IsDeterminedByTotallyNested G) ∧
    ∀ (T : Type u) (D : MixedTreeDecomp V T), D.IsDeterminedByTotallyNested G →
      D.IsAutInvariant G ∧ ∀ t, TorsoOutcome G (D.torso G t)

/-- Main Theorem 1 of Kurkofka–Planken, arXiv:2504.00760, for finite graphs: the canonical
decomposition of a `4`-connected graph along its totally-nested tetra-separations, with
classified torsos. -/
theorem P028 {V : Type u} [Finite V] (G : SimpleGraph V) : MainTheorem1Statement G := by
  sorry
