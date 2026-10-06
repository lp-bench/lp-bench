/- Paper: A hypergraph bandwidth theorem (Lang–Sanhueza-Matamala, arXiv:2412.14891). -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hypergraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Basic


open scoped BigOperators Hypergraph
open Set

namespace HypergraphBandwidth

universe u v

/-! ## Basic finite-uniform hypergraph notions -/

/-- A hypergraph is spanning when its declared vertex set is the whole ambient type. -/
def IsSpanning {V : Type u} (G : Hypergraph V) : Prop :=
  V(G) = Set.univ

/-- Every edge of `G` has exactly `k` vertices. -/
def IsUniform {V : Type u} (k : ℕ) (G : Hypergraph V) : Prop :=
  ∀ e ∈ E(G), Set.ncard e = k

/-- `F` is a spanning subhypergraph of `G`. -/
def IsSpanningSubgraph {V : Type u} (F G : Hypergraph V) : Prop :=
  V(F) = V(G) ∧ E(F) ⊆ E(G)

/-- The union of two hypergraphs on the same ambient vertex type. -/
def edgeUnion {V : Type u} (G H : Hypergraph V) : Hypergraph V where
  vertexSet := V(G) ∪ V(H)
  edgeSet := E(G) ∪ E(H)
  subset_vertexSet_of_mem_edgeSet' := by
    intro e he
    rcases he with he | he
    · exact (G.subset_vertexSet_of_mem_edgeSet he).trans Set.subset_union_left
    · exact (H.subset_vertexSet_of_mem_edgeSet he).trans Set.subset_union_right

/-- A vertex map is a hypergraph homomorphism if it maps vertices and edges into the target. -/
def IsHom {V : Type u} {W : Type v} (H : Hypergraph V) (G : Hypergraph W)
    (f : V → W) : Prop :=
  Set.MapsTo f V(H) V(G) ∧ ∀ e ∈ E(H), f '' e ∈ E(G)

/-- `H` embeds into `G` if an injective hypergraph homomorphism exists. -/
def Embeds {V : Type u} {W : Type v} (H : Hypergraph V) (G : Hypergraph W) : Prop :=
  ∃ f : V ↪ W, IsHom H G f

/-! ## Tight cycles, their powers, and closed walks -/

/-- The cyclic interval of `length` vertices beginning at `start` in `Fin q`. -/
def cyclicBlock (q length : ℕ) (start : Fin q) : Set (Fin q) :=
  {x | ∃ j : Fin length, x.val = (start.val + j.val) % q}

/--
The `(t - k + 1)`-st power of the `k`-uniform cycle on `q` vertices.

Its edges are the `k`-sets contained in some cyclic interval of `t` vertices.
-/
def cyclePower (k t q : ℕ) : Hypergraph (Fin q) where
  vertexSet := Set.univ
  edgeSet := {e | Set.ncard e = k ∧ ∃ start : Fin q, e ⊆ cyclicBlock q t start}
  subset_vertexSet_of_mem_edgeSet' := by
    intro e _
    exact Set.subset_univ e

/-- A closed tight walk of order `q` is a homomorphic image of the tight `k`-uniform
cycle on `q` vertices (the cycle power with `t = k`). -/
def HasClosedWalkOfOrder {V : Type u} (G : Hypergraph V) (k q : ℕ) : Prop :=
  k ≤ q ∧ ∃ φ : Fin q → V, IsHom (cyclePower k k q) G φ

/-- The paper's aperiodicity condition: a closed walk has order `1 mod k`. -/
def IsAperiodic {V : Type u} (k : ℕ) (G : Hypergraph V) : Prop :=
  ∃ q : ℕ, 0 < q ∧ q % k = 1 % k ∧ HasClosedWalkOfOrder G k q

/-! ## Tight connectivity and components -/

/--
The line graph whose vertices are hyperedges and whose adjacency means overlap
in exactly `k - 1` vertices.
-/
def tightLineGraph {V : Type u} (k : ℕ) (G : Hypergraph V) :
    SimpleGraph {e : Set V // e ∈ E(G)} where
  Adj e f := e ≠ f ∧ Set.ncard ((e : Set V) ∩ (f : Set V)) = k - 1
  symm := ⟨by
    intro e f h
    exact ⟨h.1.symm, by simpa [Set.inter_comm] using h.2⟩⟩
  loopless := ⟨by
    intro e h
    exact h.1 rfl⟩

/-- Connectivity from Section 3.1: no isolated vertices and connected tight line graph. -/
def IsTightConnected {V : Type u} (k : ℕ) (G : Hypergraph V) : Prop :=
  (∀ v ∈ V(G), ∃ e ∈ E(G), v ∈ e) ∧ (tightLineGraph k G).Connected

/-- An edge-maximal spanning tightly connected subhypergraph. -/
def IsComponent {V : Type u} (k : ℕ) (F G : Hypergraph V) : Prop :=
  IsSpanningSubgraph F G ∧ IsTightConnected k F ∧
    ∀ J : Hypergraph V,
      IsSpanningSubgraph J G → E(F) ⊆ E(J) → IsTightConnected k J → E(J) ⊆ E(F)

/-! ## Fractional matchings -/

/-- The total fractional-matching weight incident with a vertex. -/
noncomputable def vertexLoad {V : Type u} [Fintype V]
    (weight : Set V → ℝ) (v : V) : ℝ := by
  classical
  exact ∑ e : Set V, if v ∈ e then weight e else 0

/-- A fractional matching, extended by zero from the edge set to all vertex subsets. -/
structure FractionalMatching {V : Type u} [Fintype V] (G : Hypergraph V) where
  weight : Set V → ℝ
  zero_of_not_edge : ∀ e, e ∉ E(G) → weight e = 0
  nonnegative : ∀ e, 0 ≤ weight e
  at_most_one : ∀ e, weight e ≤ 1
  vertex_capacity : ∀ v ∈ V(G),
    vertexLoad weight v ≤ 1

/-- A perfect fractional matching has total weight `|V(G)| / k`. -/
def HasPerfectFractionalMatching {V : Type u} [Fintype V]
    (k : ℕ) (G : Hypergraph V) : Prop :=
  ∃ ω : FractionalMatching G,
    ∑ e : Set V, ω.weight e = (Set.ncard V(G) : ℝ) / (k : ℝ)

/-! ## Hamilton frameworks -/

/--
`G` is a model of deleting `x` from `J`, with `ι` supplying the relabelling
from `Fin s` onto the remaining vertices.
-/
def IsVertexDeletionModel (s : ℕ) (J : Hypergraph (Fin (s + 1)))
    (x : Fin (s + 1)) (G : Hypergraph (Fin s)) (ι : Fin s ↪ Fin (s + 1)) : Prop :=
  Set.range ι = {v | v ≠ x} ∧
    ∀ e : Set (Fin s), e ∈ E(G) ↔ ι '' e ∈ E(J)

/--
A Hamilton framework for a family of `s`-vertex `t`-graphs, implementing
conditions (F1)--(F4) of Definition 3.1.
-/
structure HamiltonFramework (t s : ℕ) (P : Set (Hypergraph (Fin s))) where
  framework : Hypergraph (Fin s) → Hypergraph (Fin s)
  member_spanning : ∀ G ∈ P, IsSpanning G
  member_uniform : ∀ G ∈ P, IsUniform t G
  component : ∀ G ∈ P, IsComponent t (framework G) G
  perfect_fractional_matching : ∀ G ∈ P,
    HasPerfectFractionalMatching t (framework G)
  aperiodic : ∀ G ∈ P, IsAperiodic t (framework G)
  consistent : ∀ G ∈ P, ∀ G' ∈ P,
    ∀ (J : Hypergraph (Fin (s + 1))) (x y : Fin (s + 1)), x ≠ y →
      ∀ (ι : Fin s ↪ Fin (s + 1)) (ι' : Fin s ↪ Fin (s + 1)),
        IsVertexDeletionModel s J x G ι →
          IsVertexDeletionModel s J y G' ι' →
            IsTightConnected t
              (edgeUnion ((framework G).image ι) ((framework G').image ι'))

/-- The family `P` admits at least one Hamilton framework. -/
def AdmitsHamiltonFramework (t s : ℕ) (P : Set (Hypergraph (Fin s))) : Prop :=
  Nonempty (HamiltonFramework t s P)

/-! ## Clique and property hypergraphs -/

/--
The `t`-uniform clique hypergraph `K_t(G)`: its edges are the `t`-sets every
`k`-subset of which is an edge of `G`.
-/
def cliqueGraph {V : Type u} (k t : ℕ) (G : Hypergraph V) : Hypergraph V where
  vertexSet := V(G)
  edgeSet := {S | S ⊆ V(G) ∧ Set.ncard S = t ∧
    ∀ e : Set V, e ⊆ S → Set.ncard e = k → e ∈ E(G)}
  subset_vertexSet_of_mem_edgeSet' := by
    intro S hS
    exact hS.1

/-- `F` is isomorphic to the subhypergraph of `G` induced on the range of `ι`. -/
def RealizesOn {V : Type u} {s : ℕ} (G : Hypergraph V)
    (F : Hypergraph (Fin s)) (ι : Fin s ↪ V) : Prop :=
  Set.range ι ⊆ V(G) ∧
    ∀ e : Set (Fin s), e ∈ E(F) ↔ ι '' e ∈ E(G)

/-- The `s`-uniform property hypergraph from Definition 3.3. -/
def propertyGraph {V : Type u} (s : ℕ) (G : Hypergraph V)
    (P : Set (Hypergraph (Fin s))) : Hypergraph V where
  vertexSet := V(G)
  edgeSet := {S | S ⊆ V(G) ∧ Set.ncard S = s ∧
    ∃ F ∈ P, ∃ ι : Fin s ↪ V, Set.range ι = S ∧ RealizesOn G F ι}
  subset_vertexSet_of_mem_edgeSet' := by
    intro S hS
    exact hS.1

/-- The number of edges containing a prescribed vertex set. -/
noncomputable def degreeAt {V : Type u} (G : Hypergraph V) (X : Set V) : ℕ :=
  Set.ncard {e | e ∈ E(G) ∧ X ⊆ e}

/-- Every `r`-set has degree at least the real-valued bound `B`. -/
def HasMinDegreeAtLeast {V : Type u} (G : Hypergraph V) (r : ℕ) (B : ℝ) : Prop :=
  ∀ X ⊆ V(G), Set.ncard X = r → B ≤ (degreeAt G X : ℝ)

/--
Robust satisfaction from Definition 3.4.  For a `uniformity`-graph the paper
sets `r = 2 * uniformity` and density `1 - 1 / s^2` in the property graph.
-/
def RobustlySatisfies {V : Type u} [Fintype V] (uniformity s : ℕ)
    (G : Hypergraph V) (P : Set (Hypergraph (Fin s))) : Prop :=
  let r := 2 * uniformity
  HasMinDegreeAtLeast (propertyGraph s G P) r
    ((1 - 1 / (s : ℝ) ^ 2) *
      (Nat.choose (Set.ncard V(G) - r) (s - r) : ℝ))

/-! ## Blow-ups and the polylog-log cluster bound -/

/-- The numerical cluster-size bound `(log (log n))^c`. -/
noncomputable def polylogLogBound (c : ℝ) (n : ℕ) : ℝ :=
  (Real.log (Real.log (n : ℝ))) ^ c

/--
`H` is a blow-up of a power of a tight `k`-cycle.  The map `cluster` assigns
each vertex to a nonempty base-cycle cluster.  Every base edge is replaced by
the complete partite `k`-graph across its clusters.
-/
def IsBlowUpOfCyclePower {V : Type u} [Fintype V]
    (H : Hypergraph V) (k t : ℕ) (c : ℝ) : Prop :=
  IsSpanning H ∧
    ∃ q : ℕ, t ≤ q ∧
      ∃ cluster : V → Fin q,
        Function.Surjective cluster ∧
          (∀ e : Set V,
            e ∈ E(H) ↔ Set.ncard e = k ∧ cluster '' e ∈ E(cyclePower k t q)) ∧
          ∀ i : Fin q,
            (Set.ncard {v : V | cluster v = i} : ℝ) ≤
              polylogLogBound c (Fintype.card V)

theorem IsBlowUpOfCyclePower.isUniform {V : Type u} [Fintype V]
    {H : Hypergraph V} {k t : ℕ} {c : ℝ}
    (hH : IsBlowUpOfCyclePower H k t c) : IsUniform k H := by
  rcases hH.2 with ⟨q, _htq, cluster, _hsurj, hedge, _hbound⟩
  intro e he
  exact (hedge e).mp he |>.1

/-! ## Main theorem -/

/--
**Theorem 3.5 (General Hypergraph Bandwidth Theorem).**

For fixed `k`, `t`, and sampling size `s`, every sufficiently large `k`-graph
whose `t`-clique graph robustly satisfies a family admitting a Hamilton
framework contains every spanning blow-up of the `(t - k + 1)`-st power of a
tight `k`-cycle whose clusters have polylog-logarithmic size.
-/
theorem P048
    (k t s : ℕ) (hk : 2 ≤ k) (hkt : k ≤ t) (hts : 2 * t ≤ s) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {V : Type u} {W : Type v} [Fintype V] [Fintype W],
        ∀ (P : Set (Hypergraph (Fin s))) (G : Hypergraph V) (H : Hypergraph W),
          n₀ ≤ Fintype.card V →
            Fintype.card W = Fintype.card V →
              IsSpanning G →
                IsUniform k G →
                  AdmitsHamiltonFramework t s P →
                    RobustlySatisfies t s (cliqueGraph k t G) P →
                      IsBlowUpOfCyclePower H k t c →
                        Embeds H G := by
  sorry

end HypergraphBandwidth
