import Mathlib.Combinatorics.Hypergraph.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Real.Basic


open scoped BigOperators Hypergraph

namespace DiracLinearHypergraphs

attribute [local instance] Classical.dec

/-- The hypergraph has the whole ambient finite type as its vertex set. -/
def IsSpanning {V : Type*} (H : Hypergraph V) : Prop :=
  V(H) = Set.univ

/-- Every edge has exactly `k` vertices. -/
def IsUniform {V : Type*} (k : ℕ) (H : Hypergraph V) : Prop :=
  ∀ e ∈ E(H), Set.ncard e = k

/-- Distinct edges of a linear hypergraph meet in at most one vertex. -/
def IsLinear {V : Type*} (H : Hypergraph V) : Prop :=
  ∀ e ∈ E(H), ∀ f ∈ E(H), e ≠ f → Set.ncard (e ∩ f) ≤ 1

/-- The finite edge set of a hypergraph on a finite ambient type. -/
noncomputable def edgeFinset {V : Type*} [Fintype V]
    (H : Hypergraph V) : Finset (Set V) :=
  Finset.univ.filter fun e => e ∈ E(H)

/-- Membership in `edgeFinset` is membership in the edge set. -/
@[simp] theorem mem_edgeFinset {V : Type*} [Fintype V]
    (H : Hypergraph V) (e : Set V) :
    e ∈ edgeFinset H ↔ e ∈ E(H) := by
  simp [edgeFinset]

/-- The degree of a vertex. -/
noncomputable def vertexDegree {V : Type*} [Fintype V]
    (H : Hypergraph V) (v : V) : ℕ :=
  ((edgeFinset H).filter fun e => v ∈ e).card

/--
The minimum vertex degree.  The edge count is added as an upper sentinel so
that the minimum is always defined; it is the usual minimum when `V` is
nonempty.
-/
noncomputable def minimumVertexDegree {V : Type*} [Fintype V]
    (H : Hypergraph V) : ℕ :=
  (insert (edgeFinset H).card
    ((Finset.univ : Finset V).image (vertexDegree H))).min' (by simp)

/-- The minimum vertex degree is at most every vertex degree. -/
theorem minimumVertexDegree_le {V : Type*} [Fintype V]
    (H : Hypergraph V) (v : V) :
    minimumVertexDegree H ≤ vertexDegree H v := by
  apply Finset.min'_le
  simp

/-- A matching is a finite pairwise-disjoint collection of edges. -/
def IsMatching {V : Type*} (H : Hypergraph V) (M : Finset (Set V)) : Prop :=
  (∀ e ∈ M, e ∈ E(H)) ∧ (M : Set (Set V)).PairwiseDisjoint id

/-- The set of vertices covered by a matching. -/
def coveredVertices {V : Type*} (M : Finset (Set V)) : Set V :=
  ⋃₀ (M : Set (Set V))

/-- A matching covers only vertices of the hypergraph. -/
theorem IsMatching.coveredVertices_subset {V : Type*} {H : Hypergraph V}
    {M : Finset (Set V)} (hM : IsMatching H M) :
    coveredVertices M ⊆ V(H) := by
  intro v hv
  rcases hv with ⟨e, heM, hve⟩
  exact Hypergraph.mem_vertexSet_of_mem_edgeSet (hM.1 e heM) hve

/-- A matching covers at least a `(1-ε)` proportion of the ambient vertices. -/
def CoversAtLeast {V : Type*} [Fintype V]
    (M : Finset (Set V)) (ε : ℝ) : Prop :=
  (1 - ε) * (Fintype.card V : ℝ) ≤ (Set.ncard (coveredVertices M) : ℝ)

/-- The conclusion of Theorem 1.2 for one hypergraph. -/
def HasAlmostPerfectMatching {V : Type*} [Fintype V]
    (H : Hypergraph V) (ε : ℝ) : Prop :=
  ∃ M : Finset (Set V), IsMatching H M ∧ CoversAtLeast M ε

/--
For `ε > 0` and `k ≥ 2`, every sufficiently large `n`-vertex linear
`k`-graph with minimum degree at least `n/k + C` has a matching covering at
least `(1-ε)n` vertices.  Theorem 1.2 of Im–Lee, arXiv:2403.14269.
-/
theorem P050
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k) :
    ∃ C n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ n : ℕ, n₀ ≤ n →
        ∀ H : Hypergraph (Fin n),
          IsSpanning H → IsUniform k H → IsLinear H →
            (n : ℝ) / (k : ℝ) + (C : ℝ) ≤
                (minimumVertexDegree H : ℝ) →
              HasAlmostPerfectMatching H ε := by
  sorry

end DiracLinearHypergraphs
