import Mathlib

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

/-- A finite hypergraph with possible parallel edges: `edges` is a finite set of
edge labels from `I`, each with a support in `vertices`, and different labels may
have the same support. -/
structure FiniteMultiHypergraph (V I : Type*) [DecidableEq V] [DecidableEq I] where
  vertices : Finset V
  edges : Finset I
  support : I → Finset V
  edge_subset_vertices : ∀ e, e ∈ edges → support e ⊆ vertices

namespace FiniteMultiHypergraph

variable (H : FiniteMultiHypergraph V I)

/-- The incident edge labels at a vertex. -/
def incidentEdges (v : V) : Finset I :=
  H.edges.filter fun e => v ∈ H.support e

/-- The degree of a vertex, counting parallel edges with multiplicity. -/
def degree (v : V) : ℕ :=
  (H.incidentEdges v).card

/-- The degree of a vertex inside a selected edge-label set. -/
def degreeIn (M : Finset I) (v : V) : ℕ :=
  (M.filter fun e => v ∈ H.support e).card

/-- `H.IsUniform r`: every edge label has support of cardinality `r`. -/
def IsUniform (r : ℕ) : Prop :=
  ∀ e, e ∈ H.edges → (H.support e).card = r

/-- Every vertex has degree at least `d`. -/
def MinDegreeAtLeast (d : ℕ) : Prop :=
  ∀ v, v ∈ H.vertices → d ≤ H.degree v

/-- Every vertex has degree at most `D`. -/
def MaxDegreeAtMost (D : ℕ) : Prop :=
  ∀ v, v ∈ H.vertices → H.degree v ≤ D

/-- `H` is `μ`-near-regular: for some integers `0 < δ` and `Δ ≤ μ·δ`, every
vertex has degree between `δ` and `Δ`. -/
def IsNearRegular (μ : ℝ) : Prop :=
  ∃ δ Δ : ℕ,
    0 < δ ∧
      (Δ : ℝ) ≤ μ * (δ : ℝ) ∧
      H.MinDegreeAtLeast δ ∧
      H.MaxDegreeAtMost Δ

/-- A selected edge-label set hits every vertex. -/
def IsHittingEdgeSet (M : Finset I) : Prop :=
  M ⊆ H.edges ∧ ∀ v, v ∈ H.vertices → 1 ≤ H.degreeIn M v

/-- A selected edge-label set is both hitting and `t`-shallow. -/
def IsShallowHittingEdgeSet (t : ℕ) (M : Finset I) : Prop :=
  M ⊆ H.edges ∧ ∀ v, v ∈ H.vertices → 1 ≤ H.degreeIn M v ∧ H.degreeIn M v ≤ t

/-- Existence of a `t`-shallow hitting edge set. -/
def HasShallowHittingEdgeSet (t : ℕ) : Prop :=
  ∃ M : Finset I, H.IsShallowHittingEdgeSet t M

/-- The incident edge labels at a vertex are edge labels of `H`. -/
@[simp] theorem incidentEdges_subset_edges (v : V) : H.incidentEdges v ⊆ H.edges := by
  intro e he
  exact (Finset.mem_filter.mp he).1

/-- A shallow hitting edge set is a hitting edge set. -/
theorem shallowHitting_isHitting {t : ℕ} {M : Finset I}
    (hM : H.IsShallowHittingEdgeSet t M) : H.IsHittingEdgeSet M :=
  ⟨hM.1, fun v hv => (hM.2 v hv).1⟩

end FiniteMultiHypergraph
