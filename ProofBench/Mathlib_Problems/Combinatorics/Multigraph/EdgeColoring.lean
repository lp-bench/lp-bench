import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.CycleDoubleCover
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.RotationSystem

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
variable (M : Multigraph V E)

/-- The degree of a vertex: the number of incident non-loop edges. -/
def degree (v : V) : ℕ := (M.incidenceFinset v).card

/-- Every vertex has degree `d`. -/
def IsRegular (d : ℕ) : Prop := ∀ v : V, M.degree v = d

/-- The edges crossing the vertex set `S`: one endpoint inside and one
outside.  Loops never cross. -/
noncomputable def crossingEdges (S : Finset V) : Finset E := by
  classical
  exact Finset.univ.filter fun e =>
    (∃ x ∈ M.ends e, x ∈ S) ∧ ∃ y ∈ M.ends e, y ∉ S

/-- Every odd proper vertex set is crossed by at least `d` edges. -/
def OddlyEdgeConnected [Fintype V] (d : ℕ) : Prop :=
  ∀ S : Finset V, Odd S.card → S ≠ Finset.univ →
    d ≤ (M.crossingEdges S).card

/-- Every proper nonempty vertex set is crossed by at least `d` edges. -/
def EdgeConnected [Fintype V] (d : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    d ≤ (M.crossingEdges S).card

/-- A perfect matching of edges: every vertex is incident with exactly one
matching edge. -/
def IsPerfectMatchingSet (P : Finset E) : Prop :=
  ∀ v : V, (M.incidenceFinset v ∩ P).card = 1

/-- A proper edge colouring with `d` colours exists: edges incident with a
common vertex receive distinct colours. -/
def EdgeColorable (d : ℕ) : Prop :=
  ∃ c : E → Fin d, ∀ v : V, Set.InjOn c ↑(M.incidenceFinset v)

/-- Planarity of a multigraph through its underlying simple graph: parallel
edges and loops never obstruct an embedding in the sphere. -/
def IsPlanar [Finite V] : Prop := M.toSimpleGraph.IsGenusZero

end Multigraph
