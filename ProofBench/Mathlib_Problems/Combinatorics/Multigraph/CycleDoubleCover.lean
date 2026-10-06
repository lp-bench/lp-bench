import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic

universe u v

/-- A finite multigraph with vertex type `V` and edge-index type `E`.
Parallel edges and loops are allowed. -/
structure Multigraph (V : Type u) (E : Type v) where
  /-- The unordered pair of endpoints of an edge. -/
  ends : E → Sym2 V

namespace Multigraph

variable {V : Type u} {E : Type v}
variable [DecidableEq V] [DecidableEq E] [Fintype E]
variable (M : Multigraph V E)

/-- The edge `e` is incident with the vertex `v`. -/
def Inc (e : E) (v : V) : Prop :=
  v ∈ M.ends e

/-- The edge `e` is a loop. -/
def IsLoop (e : E) : Prop :=
  (M.ends e).IsDiag

instance (e : E) (v : V) : Decidable (M.Inc e v) :=
  inferInstanceAs (Decidable (v ∈ M.ends e))

instance (e : E) : Decidable (M.IsLoop e) :=
  inferInstanceAs (Decidable (M.ends e).IsDiag)

/-- The non-loop edges incident with `v`. -/
def incidenceFinset (v : V) : Finset E :=
  Finset.univ.filter fun e ↦ M.Inc e v ∧ ¬M.IsLoop e

/-- The underlying simple graph, obtained by forgetting loops and multiplicities. -/
def toSimpleGraph : SimpleGraph V :=
  SimpleGraph.fromRel fun a b ↦ ∃ e, M.ends e = s(a, b)

instance : DecidableRel M.toSimpleGraph.Adj := fun a b ↦ by
  change Decidable
    (a ≠ b ∧ ((∃ e, M.ends e = s(a, b)) ∨ ∃ e, M.ends e = s(b, a)))
  infer_instance

/-- Delete one edge while retaining every vertex. -/
def deleteEdge (e : E) : Multigraph V {e' : E // e' ≠ e} :=
  ⟨fun e' ↦ M.ends e'.1⟩

/-- An edge is a bridge if deleting it disconnects its endpoints. -/
def IsBridge (e : E) : Prop :=
  ∀ x y, M.ends e = s(x, y) → ¬(M.deleteEdge e).toSimpleGraph.Reachable x y

/-- A multigraph is bridgeless when none of its edges is a bridge. -/
def Bridgeless : Prop :=
  ∀ e, ¬M.IsBridge e

/-- A multigraph is simple when it has no loops and no two edge objects have
the same unordered pair of endpoints. -/
def IsSimple : Prop :=
  (∀ e, ¬M.IsLoop e) ∧ Function.Injective M.ends

/-- A proper edge-colouring with three colours.  Properness says that edges
incident with the same vertex have distinct colours. -/
structure ProperThreeEdgeColoring where
  color : E → Fin 3
  proper : ∀ v : V, Set.InjOn color ↑(M.incidenceFinset v)

/-- An edge set is even when every vertex is incident with an even number of
its non-loop edges. Loops contribute twice and hence vanish modulo two. -/
def IsEvenEdgeSet (F : Finset E) : Prop :=
  ∀ v : V, ∑ e ∈ M.incidenceFinset v, (if e ∈ F then (1 : ZMod 2) else 0) = 0

/-- A cycle is a nonempty inclusion-minimal even edge set. This is the usual
multigraph circuit notion: a loop is a one-edge cycle and two parallel edges
can form a two-edge cycle. -/
structure Cycle where
  edges : Finset E
  nonempty : edges.Nonempty
  even : M.IsEvenEdgeSet edges
  minimal : ∀ D : Finset E, D.Nonempty → D ⊆ edges → M.IsEvenEdgeSet D → D = edges

/-- Every cycle has at least `g` edges.  Girth at least `3` already forces
simplicity: a loop is a one-edge cycle and two parallel edges form a
two-edge cycle. -/
def HasGirthAtLeast (g : ℕ) : Prop :=
  ∀ C : M.Cycle, g ≤ C.edges.card

/-- A finite multiset of cycles in which every edge occurs exactly twice.
The list representation retains repeated cycles. -/
structure CycleDoubleCover where
  cycles : List M.Cycle
  coveredTwice : ∀ e : E, (cycles.filter fun C ↦ e ∈ C.edges).length = 2

noncomputable instance : Fintype M.Cycle :=
  Fintype.ofInjective Cycle.edges fun C D h ↦ by
    cases C
    cases D
    cases h
    rfl

/-- A circuit double cover represented canonically by the multiplicity
`0`, `1`, or `2` of each cycle. -/
def IsCircuitDoubleCover (C : M.Cycle → Fin 3) : Prop :=
  ∀ e : E, (∑ D : M.Cycle, if e ∈ D.edges then (C D : ℕ) else 0) = 2

/-- The finite set of all circuit double covers, in canonical multiplicity
form rather than as lists with arbitrary order. -/
noncomputable def circuitDoubleCovers : Finset (M.Cycle → Fin 3) := by
  classical
  exact Finset.univ.filter M.IsCircuitDoubleCover

end Multigraph
