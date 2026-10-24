import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

open Function Set

namespace ClusteredHajos

universe u

variable {V : Type u}

/-- An unrestricted vertex coloring: in contrast with `SimpleGraph.Coloring`,
adjacent vertices may receive the same color. -/
abbrev VertexColoring (V C : Type*) := V → C

/-- The subgraph induced by the vertices receiving a specified color. -/
def monochromaticSubgraph (G : SimpleGraph V) {C : Type*}
    (c : VertexColoring V C) (a : C) : SimpleGraph {v : V // c v = a} :=
  G.induce {v | c v = a}

/-- A coloring has clustering `η` when every connected monochromatic
component has at most `η` vertices. -/
def HasClustering (G : SimpleGraph V) {C : Type*}
    (c : VertexColoring V C) (η : ℕ) : Prop :=
  ∀ a : C, ∀ K : (monochromaticSubgraph G c a).ConnectedComponent,
    Set.ncard K.supp ≤ η

/-- `G` admits a coloring with `k` colors and clustering `η`. -/
def ClusterColorable (G : SimpleGraph V) (k η : ℕ) : Prop :=
  ∃ c : VertexColoring V (Fin k), HasClustering G c η

/-- Increasing the permitted cluster size preserves clustered
colorability. -/
theorem ClusterColorable.monoClustering
    {G : SimpleGraph V} {k m n : ℕ}
    (h : ClusterColorable G k m) (hmn : m ≤ n) :
    ClusterColorable G k n := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun a K => (hc a K).trans hmn⟩

/-- One edge of the complete graph on `Fin n`, represented once by ordering
its endpoints. -/
abbrev CliqueEdge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

/-- The internal vertices of the route of the clique edge `e`: its vertices
other than the two branch vertices joined by `e`. -/
def routeInterior {n : ℕ} (branch : Fin n → V)
    (route : CliqueEdge n → List V) (e : CliqueEdge n) : Set V :=
  {v | v ∈ route e ∧ v ≠ branch e.1.1 ∧ v ≠ branch e.1.2}

/-- `G` contains a subdivision of `K_n`: distinct branch vertices and, for
each edge of `K_n`, a path in `G` (a repetition-free vertex list) between the
two branch vertices; no internal vertex is a branch vertex, and paths of
distinct clique edges are internally disjoint. -/
def IsCliqueSubdivision (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ branch : Fin n → V, Injective branch ∧
    ∃ route : CliqueEdge n → List V,
      (∀ e, (route e).head? = some (branch e.1.1)) ∧
      (∀ e, (route e).getLast? = some (branch e.1.2)) ∧
      (∀ e, (route e).IsChain G.Adj) ∧
      (∀ e, (route e).Nodup) ∧
      (∀ e i, branch i ∉ routeInterior branch route e) ∧
      (∀ e f, e ≠ f →
        Disjoint (routeInterior branch route e) (routeInterior branch route f))

/-- Theorem 6 of Liu–Wood, arXiv:1908.05597 (clustered Hajós): for every `s`
there is `η` such that every finite graph with no subdivision of `K_(s+1)` is
colorable with `max (4s − 5) 1` colors and clustering `η`. Subtraction is
truncated; the `max` keeps one color in the degenerate cases `s ≤ 1`. -/
theorem P046 (s : ℕ) :
    ∃ η : ℕ, ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
      ¬ IsCliqueSubdivision G (s + 1) →
        ClusterColorable G (max (4 * s - 5) 1) η := by
  sorry

end ClusteredHajos
