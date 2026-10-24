import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Fin.VecNotation

noncomputable section

open SimpleGraph

variable {V : Type*}

/-- A finite hypergraph on `α`: a finite vertex set together with a set of
hyperedges, each a subset of the vertex set. -/
structure FinHypergraph (α : Type*) where
  vertices : Finset α
  edges : Set (Finset α)
  edges_subset_vertices : ∀ e ∈ edges, e ⊆ vertices

variable (H : FinHypergraph V)

namespace FinHypergraph

/-- `C` is a vertex cover of `H`: a set of vertices of `H` meeting every edge. -/
def IsVertexCover (C : Finset V) : Prop :=
  C ⊆ H.vertices ∧
    ∀ ⦃e : Finset V⦄, e ∈ H.edges → ∃ v : V, v ∈ C ∧ v ∈ e

/-- The cover number `τ(H)`: the least size of a vertex cover, as an `sInf`
(`0` if no cover exists, which happens only when some edge is empty). -/
def coverNumber : ℕ :=
  sInf {n | ∃ C : Finset V, H.IsVertexCover C ∧ C.card = n}

/-- `M` is a matching of `H`: a set of pairwise disjoint edges of `H`. -/
def IsMatching (M : Finset (Finset V)) : Prop :=
  (∀ ⦃e : Finset V⦄, e ∈ M → e ∈ H.edges) ∧
    ∀ ⦃e₁ : Finset V⦄, e₁ ∈ M →
      ∀ ⦃e₂ : Finset V⦄, e₂ ∈ M → e₁ ≠ e₂ → Disjoint e₁ e₂

/-- The matching number `ν(H)`: the largest size of a matching, as an `sSup`
(a maximum, since there are finitely many matchings). -/
def matchingNumber : ℕ :=
  sSup {n | ∃ M : Finset (Finset V), H.IsMatching M ∧ M.card = n}

variable [DecidableEq V]

/-- `H` is `r`-uniform: every edge has exactly `r` vertices. -/
def IsUniform (r : ℕ) : Prop :=
  ∀ ⦃e : Finset V⦄, e ∈ H.edges → e.card = r

/-- `H` is `r`-partite: its vertex set is split into `r` pairwise disjoint parts
and every edge has exactly one vertex in each part. -/
def IsPartite (r : ℕ) : Prop :=
  ∃ parts : Fin r → Finset V,
    (∀ v : V, v ∈ H.vertices ↔ ∃ i : Fin r, v ∈ parts i) ∧
      (∀ i j : Fin r, i ≠ j → Disjoint (parts i) (parts j)) ∧
        (∀ ⦃e : Finset V⦄, e ∈ H.edges →
          ∀ i : Fin r, ((parts i) ∩ e).card = 1)

/-- The simple graph of `H`: `u ~ v` iff `u ≠ v` and `{u, v}` is an edge of `H`. -/
def toSimpleGraph (H : FinHypergraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ({u, v} : Finset V) ∈ H.edges
  symm := ⟨fun {u v} h => ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

end FinHypergraph

/-- The matching number of a simple graph: the supremum in `ℕ∞` of the number
of edges of a matching. -/
def SimpleGraph.matchingNumber (G : SimpleGraph V) : ℕ∞ :=
  ⨆ (M : G.Subgraph) (_ : M.IsMatching), M.edgeSet.encard

variable [DecidableEq V]

/-- The hypergraph of a finite simple graph: all vertices, and an edge `{u, v}`
for each adjacent pair. -/
def SimpleGraph.toHypergraph (G : SimpleGraph V) [Fintype V] : FinHypergraph V where
  vertices := Finset.univ
  edges := {e : Finset V | ∃ u v, G.Adj u v ∧ e = {u, v}}
  edges_subset_vertices := fun e _ => Finset.subset_univ e

/-- The pair `{a, b}` of a graph edge `s(a, b)`. -/
def pairMap : Sym2 V → Finset V :=
  Sym2.lift ⟨fun a b => ({a, b} : Finset V), fun a b => Finset.pair_comm a b⟩
