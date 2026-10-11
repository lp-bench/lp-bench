import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Fin.VecNotation

noncomputable section

open SimpleGraph

variable {V : Type*}

/- A **finite hypergraph** `H = (V, E)` on a vertex type `α`: a finite vertex
set `vertices` together with a set `edges` of hyperedges, each a subset of `V`. -/
structure FinHypergraph (α : Type*) where
  vertices : Finset α
  edges : Set (Finset α)
  edges_subset_vertices : ∀ e ∈ edges, e ⊆ vertices

variable (H : FinHypergraph V)

namespace FinHypergraph

/- C is a vertex cover if every edge contains a vertex in C. -/
def IsVertexCover (C : Finset V) : Prop :=
  C ⊆ H.vertices ∧
    ∀ ⦃e : Finset V⦄, e ∈ H.edges → ∃ v : V, v ∈ C ∧ v ∈ e

/- The **cover number** `τ(H)`: the least cardinality of a vertex cover, as an
`sInf` over the achievable cover cardinalities (`0` if no cover exists). -/
def coverNumber : ℕ :=
  sInf {n | ∃ C : Finset V, H.IsVertexCover C ∧ C.card = n}

/- M is a matching if its edges are pairwise disjoint. -/
def IsMatching (M : Finset (Finset V)) : Prop :=
  (∀ ⦃e : Finset V⦄, e ∈ M → e ∈ H.edges) ∧
    ∀ ⦃e₁ : Finset V⦄, e₁ ∈ M →
      ∀ ⦃e₂ : Finset V⦄, e₂ ∈ M → e₁ ≠ e₂ → Disjoint e₁ e₂

/- The **matching number** `ν(H)`: the largest size of a matching, as an
`sSup` over the achievable matching sizes (always attained, since the empty
matching gives nonemptiness and matchings live in the finite powerset of the
vertex set). -/
def matchingNumber : ℕ :=
  sSup {n | ∃ M : Finset (Finset V), H.IsMatching M ∧ M.card = n}

/-! ### Spec lemmas for `coverNumber` and `matchingNumber`-/

variable [DecidableEq V]

def IsUniform (r : ℕ) : Prop :=
  ∀ ⦃e : Finset V⦄, e ∈ H.edges → e.card = r

/- H is r-partite if vertices can be partitioned into r parts,
    each edge containing exactly one vertex from each part. -/
def IsPartite (r : ℕ) : Prop :=
  ∃ parts : Fin r → Finset V,
    (∀ v : V, v ∈ H.vertices ↔ ∃ i : Fin r, v ∈ parts i) ∧
      (∀ i j : Fin r, i ≠ j → Disjoint (parts i) (parts j)) ∧
        (∀ ⦃e : Finset V⦄, e ∈ H.edges →
          ∀ i : Fin r, ((parts i) ∩ e).card = 1)

/- The **canonical simple graph** of a hypergraph: `u ~ v` iff `{u, v}` is a
hyperedge.  For a 2-uniform hypergraph this is a faithful encoding. -/
def toSimpleGraph (H : FinHypergraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ({u, v} : Finset V) ∈ H.edges
  symm := ⟨fun {u v} h => ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

end FinHypergraph

def SimpleGraph.matchingNumber (G : SimpleGraph V) : ℕ∞ :=
  ⨆ (M : G.Subgraph) (_ : M.IsMatching), M.edgeSet.encard

variable [DecidableEq V]

/-- **Graph → hypergraph.** -/
def SimpleGraph.toHypergraph (G : SimpleGraph V) [Fintype V] : FinHypergraph V where
  vertices := Finset.univ
  edges := {e : Finset V | ∃ u v, G.Adj u v ∧ e = {u, v}}
  edges_subset_vertices := fun e _ => Finset.subset_univ e

/-! ### Matching correspondence helpers -/

/- Send a graph edge `s(a,b)` to the pair `{a,b}`. -/
def pairMap : Sym2 V → Finset V :=
  Sym2.lift ⟨fun a b => ({a, b} : Finset V), fun a b => Finset.pair_comm a b⟩
