import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Decks of a graph

Shared statement-layer vocabulary for the reconstruction problems (P080, …).  The
*card* of a graph `G` at a vertex `v` is the vertex-deleted subgraph `G - v`, the
subgraph induced on the other vertices.  Two graphs have the *same deck* when there is a
bijection between their vertex sets pairing each card with an isomorphic card; the
isomorphisms of the individual cards are not required to agree with each other or with
the bijection.  Multiplicities are retained.
-/

universe u v

namespace SimpleGraph

variable {V : Type u} {V' : Type v}

/-- The card of `G` at `v`: the vertex-deleted subgraph `G - v`, induced on the vertices
other than `v`. -/
abbrev cardAt (G : SimpleGraph V) (v : V) : SimpleGraph ({w : V | w ≠ v} : Set V) :=
  G.induce {w | w ≠ v}

/-- `G` and `G'` have the same deck: a bijection `σ` between the vertex sets such that the
card of `G` at `v` is isomorphic to the card of `G'` at `σ v`, for every `v`. -/
def SameDeck (G : SimpleGraph V) (G' : SimpleGraph V') : Prop :=
  ∃ σ : V ≃ V', ∀ v, Nonempty (G.cardAt v ≃g G'.cardAt (σ v))

end SimpleGraph
