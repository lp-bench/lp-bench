import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite

universe u v

namespace SimpleGraph

variable {V : Type u} {V' : Type v}

/-- The card of `G` at `v`: the vertex-deleted subgraph `G - v`, induced on the vertices
other than `v`. -/
abbrev cardAt (G : SimpleGraph V) (v : V) : SimpleGraph ({w : V | w ≠ v} : Set V) :=
  G.induce {w | w ≠ v}

/-- `G` and `G'` have the same deck: a bijection `σ` between the vertex sets such that the
card of `G` at `v` is isomorphic to the card of `G'` at `σ v`, for every `v`. The isomorphisms
of the individual cards need not agree with each other or with `σ`. -/
def SameDeck (G : SimpleGraph V) (G' : SimpleGraph V') : Prop :=
  ∃ σ : V ≃ V', ∀ v, Nonempty (G.cardAt v ≃g G'.cardAt (σ v))

end SimpleGraph
