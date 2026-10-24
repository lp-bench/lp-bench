import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

open Sym2

universe u

namespace SimpleGraph

variable {V : Type u}

/-- The vertex `v` lies in the ball `B_r(center, G)`: it lies on a closed walk of length at most
`r` through `center`. -/
def IsInLocalBall (G : SimpleGraph V) (r : ℕ) (center v : V) : Prop :=
  ∃ w : G.Walk center center, w.length ≤ r ∧ v ∈ w.support

/-- The edge `e` lies in the ball `B_r(center, G)`: it lies on a closed walk of length at most `r`
through `center`. -/
def IsEdgeInLocalBall (G : SimpleGraph V) (r : ℕ) (center : V)
    (e : Sym2 V) : Prop :=
  ∃ w : G.Walk center center, w.length ≤ r ∧ e ∈ w.edges

end SimpleGraph
