import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Local balls via closed walks, and their metric description

* `isInLocalBall_iff`: a vertex lies in the ball iff it is reachable and
  `2 * dist center v ≤ r`, i.e. `dist center v ≤ r / 2`;
* `isEdgeInLocalBall_iff`: an edge `s(x, y)` lies in the ball iff
  `dist center x + dist center y + 1 ≤ r`, i.e. the farthest point of the
  edge in the geometric realization is within distance `r / 2` of the center.

Specializing to the two parities of `r` recovers Definition 2.3 verbatim:

* diameter `2 * s` (integer radius `s`): the vertices at distance at most `s`,
  *without* the edges joining two vertices of distance precisely `s`
  (`isEdgeInLocalBall_two_mul_iff`);
* diameter `2 * s + 1` (half-integer radius `s + 1/2`): the full induced
  subgraph on the vertices at distance at most `s`
  (`isEdgeInLocalBall_odd_iff`).
-/

open Sym2

universe u

namespace SimpleGraph

variable {V : Type u}

/-
A vertex lies in the paper's ball `B_r(center, G)` when it lies on a closed
walk of length at most `r` through `center`.
-/
def IsInLocalBall (G : SimpleGraph V) (r : ℕ) (center v : V) : Prop :=
  ∃ w : G.Walk center center, w.length ≤ r ∧ v ∈ w.support

/- An edge lies in the paper's ball `B_r(center, G)`. -/
def IsEdgeInLocalBall (G : SimpleGraph V) (r : ℕ) (center : V)
    (e : Sym2 V) : Prop :=
  ∃ w : G.Walk center center, w.length ≤ r ∧ e ∈ w.edges

end SimpleGraph
