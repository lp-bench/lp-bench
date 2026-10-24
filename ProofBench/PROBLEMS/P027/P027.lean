import Mathlib.Data.Set.Card

/-- An *oriented graph* on a vertex type `V`: an adjacency relation that is
loopless and has no 2-cycles (so it is an orientation of a simple graph). -/
structure OrientedGraph (V : Type*) where
  /-- The directed adjacency relation: `Adj u v` means there is an arc `u → v`. -/
  Adj : V → V → Prop
  /-- No loops. -/
  loopless : ∀ v, ¬ Adj v v
  /-- No 2-cycles: an arc `u → v` forbids the reverse arc `v → u`. -/
  oriented : ∀ u v, Adj u v → ¬ Adj v u

namespace OrientedGraph

variable {V : Type*}

/-- First out-neighbourhood `N⁺(v) = { w | v → w }`. -/
def outNeighborhood (G : OrientedGraph V) (v : V) : Set V :=
  {w | G.Adj v w}

/-- Second out-neighbourhood `N⁺⁺(v)`: vertices at directed distance exactly two
from `v` — reachable by a 2-step directed path, but not out-neighbours of `v`. -/
def secondOutNeighborhood (G : OrientedGraph V) (v : V) : Set V :=
  {w | w ≠ v ∧ ¬ G.Adj v w ∧ ∃ u, G.Adj v u ∧ G.Adj u w}

end OrientedGraph

open OrientedGraph

/- Do not modify above this line. -/

/-- Seymour's Second Neighbourhood Conjecture (c. 1990; see Dean–Latka 1995): every nonempty
finite oriented graph has a vertex `v` with `|N⁺(v)| ≤ |N⁺⁺(v)|`. -/
theorem P027 {V : Type*} [Finite V] [Nonempty V] (G : OrientedGraph V) :
    ∃ v, (G.outNeighborhood v).ncard ≤ (G.secondOutNeighborhood v).ncard := by
  sorry
