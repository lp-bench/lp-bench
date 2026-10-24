import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

open SimpleGraph Finset

variable {V V' : Type} (G : SimpleGraph V) (G' : SimpleGraph V')
variable [Fintype V] [DecidableRel G.Adj]

/-- `G` contains a copy of `G'`: there is a graph embedding `G' ↪g G`, an injective
map preserving adjacency and non-adjacency. -/
def contains : Prop := Nonempty ( G' ↪g G )

/-- `G` is `G'`-free: it contains no copy of `G'`. -/
def free : Prop := ¬ contains G G'

/-- `G` is triangle-free: it contains no copy of `K_3`. -/
def triangle_free := free G (completeGraph (Fin 3))

/-- Mantel's theorem (1907): a triangle-free graph on `n` vertices has at most
`⌊n^2/4⌋` edges. -/
theorem P098 {htf : triangle_free G} :
    Finset.card (G.edgeSet.toFinset) ≤  (Fintype.card V)^2 / 4 := by sorry
