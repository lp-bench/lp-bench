import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

open SimpleGraph Finset

variable {V V' : Type} (G : SimpleGraph V) (G' : SimpleGraph V')
variable [Fintype V] [DecidableRel G.Adj]

def contains : Prop := Nonempty ( G' ↪g G )

def free : Prop := ¬ contains G G'

def triangle_free := free G (completeGraph (Fin 3))

theorem P098 {htf : triangle_free G} :
    Finset.card (G.edgeSet.toFinset) ≤  (Fintype.card V)^2 / 4 := by sorry
