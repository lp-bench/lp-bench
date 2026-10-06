import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.Field.Rat

namespace SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The average vertex degree of a finite simple graph, as a rational number;
by the division-by-zero convention it is `0` for the graph on no vertices. -/
def averageDegree : ℚ :=
  ((∑ v, G.degree v : ℕ) : ℚ) / Fintype.card V

end SimpleGraph
