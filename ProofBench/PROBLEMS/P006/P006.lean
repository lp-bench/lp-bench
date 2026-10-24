import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.AlphaWQO

/-- The graph-minor `α`-WQO ladder: for every ordinal `r`, finite *planar* graphs are
`(r / 2)`-well-quasi-ordered under minors when `r` is even, and *all* finite graphs
are when `r` is odd (ordinal quotient and remainder by `2`). -/
def GraphMinorWQOConj : Prop :=
  ∀ r : Ordinal.{1}, if r % 2 = 0
  then IsAlphaWQO PlanarGraph.MinorLE (r / 2)
  else IsAlphaWQO FiniteGraph.MinorLE (r / 2)

/-- **Better-quasi-ordering of graph minors** (an open strengthening of the
Robertson–Seymour graph minor theorem): for every ordinal `r`, finite planar graphs
(`r` even) or all finite graphs (`r` odd) are `(r / 2)`-well-quasi-ordered under minors. -/
theorem P006 : GraphMinorWQOConj := sorry
