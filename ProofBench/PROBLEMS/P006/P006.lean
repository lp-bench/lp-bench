import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.AlphaWQO

/-!
# Better-Quasi-Ordering of Finite Graphs under Minor Relation
-/

/- The graph minor `α`-WQO ladder at rung `r`: finite *planar* graphs are
`(r / 2)`-well-quasi-ordered under minors when `r` is even, and *all* finite
graphs are when `r` is odd. -/
def GraphMinorWQOConj : Prop :=
  ∀ r : Ordinal.{1}, if r % 2 = 0
  then IsAlphaWQO PlanarGraph.MinorLE (r / 2)
  else IsAlphaWQO FiniteGraph.MinorLE (r / 2)

/- `α`-well-quasi-ordering of finite (planar) graphs under minors, for the
chosen `r`: planar graphs at level `r / 2` when `r` is even, all finite
graphs at level `r / 2` when `r` is odd. -/
theorem P006 : GraphMinorWQOConj := sorry
