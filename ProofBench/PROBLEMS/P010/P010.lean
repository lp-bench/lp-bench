import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Countable.Defs
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.UnfriendlyPartition

universe u

variable {V : Type u} [Countable V] (G : SimpleGraph V)

/-- `G` has an unfriendly partition: an assignment `f : V → Option Bool` of every vertex
to one of two sides that is unfriendly at every vertex. -/
def UPConj : Prop :=
    ∃ f : V → Option Bool, IsUnfriendlyPartition G f

/-- **The unfriendly partition conjecture** (Cowan–Emerson): every countable graph has a
partition of its vertices into two sides in which every vertex has at least as many
neighbours on the other side as on its own. -/
theorem P010 : UPConj G := sorry
