import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Countable.Defs
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.UnfriendlyPartition

/-!
# The Unfriendly Partition Conjecture — Universal Statement

Does every **countable** graph admit a partition of its vertex set into two
parts such that every vertex has at least as many neighbours in the other
part as in its own?

-/

universe u

variable {V : Type u} [Countable V] (G : SimpleGraph V)

/- The Unfriendly Partition Conjecture: Every countable graph has an unfriendly partition. -/
def UPConj : Prop :=
    ∃ f : V → Option Bool, IsUnfriendlyPartition G f

/- **The Unfriendly Partition Conjecture**: every
countable graph has a partition that is unfriendly at every vertex. -/
theorem P010 : UPConj G := sorry
